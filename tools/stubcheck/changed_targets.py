#!/usr/bin/env python3
"""Print the stub-check targets touched between two commits.

  P2M/Sol/S_<X>.lean changed    -> target <X>
  Theorems/Thm_<X>.lean changed -> target <X>, plus every proof that cites it (imports Theorems.Thm_<X>):
                                   a changed statement changes the contract those proofs rely on
  Definitions/<D>.lean changed  -> every theorem whose statement or proof names a declaration of <D>
                                   (old or new version), and, transitively, of the definition modules
                                   that name those declarations

Names are matched as whole identifier pieces in the source text, by their last component when it is
distinctive and by their last two components otherwise, so the set errs on the side of checking too
much. Structure fields are covered through their structure's name; instances are not followed.

At most --max-targets targets are printed (direct changes first, then citing proofs, then users of
changed definitions); the rest are reported in a warning and written, with the full list, to
--list-file if given.

Usage: changed_targets.py --repo . --base <sha> --head <sha> [--max-targets 200] [--list-file f]
Targets go to stdout (space-separated); warnings go to stderr as GitHub annotations.
"""
import argparse
import os
import re
import subprocess
import sys

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|irreducible_def|opaque)\s+([^\s:({\[]+)",
    re.M)
NS_RE = re.compile(r"^\s*namespace\s+(\S+)", re.M)
IDCHARS = r"[\w'!?ₐ-ₜᵢ-ᵪⱼ₀-₉ʰ-ʸͰ-Ͽᴀ-ᶿ℀-⅏\U0001d400-\U0001d7ff]"


def git(repo, *args, check=False):
    r = subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True)
    if check and r.returncode:
        raise RuntimeError(r.stderr.strip())
    return r


def warn(msg, path=None):
    loc = f" file={path}" if path else ""
    print(f"::warning{loc}::{msg}", file=sys.stderr)


def declared_names(text):
    """Declarations of a Lean file, qualified by the enclosing namespaces (good enough here)."""
    names, ns_stack = set(), []
    for line in text.split("\n"):
        m = re.match(r"\s*namespace\s+(\S+)", line)
        if m:
            ns_stack.append(m.group(1))
            continue
        m = re.match(r"\s*end\s+(\S+)\s*$", line)
        if m and ns_stack and ns_stack[-1] == m.group(1):
            ns_stack.pop()
            continue
        m = DECL_RE.match(line)
        if m:
            n = m.group(1)
            if n.startswith("_root_."):
                n = n[len("_root_."):]
            elif ns_stack:
                n = ".".join(ns_stack) + "." + n
            names.add(n)
    return names


def search_keys(names):
    """How to look for each name: its last component when that is distinctive (a type-like name starting
    with a capital, a name with an underscore, or one of 10+ characters), else its last two components."""
    keys = set()
    for n in names:
        parts = n.split(".")
        last = parts[-1]
        if len(parts) == 1 or last[:1].isupper() or "_" in last or len(last) >= 10:
            keys.add(last)
        else:
            keys.add(".".join(parts[-2:]))
    return keys


TOKEN_RE = re.compile(IDCHARS.replace("]", ".]") + "+")


def tokens(text):
    """Identifier pieces of a file: every component of a dotted name, and every pair of adjacent components."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    text = "\n".join(l for l in text.split("\n") if not l.startswith(("attribute [-", "import ")))
    out = set()
    for tok in TOKEN_RE.findall(text):
        parts = [p for p in tok.split(".") if p]
        out.update(parts)
        out.update(f"{x}.{y}" for x, y in zip(parts, parts[1:]))
    return out


_TOKENS = {}


def files_naming(repo, keys, dirs):
    """Files under dirs whose code names one of keys as a whole identifier piece."""
    if not keys:
        return set()
    args = ["grep", "-l", "-F"]
    for k in sorted(keys):
        args += ["-e", k]
    cands = git(repo, *args, "--", *dirs).stdout.split()
    hits = set()
    for f in cands:
        if f not in _TOKENS:
            try:
                _TOKENS[f] = tokens(open(os.path.join(repo, f), encoding="utf-8").read())
            except OSError:
                _TOKENS[f] = set()
        if _TOKENS[f] & keys:
            hits.add(f)
    return hits


def target_of(path):
    m = re.fullmatch(r"P2M/Sol/S_(.+)\.lean", path) or re.fullmatch(r"Theorems/Thm_(.+)\.lean", path)
    return m.group(1) if m else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--base", default="")
    ap.add_argument("--head", default="HEAD")
    ap.add_argument("--max-targets", type=int, default=200)
    ap.add_argument("--list-file", default="")
    ap.add_argument("--def-depth", type=int, default=3,
                    help="how many rounds of definition files naming changed declarations to follow")
    a = ap.parse_args()
    base = a.base
    if not base or set(base) == {"0"}:
        base = f"{a.head}~1"
    r = git(a.repo, "diff", "--name-status", "--find-renames", base, a.head)
    if r.returncode:
        warn(f"could not diff {base}..{a.head}: {r.stderr.strip()}")
        return 0
    direct, cited, def_users = [], set(), set()
    changed_defs = []
    for line in r.stdout.splitlines():
        parts = line.split("\t")
        status, paths = parts[0], parts[1:]
        path = paths[-1]
        old_path = paths[0]
        t = target_of(path)
        if t and not status.startswith("D"):
            direct.append(t)
            if path.startswith("Theorems/"):
                mod = "Theorems.Thm_" + t
                g = git(a.repo, "grep", "-l", "-E", rf"^import {re.escape(mod)}\s*$", "--", "P2M/Sol")
                users = {target_of(f) for f in g.stdout.split()} - {None, t}
                cited |= users
                warn(f"statement changed: re-checking the {len(users)} proofs that cite it", path)
            continue
        if path.startswith("Definitions/") and path.endswith(".lean"):
            changed_defs.append((status, old_path, path))

    if changed_defs:
        names = set()
        for status, old_path, path in changed_defs:
            if not status.startswith("A"):
                old = git(a.repo, "show", f"{base}:{old_path}")
                if old.returncode == 0:
                    names |= declared_names(old.stdout)
            if not status.startswith("D"):
                new = git(a.repo, "show", f"{a.head}:{path}")
                if new.returncode == 0:
                    names |= declared_names(new.stdout)
        # definition modules that name those declarations change meaning too: follow them to a fixpoint
        seen_defs = {p for _, _, p in changed_defs}
        frontier = set(names)
        rounds = 0
        while frontier and rounds < a.def_depth:
            rounds += 1
            keys = search_keys(frontier)
            users = files_naming(a.repo, keys, ["Definitions"]) - seen_defs
            frontier = set()
            for f in users:
                seen_defs.add(f)
                text = git(a.repo, "show", f"{a.head}:{f}").stdout
                new = declared_names(text) - names
                names |= new
                frontier |= new
            print(f"  round {rounds}: {len(users)} more definition files, {len(names)} names", file=sys.stderr)
        if frontier:
            warn(f"stopped following definitions after {a.def_depth} rounds; raise --def-depth to go further")
        keys = search_keys(names)
        for f in files_naming(a.repo, keys, ["Theorems", "P2M/Sol"]):
            t = target_of(f)
            if t:
                def_users.add(t)
        warn(f"{len(changed_defs)} definition file(s) changed: {len(seen_defs) - len(changed_defs)} more definition "
             f"files name their declarations; {len(def_users)} theorems name one of them and are re-checked")

    ordered = []
    for group in (sorted(set(direct)), sorted(cited - set(direct)), sorted(def_users - set(direct) - cited)):
        ordered += [t for t in group if t not in ordered]
    if a.list_file:
        with open(a.list_file, "w", encoding="utf-8") as f:
            f.write("\n".join(ordered) + ("\n" if ordered else ""))
    if len(ordered) > a.max_targets:
        warn(f"{len(ordered)} targets; checking the first {a.max_targets} (direct changes first). "
             f"Dispatch the rest by hand from the target list.")
        ordered = ordered[:a.max_targets]
    print(" ".join(ordered))
    return 0


if __name__ == "__main__":
    sys.exit(main())
