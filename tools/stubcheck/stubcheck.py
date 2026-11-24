#!/usr/bin/env python3
"""Stub check for the Lean FLT proof (anthropics/fermats-last-theorem).

Checks the proof of one or more theorems against the *statements* they cite, without
building the cones behind those statements.

For each target theorem X (a stem such as `FreyPackage_Mazur_Frey`, or a full name such as
`FreyPackage.Mazur_Frey`):
  * `P2M/Sol/S_X.lean` (the proof, optionally patched) and `Theorems/Thm_X.lean` (the
    statement, which closes the proof with `p2m_exact_reverting`) are compiled as they are;
  * every other statement module reachable from them is replaced by a stub: the same text,
    with `theorem` turned into `axiom`, the proof call removed, and the import of its own
    proof module and any `#p2m_type_eq` checks of it dropped;
  * definition modules and `P2M/Util.lean` are used as they are;
  * in every copied module the generated `attribute [-instance|-simp|-ext] …` preamble becomes
    `p2m_stub_erase_* …`, which skips names that do not exist without their proof cones.

The result is a small Lake project. Building it and running `#print axioms` on each target
gives PASS when the proof compiles and uses nothing beyond Lean's three standard axioms and
the stubs (the cited statements), and FAIL otherwise. A stub check can fail where the full
build would pass (a proof that silently relies on something from a cited theorem's proof
cone), never the other way round, provided the stubs match the real statements; they are
generated from the same text, and the full build settles it.

Usage:
  stubcheck.py --repo FLT --out DIR --target X [--target Y …] [--patch FILE.patch]
               (--mathlib-path PATH | --mathlib-rev REV) [--toolchain leanprover/lean4:v4.33.1]
               [--build] [--lake lake]
"""
import argparse
import os
import re
import shutil
import subprocess
import sys

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*$")
PROOF_CALL_RE = re.compile(r"\s*:=\s*by\s+p2m_exact_reverting\s+@_root_\.P2MW\.S_\S+\.solution")
PREAMBLE_RE = re.compile(r"^attribute \[-(instance|simp|ext)\]\s+(.*)$")
FLT_TOPS = ("Theorems", "Definitions", "P2M")


def stem_of(target, repo):
    """Accept a module stem or a theorem name; return the stem of Thm_<stem>.lean."""
    for cand in (target, target.replace(".", "_")):
        if os.path.exists(os.path.join(repo, "Theorems", f"Thm_{cand}.lean")):
            return cand
    sys.exit(f"stubcheck: no statement module for target {target!r}")


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def split_imports(text):
    """Return (imports, rest_lines) for a Lean file whose header is a run of import lines,
    possibly interleaved with blank lines and comments."""
    lines = text.split("\n")
    imports, i = [], 0
    while i < len(lines):
        line = lines[i]
        m = IMPORT_RE.match(line)
        if m:
            imports.append(m.group(1))
        elif line.strip() and not line.strip().startswith("--"):
            break
        i += 1
    return imports, lines[i:]


def transform_preamble(lines):
    out, changed = [], False
    for line in lines:
        m = PREAMBLE_RE.match(line)
        if m:
            out.append(f"p2m_stub_erase_{m.group(1)} {m.group(2)}")
            changed = True
        else:
            out.append(line)
    return out, changed


def render(imports, body_lines, add_stubutil):
    imps = list(imports)
    if add_stubutil and "P2M.StubUtil" not in imps:
        imps.append("P2M.StubUtil")
    return "\n".join(f"import {m}" for m in imps) + "\n" + "\n".join(body_lines)


def make_stub(text, stem):
    """Statement module -> axiom stub."""
    imports, body = split_imports(text)
    imports = [m for m in imports if m != f"P2M.Sol.S_{stem}"]
    src = "\n".join(body)
    src, n = PROOF_CALL_RE.subn("", src)
    if n != 1:
        raise ValueError(f"Thm_{stem}: expected one p2m_exact_reverting call, found {n}")
    # the theorem whose proof call was removed becomes an axiom: it is the last `theorem`
    # declaration before the removed call (statement files hold exactly one)
    decls = list(re.finditer(r"^theorem\s", src, re.M))
    if not decls:
        raise ValueError(f"Thm_{stem}: no theorem declaration")
    d = decls[-1]
    src = src[:d.start()] + "axiom " + src[d.end():]
    body = [l for l in src.split("\n") if not l.lstrip().startswith("#p2m_type_eq")]
    return imports, body


def module_path(root, mod):
    return os.path.join(root, *mod.split(".")) + ".lean"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--target", action="append", required=True)
    ap.add_argument("--patch")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--mathlib-path")
    g.add_argument("--mathlib-rev")
    ap.add_argument("--toolchain", default=None, help="default: the repository's lean-toolchain")
    ap.add_argument("--build", action="store_true", help="build and report (needs lake on PATH)")
    ap.add_argument("--lake", default="lake")
    ap.add_argument("--no-cache", action="store_true",
                    help="pass --no-cache to lake (no download of build caches; build locally)")
    a = ap.parse_args()

    repo = os.path.abspath(a.repo)
    out = os.path.abspath(a.out)
    here = os.path.dirname(os.path.abspath(__file__))

    # overlay: patched copies of the files a patch touches
    overlay = None
    if a.patch:
        overlay = os.path.join(out, ".overlay")
        shutil.rmtree(overlay, ignore_errors=True)
        touched = re.findall(r"^\+\+\+ b/(\S+)", read(a.patch), re.M)
        for rel in touched:
            src = os.path.join(repo, rel)
            dst = os.path.join(overlay, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            if os.path.exists(src):
                shutil.copy(src, dst)
        r = subprocess.run(["patch", "-p1", "-s", "-d", overlay, "-i", os.path.abspath(a.patch)],
                           capture_output=True, text=True)
        if r.returncode:
            sys.exit(f"stubcheck: patch does not apply:\n{r.stdout}{r.stderr}")

    def source(mod):
        rel = os.path.join(*mod.split(".")) + ".lean"
        if overlay and os.path.exists(os.path.join(overlay, rel)):
            return read(os.path.join(overlay, rel))
        return read(os.path.join(repo, rel))

    stems = [stem_of(t, repo) for t in a.target]
    real = {f"P2M.Sol.S_{s}" for s in stems} | {f"Theorems.Thm_{s}" for s in stems}

    # closure: real targets, stubs for other statements, definitions and P2M.Util as they are
    files, stack, seen = {}, sorted(real), set()
    mathlib_imports = set()
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        text = source(mod)
        if mod.startswith("Theorems.") and mod not in real:
            stem = mod.split("Thm_", 1)[1]
            imports, body = make_stub(text, stem)
            kind = "stub"
        else:
            imports, body = split_imports(text)
            kind = "real"
        body, changed = transform_preamble(body)
        files[mod] = (imports, body, changed, kind)
        for m in imports:
            top = m.split(".")[0]
            if top in FLT_TOPS:
                if m.startswith("P2M.Sol.") and m not in real:
                    raise SystemExit(f"stubcheck: {mod} imports proof module {m}, which is not a target")
                stack.append(m)
            else:
                mathlib_imports.add(m)

    # write the project
    for sub in ("Theorems", "Definitions", "P2M"):
        shutil.rmtree(os.path.join(out, sub), ignore_errors=True)
    for mod, (imports, body, changed, kind) in files.items():
        path = module_path(out, mod)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write(render(imports, body, changed))
    shutil.copy(os.path.join(here, "StubUtil.lean"), module_path(out, "P2M.StubUtil"))

    names = []
    for s in stems:
        m = re.search(r"^theorem\s+(\S+)", "\n".join(files[f"Theorems.Thm_{s}"][1]), re.M)
        decl = m.group(1)
        ns = re.findall(r"^namespace\s+(\S+)", "\n".join(files[f"Theorems.Thm_{s}"][1]), re.M)
        names.append(".".join(ns + [decl]) if ns and not decl.startswith("_root_.") else decl.removeprefix("_root_."))
    with open(os.path.join(out, "Check.lean"), "w", encoding="utf-8") as f:
        f.write("".join(f"import Theorems.Thm_{s}\n" for s in stems) + "\n")
        f.write("".join(f"#print axioms {n}\n" for n in names))

    # lakefile: the repository's leanOptions, its Mathlib pin, one library per top folder
    lakefile = read(os.path.join(repo, "lakefile.lean"))
    opts = re.search(r"leanOptions := #\[(.*?)\n  \]", lakefile, re.S).group(1)
    rev = a.mathlib_rev or re.search(r'require mathlib from git "[^"]+" @ "([0-9a-f]+)"', lakefile).group(1)
    req = (f'require mathlib from "{os.path.abspath(a.mathlib_path)}"' if a.mathlib_path
           else f'require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{rev}"')
    # a local Mathlib checkout shares its dependency packages (and their builds) with the check
    pkgdir = (f'\n  packagesDir := "{os.path.join(os.path.abspath(a.mathlib_path), ".lake", "packages")}"'
              if a.mathlib_path else "")
    with open(os.path.join(out, "lakefile.lean"), "w", encoding="utf-8") as f:
        f.write(f"""import Lake
open Lake DSL

package stubcheck where{pkgdir}
  leanOptions := #[{opts}
  ]

{req}

lean_lib Theorems where
  globs := #[.submodules `Theorems]

lean_lib Definitions where
  globs := #[.submodules `Definitions]

lean_lib P2M where
  globs := #[.submodules `P2M]
""")
    toolchain = a.toolchain or read(os.path.join(repo, "lean-toolchain")).strip()
    with open(os.path.join(out, "lean-toolchain"), "w") as f:
        f.write(toolchain + "\n")

    kinds = {k: sum(1 for v in files.values() if v[3] == k) for k in ("real", "stub")}
    wholesale = "Mathlib" in mathlib_imports
    print(f"stubcheck: {len(stems)} target(s); {kinds['real']} modules as they are, {kinds['stub']} stubs; "
          f"Mathlib needed: {'all of it' if wholesale else str(len(mathlib_imports)) + ' imported modules'}")
    with open(os.path.join(out, "targets.txt"), "w") as f:
        f.write("\n".join(names) + "\n")

    if not a.build:
        return 0

    stub_axioms = set()
    for mod, (_, body, _, kind) in files.items():
        if kind == "stub":
            text = "\n".join(body)
            ns = re.findall(r"^namespace\s+(\S+)", text, re.M)
            d = re.search(r"^axiom\s+(\S+)", text, re.M).group(1)
            stub_axioms.add(".".join(ns + [d]) if ns and not d.startswith("_root_.") else d.removeprefix("_root_."))
    lake_flags = ["--no-cache"] if a.no_cache else []
    env = dict(os.environ)
    if a.no_cache:
        # Mathlib's post-update hook would otherwise try to download its cache when Lake first
        # resolves the dependencies of a fresh check project
        env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    r = subprocess.run([a.lake, "build", *lake_flags] + [f"Theorems.Thm_{s}" for s in stems], cwd=out,
                       capture_output=True, text=True, env=env)
    log = r.stdout + r.stderr
    with open(os.path.join(out, "build.log"), "w", encoding="utf-8") as f:
        f.write(log)
    if r.returncode:
        errors = [l for l in log.split("\n") if "error" in l.lower()][:40]
        print("FAIL: the check does not compile\n" + "\n".join(errors))
        return 1
    r = subprocess.run([a.lake, "env", "lean", "Check.lean"], cwd=out, capture_output=True, text=True, env=env)
    text = r.stdout + r.stderr
    ok = r.returncode == 0
    standard = {"propext", "Classical.choice", "Quot.sound"}
    for n in names:
        m = re.search(rf"'{re.escape(n)}' depends on axioms: \[(.*?)\]", text, re.S)
        if not m:
            m2 = re.search(rf"'{re.escape(n)}' does not depend on any axioms", text)
            used = set() if m2 else None
        else:
            used = {x.strip() for x in m.group(1).replace("\n", " ").split(",") if x.strip()}
        if used is None:
            print(f"FAIL {n}: no axiom report\n{text[-2000:]}")
            ok = False
            continue
        stubs = sorted(used & stub_axioms)
        other = sorted(used - standard - stub_axioms)
        verdict = "PASS" if not other else "FAIL"
        ok &= verdict == "PASS"
        print(f"{verdict} {n}\n  cited statements used ({len(stubs)}): {', '.join(stubs) or 'none'}"
              + (f"\n  unexpected axioms: {', '.join(other)}" if other else ""))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
