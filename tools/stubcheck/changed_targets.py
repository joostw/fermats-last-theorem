#!/usr/bin/env python3
"""Print the stub-check targets touched between two commits.

  P2M/Sol/S_<X>.lean changed   -> target <X>
  Theorems/Thm_<X>.lean changed -> target <X>, plus a warning: a changed statement changes the
                                   contract every theorem citing it relies on
  Definitions/… changed         -> a warning only: dependents are not found automatically

Usage: changed_targets.py --repo . --base <sha> --head <sha>
Targets go to stdout (space-separated); warnings go to stderr as GitHub annotations.
"""
import argparse
import re
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--base", default="")
    ap.add_argument("--head", default="HEAD")
    a = ap.parse_args()
    base = a.base
    if not base or set(base) == {"0"}:
        base = f"{a.head}~1"
    r = subprocess.run(["git", "-C", a.repo, "diff", "--name-only", "--diff-filter=AMR", base, a.head],
                       capture_output=True, text=True)
    if r.returncode:
        print(f"::warning::could not diff {base}..{a.head}: {r.stderr.strip()}", file=sys.stderr)
        return 0
    targets = []
    for path in r.stdout.split():
        m = re.fullmatch(r"P2M/Sol/S_(.+)\.lean", path)
        if m:
            targets.append(m.group(1))
            continue
        m = re.fullmatch(r"Theorems/Thm_(.+)\.lean", path)
        if m:
            targets.append(m.group(1))
            print(f"::warning file={path}::statement changed: every theorem citing it relies on the old text",
                  file=sys.stderr)
            continue
        if path.startswith("Definitions/"):
            print(f"::warning file={path}::definition changed: theorems using it are not checked automatically",
                  file=sys.stderr)
    print(" ".join(sorted(set(targets))))
    return 0


if __name__ == "__main__":
    sys.exit(main())
