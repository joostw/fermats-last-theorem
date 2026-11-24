# Stub checks for the Lean FLT proof

Check one proof at a time against the statements it cites, without building the millions of
lines behind those statements.

## Why this works

Every theorem `X` of the repository is split in two: `Theorems/Thm_X.lean` states it and
`P2M/Sol/S_X.lean` proves it, importing exactly the statements it cites. A proof therefore only
needs its cited *statements*. A stub check compiles `S_X` against stubs: copies of the cited
statement modules in which `theorem` becomes `axiom` and the proof call is removed.

What is compiled as it is: the proof `S_X` (and `Thm_X`, which closes it with
`p2m_exact_reverting`), the definition modules it reaches, `P2M/Util.lean`, and Mathlib.
What is stubbed: every other statement module.

The result for each target:

- **PASS** — the proof compiles and `#print axioms` shows only Lean's three standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) and stubs. The stubs listed are the cited
  statements the proof actually uses.
- **FAIL** — it does not compile, or it uses another axiom (`sorryAx`, a new `axiom`).

A stub check is conservative. It can fail where the full build would pass, for example when a
proof relies on an instance or lemma that only a cited theorem's proof cone provides; it should
not pass where the full build fails, because each stub is generated from the real statement's
text. The full build (`lake build` in the repository root, see the main README) remains the
final word.

The generated `attribute [-instance|-simp|-ext] …` preambles become `p2m_stub_erase_* …`
commands (`StubUtil.lean`), which skip names that do not exist without the proof cones and
otherwise do exactly the same.

## Running it on GitHub

`.github/workflows/stub-check.yml` runs on every push or pull request that changes
`P2M/Sol/`, `Theorems/` or `Definitions/`, and checks the proof modules that changed. It can
also be started by hand (Actions → stub-check → Run workflow) with a list of targets.

Two modes:

- **fast** (default): Lean 4.33.0 with Mathlib's published build cache for the pinned Mathlib
  commit (v4.33.0). A run takes minutes. The repository itself pins Lean 4.33.1, a patch
  release with kernel fixes; for checking that a proof elaborates the difference should not
  matter, and the exact mode removes it.
- **exact**: Lean 4.33.1 with Mathlib built from source. Run the `mathlib-exact` workflow once
  first; it builds Mathlib in up to three sequential stages of at most five hours each and
  caches the result. If its last stage ends partial, run it again.

Standard GitHub-hosted runners are free for public repositories (4 cores, 16 GB, 14 GB disk,
6 hours per job), so the fork must be public.

## Running it locally

Needs Lean (elan) and a Mathlib checkout at the pinned commit with its build:

```sh
python3 tools/stubcheck/stubcheck.py --repo . --out /tmp/check \
    --target FreyPackage.Mazur_Frey --mathlib-path ~/mathlib --build --no-cache
```

`--target` takes a theorem name or a module stem and may be repeated; a target that cites another target sees the real theorem, not a stub. `--patch file.patch`
checks a patched version without changing the repository. Without `--build` the tool only
writes the check project to `--out` (a Lake project: `lakefile.lean`, the copied and stubbed
modules, `Check.lean`).

## Files

- `stubcheck.py` — builds the check project and, with `--build`, runs and judges it.
- `StubUtil.lean` — the `p2m_stub_erase_*` commands.
- `changed_targets.py` — the targets touched between two commits (used by the workflow).
