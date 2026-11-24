import Lean

/-!
Commands used by stub checks of the Lean FLT proof.

Every module of the repository starts with a generated preamble such as
`attribute [-instance] A.instFoo B.instBar` that removes instances (and `simp`/`ext` lemmas)
brought in by the proof cones it imports. In a stub check those cones are absent, so some
of the names do not exist and the plain `attribute` command would fail. These commands do the
same erasures, skipping names that are not in the environment. For a name that does exist,
the effect is exactly the original `attribute [-…]` command.
-/

open Lean Elab Command

/-- `attribute [-instance] n₁ … nₖ`, skipping names absent from the environment. -/
elab "p2m_stub_erase_instance " ns:ident* : command => do
  for n in ns do
    if (← getEnv).contains n.getId then
      elabCommand (← `(attribute [-instance] $n:ident))

/-- `attribute [-simp] n₁ … nₖ`, skipping names absent from the environment. -/
elab "p2m_stub_erase_simp " ns:ident* : command => do
  for n in ns do
    if (← getEnv).contains n.getId then
      elabCommand (← `(attribute [-simp] $n:ident))

/-- `attribute [-ext] n₁ … nₖ`, skipping names absent from the environment. -/
elab "p2m_stub_erase_ext " ns:ident* : command => do
  for n in ns do
    if (← getEnv).contains n.getId then
      elabCommand (← `(attribute [-ext] $n:ident))
