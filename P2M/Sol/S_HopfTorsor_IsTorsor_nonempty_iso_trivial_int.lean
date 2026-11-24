import Definitions.Def_HopfTorsor_Descent
import Theorems.Thm_Algebra_FormallyUnramified_nonempty_ringHom_int
import P2M.Util
namespace P2MW.S_HopfTorsor_IsTorsor_nonempty_iso_trivial_int

set_option autoImplicit false
-- The `convert` fallbacks below are needed only when the instance paths differ, which depends on
-- the imports in scope; where they coincide the linters would flag the fallback as dead code.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem solution
    {H : Type} [CommRing H] [HopfAlgebra ℤ H] [Module.Finite ℤ H]
    [Algebra.FormallyUnramified ℤ H]
    {A : Type} [CommRing A] {c : HopfTorsor.Coaction ℤ H A} (hc : HopfTorsor.IsTorsor c) :
    Nonempty (HopfTorsor.CoactionIso c HopfTorsor.Coaction.trivial) := by
  -- The `ℤ`-module and `ℤ`-algebra structures below can be reached by different instance paths
  -- (from `HopfAlgebra ℤ H`, from `Ring.toIntAlgebra`, from `AddCommGroup.toIntModule`). They are
  -- equal, since `Module ℤ M` and `Algebra ℤ A` are subsingletons; `convert` bridges them.
  have : @Module.Finite ℤ H _ _ Algebra.toModule := by
    convert ‹Module.Finite ℤ H› <;> first | rfl | exact Subsingleton.elim _ _
  have : Nontrivial A := hc.torsor_nontrivial
  have : Module.Finite ℤ A := by
    convert hc.torsor_finite <;> first | rfl | exact Subsingleton.elim _ _
  have : Module.Flat ℤ A := by
    convert hc.torsor_flat <;> first | rfl | exact Subsingleton.elim _ _
  have : Algebra.FormallyUnramified ℤ A := by
    convert hc.torsor_formallyUnramified <;> first | rfl | exact Subsingleton.elim _ _
  -- Minkowski: a nonzero finite flat unramified `ℤ`-algebra has a `ℤ`-point.
  obtain ⟨f⟩ := Algebra.FormallyUnramified.nonempty_ringHom_int A
  -- A torsor with a point is trivial.
  exact hc.nonempty_iso_trivial_of_point f.toIntAlgHom

end P2MW.S_HopfTorsor_IsTorsor_nonempty_iso_trivial_int
