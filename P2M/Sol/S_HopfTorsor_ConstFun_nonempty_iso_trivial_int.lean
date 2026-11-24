import Definitions.Def_HopfTorsor_ConstFun
import Theorems.Thm_HopfTorsor_IsTorsor_nonempty_iso_trivial_int
import P2M.Util
namespace P2MW.S_HopfTorsor_ConstFun_nonempty_iso_trivial_int

set_option autoImplicit false
-- The `convert` fallbacks below are needed only when the instance paths differ, which depends on
-- the imports in scope; where they coincide the linters would flag the fallback as dead code.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem solution (G : Type) [Group G] [Fintype G]
    [DecidableEq G] {A : Type} [CommRing A]
    {c : HopfTorsor.Coaction ℤ (HopfTorsor.ConstFun ℤ G) A} (hc : HopfTorsor.IsTorsor c) :
    Nonempty (HopfTorsor.CoactionIso c HopfTorsor.Coaction.trivial) := by
  -- Functions on a finite group are a finite, formally unramified `ℤ`-algebra. As in the general
  -- theorem, the instances are bridged with `convert` in case their paths differ.
  refine @HopfTorsor.IsTorsor.nonempty_iso_trivial_int _ _ _ ?_ ?_ _ _ _ hc
  · convert HopfTorsor.ConstFun.instFiniteInt G <;> first | rfl | exact Subsingleton.elim _ _
  · convert (inferInstance : Algebra.FormallyUnramified ℤ (HopfTorsor.ConstFun ℤ G)) <;>
      first | rfl | exact Subsingleton.elim _ _

end P2MW.S_HopfTorsor_ConstFun_nonempty_iso_trivial_int
