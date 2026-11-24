import Definitions.Def_HopfTorsor_Coaction
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Etale.Descent

set_option autoImplicit false

/-!
# What a torsor inherits from its group

Properties of the Hopf algebra `H` that are local for the fpqc topology pass to every
`H`-torsor `A`, because `A` and `H` become isomorphic after a faithfully flat base change.
This file records the ones needed over `ℤ`:

* `IsTorsor.torsor_flat`, `IsTorsor.torsor_nontrivial`: from faithful flatness of `A`.
* `IsTorsor.torsor_finite`: `H` finite over `R` implies `A` finite over `R`.
* `IsTorsor.torsor_formallyUnramified`: `H` formally unramified implies `A` formally unramified.

The arithmetic consequence: over `ℤ`, a torsor under a finite étale group is a finite flat
unramified `ℤ`-algebra, so Minkowski's theorem gives it a `ℤ`-point, and a torsor with a point is
trivial (`IsTorsor.nonempty_iso_trivial_of_point`). This is `H¹_fppf(Spec ℤ, G) = 0` for such `G`,
proved without sites. Here Minkowski enters as the hypothesis `MinkowskiPoint`, which has the
shape of `Algebra.FormallyUnramified.nonempty_ringHom_int`; the theorem
`HopfTorsor.IsTorsor.nonempty_iso_trivial_int` (in `Theorems/`) discharges it with that result.
-/

open TensorProduct

namespace HopfTorsor

universe u

variable {R : Type u} [CommRing R] {H : Type u} [CommRing H] [HopfAlgebra R H]
variable {A : Type u} [CommRing A] [Algebra R A] {c : Coaction R H A}

theorem IsTorsor.torsor_flat (hc : IsTorsor c) : Module.Flat R A := by
  have := hc.faithfullyFlat
  infer_instance

theorem IsTorsor.torsor_nontrivial [Nontrivial R] (hc : IsTorsor c) : Nontrivial A := by
  have := hc.faithfullyFlat
  exact (TensorProduct.lid R A).symm.toEquiv.nontrivial

/-- A torsor under a finite group is finite. -/
theorem IsTorsor.torsor_finite [Module.Finite R H] (hc : IsTorsor c) : Module.Finite R A := by
  obtain ⟨R', _, _, hR', e, -⟩ := hc.locallyTrivial
  have : Module.Finite R' (R' ⊗[R] A) := Module.Finite.equiv e.symm.toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat R'

/-- A torsor under a formally unramified group is formally unramified. -/
theorem IsTorsor.torsor_formallyUnramified [Algebra.FormallyUnramified R H] (hc : IsTorsor c) :
    Algebra.FormallyUnramified R A := by
  obtain ⟨R', _, _, hR', e, -⟩ := hc.locallyTrivial
  have : Algebra.FormallyUnramified R' (R' ⊗[R] A) := .of_equiv e.symm
  exact Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat R'

end HopfTorsor

namespace HopfTorsor

/-- Minkowski's theorem in the form used by the repository
(`Algebra.FormallyUnramified.nonempty_ringHom_int`): a nonzero finite flat formally unramified
`ℤ`-algebra has a ring map to `ℤ`. Equivalently, `ℚ` has no nontrivial unramified extension. -/
def MinkowskiPoint : Prop :=
  ∀ (B : Type) [CommRing B] [Nontrivial B] [Module.Finite ℤ B] [Module.Flat ℤ B]
    [Algebra.FormallyUnramified ℤ B], Nonempty (B →+* ℤ)

/-- **Torsors under finite étale groups over `ℤ` are trivial**, given Minkowski's theorem.
In fppf language: `H¹(Spec ℤ, G) = 0` for every finite étale group scheme `G` over `ℤ`. -/
theorem IsTorsor.nonempty_iso_trivial_int_of_minkowski (hM : MinkowskiPoint)
    {H : Type} [CommRing H] [HopfAlgebra ℤ H] [Module.Finite ℤ H]
    [Algebra.FormallyUnramified ℤ H]
    {A : Type} [CommRing A] {c : Coaction ℤ H A} (hc : IsTorsor c) :
    Nonempty (CoactionIso c Coaction.trivial) := by
  -- `Module.Finite ℤ H` may be stated with either `ℤ`-module structure on `H`; they agree.
  have : @Module.Finite ℤ H _ _ Algebra.toModule := by
    convert ‹Module.Finite ℤ H› <;> first | rfl | exact Subsingleton.elim _ _
  have := hc.torsor_nontrivial
  have := hc.torsor_flat
  have := hc.torsor_finite
  have := hc.torsor_formallyUnramified
  obtain ⟨f⟩ := hM A
  exact hc.nonempty_iso_trivial_of_point f.toIntAlgHom

end HopfTorsor
