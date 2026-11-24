import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

set_option autoImplicit false

/-!
# Torsors under an affine group scheme, written as algebras

Pilot for removing fppf sheaves from Mazur's step of the FLT proof.

For a commutative Hopf algebra `H` over a commutative ring `R` (so `G = Spec H` is an affine
group scheme over `Spec R`), a `G`-torsor over `Spec R` is, algebraically, a faithfully flat
commutative `R`-algebra `A` with a coassociative, counital coaction `ρ : A → A ⊗[R] H` that
becomes isomorphic to the trivial coaction `Δ : H → H ⊗[R] H` after some faithfully flat base
change `R → R'`. Classes of such torsors are what fppf `H¹(Spec R, G)` counts, but nothing here
mentions a site or a sheaf: for `H` of finite type over `ℤ`, a torsor is a finitely presented
`ℤ`-algebra with a coaction, which is finite data.

## Main definitions

* `HopfTorsor.Coaction R H A`: a right coaction of `H` on the `R`-algebra `A`.
* `HopfTorsor.Coaction.trivial R H`: `H` coacting on itself by comultiplication.
* `HopfTorsor.Coaction.baseChange`: the coaction on `R' ⊗[R] A`.
* `HopfTorsor.Coaction.Iso`: isomorphisms of algebras with coaction.
* `HopfTorsor.IsTorsor`: faithfully flat, and trivial after a faithfully flat base change.

## Main results

* `HopfTorsor.Coaction.trivial_isTorsor`: the trivial coaction is a torsor when `H` is
  faithfully flat over `R`.
* `HopfTorsor.IsTorsor.of_iso`: being a torsor is invariant under isomorphism of coactions.
-/

open TensorProduct

namespace HopfTorsor

universe u

variable (R : Type u) [CommRing R] (H : Type u) [CommRing H] [HopfAlgebra R H]

/-- A right coaction of the Hopf algebra `H` on the commutative `R`-algebra `A`, as an algebra
map `ρ : A → A ⊗ H` that is coassociative and counital. Geometrically: an action of
`G = Spec H` on `Spec A` over `Spec R`. -/
structure Coaction (A : Type u) [CommRing A] [Algebra R A] where
  /-- The coaction map. -/
  ρ : A →ₐ[R] A ⊗[R] H
  /-- `(ρ ⊗ id) ∘ ρ = (id ⊗ Δ) ∘ ρ`, up to the associator. -/
  coassoc : (Algebra.TensorProduct.assoc R R R A H H : (A ⊗[R] H) ⊗[R] H →ₐ[R] A ⊗[R] (H ⊗[R] H)).comp
      ((Algebra.TensorProduct.map ρ (AlgHom.id R H)).comp ρ) =
    (Algebra.TensorProduct.map (AlgHom.id R A) (Bialgebra.comulAlgHom R H)).comp ρ
  /-- `(id ⊗ ε) ∘ ρ = id`, up to `A ⊗ R ≅ A`. -/
  counit : (Algebra.TensorProduct.rid R R A : A ⊗[R] R →ₐ[R] A).comp
      ((Algebra.TensorProduct.map (AlgHom.id R A) (Bialgebra.counitAlgHom R H)).comp ρ) =
    AlgHom.id R A

namespace Coaction

variable {R H}

/-- `H` coacting on itself by its comultiplication: the trivial torsor. -/
noncomputable def trivial : Coaction R H H where
  ρ := Bialgebra.comulAlgHom R H
  coassoc := by
    apply AlgHom.toLinearMap_injective
    ext x
    exact LinearMap.congr_fun (Coalgebra.coassoc (R := R) (A := H)) x
  counit := by
    ext x
    have h : Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.counitAlgHom R H)
        (Bialgebra.comulAlgHom R H x) = x ⊗ₜ[R] (1 : R) :=
      LinearMap.congr_fun (Coalgebra.lTensor_counit_comp_comul (R := R) (A := H)) x
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    rw [h]
    simp

variable {A : Type u} [CommRing A] [Algebra R A]
variable (R' : Type u) [CommRing R'] [Algebra R R']

/-- The coaction after base change along `R → R'`, on `R' ⊗[R] A`, still with `H` over `R`. -/
noncomputable def baseChange (c : Coaction R H A) : R' ⊗[R] A →ₐ[R] (R' ⊗[R] A) ⊗[R] H :=
  (Algebra.TensorProduct.assoc R R R R' A H).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R R') c.ρ)

variable {B : Type u} [CommRing B] [Algebra R B]

/-- An isomorphism of algebras with coaction: an algebra isomorphism `A ≃ B` that intertwines
the coactions. Geometrically: a `G`-equivariant isomorphism `Spec B ≅ Spec A`. -/
structure Iso (c : Coaction R H A) (d : Coaction R H B) where
  /-- The underlying algebra isomorphism. -/
  e : A ≃ₐ[R] B
  /-- `(e ⊗ id) ∘ ρ_A = ρ_B ∘ e`. -/
  comm : (Algebra.TensorProduct.map (e : A →ₐ[R] B) (AlgHom.id R H)).comp c.ρ = d.ρ.comp e

end Coaction

open Coaction

variable {R H}

/-- The coaction `c` on `A` is a torsor: `A` is faithfully flat over `R`, and after some faithfully
flat base change `R → R'` it becomes isomorphic, as an `R'`-algebra with coaction, to the trivial
torsor. This is the algebraic form of an fppf `Spec H`-torsor over `Spec R`. -/
structure IsTorsor {A : Type u} [CommRing A] [Algebra R A] (c : Coaction R H A) : Prop where
  faithfullyFlat : Module.FaithfullyFlat R A
  locallyTrivial : ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
    Module.FaithfullyFlat R R' ∧
    ∃ e : R' ⊗[R] A ≃ₐ[R'] R' ⊗[R] H,
      (Algebra.TensorProduct.map (e.toAlgHom.restrictScalars R) (AlgHom.id R H)).comp
          (c.baseChange R') =
        (Coaction.trivial.baseChange R').comp (e.toAlgHom.restrictScalars R)

/-- The trivial coaction is a torsor, as soon as `H` is faithfully flat over `R` (for an affine
group scheme of finite type over a field or over `ℤ`, flat suffices: the counit makes `R` a
direct summand of `H`). Here one can take `R' = R`. -/
theorem Coaction.trivial_isTorsor [Module.FaithfullyFlat R H] :
    IsTorsor (Coaction.trivial (R := R) (H := H)) where
  faithfullyFlat := inferInstance
  locallyTrivial := ⟨R, inferInstance, inferInstance, inferInstance, AlgEquiv.refl, by
    have h : (AlgEquiv.refl : R ⊗[R] H ≃ₐ[R] R ⊗[R] H).toAlgHom.restrictScalars R =
        AlgHom.id R (R ⊗[R] H) := rfl
    rw [h, Algebra.TensorProduct.map_id, AlgHom.id_comp, AlgHom.comp_id]⟩

/-- Base change intertwines with an isomorphism of coactions: for `i : A ≃ B` compatible with the
coactions, `R' ⊗ i⁻¹ : R' ⊗ B ≃ R' ⊗ A` is compatible with the base-changed coactions. -/
theorem Coaction.Iso.baseChange_symm {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] {c : Coaction R H A} {d : Coaction R H B} (i : Coaction.Iso c d)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    (Algebra.TensorProduct.map
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : R' ≃ₐ[R'] R') i.e.symm).toAlgHom.restrictScalars R)
        (AlgHom.id R H)).comp (d.baseChange R') =
      (c.baseChange R').comp
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : R' ≃ₐ[R'] R') i.e.symm).toAlgHom.restrictScalars R) := by
  -- `ρ_A ∘ i⁻¹ = (i⁻¹ ⊗ id) ∘ ρ_B`, from `i.comm`
  have hinv : ∀ y : A ⊗[R] H, Algebra.TensorProduct.map (i.e.symm : B →ₐ[R] A) (AlgHom.id R H)
      (Algebra.TensorProduct.map (i.e : A →ₐ[R] B) (AlgHom.id R H) y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a h => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hρ : ∀ b : B, c.ρ (i.e.symm b) =
      Algebra.TensorProduct.map (i.e.symm : B →ₐ[R] A) (AlgHom.id R H) (d.ρ b) := by
    intro b
    have h1 : Algebra.TensorProduct.map (i.e : A →ₐ[R] B) (AlgHom.id R H) (c.ρ (i.e.symm b)) =
        d.ρ b := by
      have := congrArg (fun φ : A →ₐ[R] B ⊗[R] H => φ (i.e.symm b)) i.comm
      simpa using this
    rw [← h1, hinv]
  ext x
  · simp [baseChange, Algebra.TensorProduct.one_def]
  · have hf : ((Algebra.TensorProduct.congr (AlgEquiv.refl : R' ≃ₐ[R'] R') i.e.symm :
        R' ⊗[R] B →ₐ[R'] R' ⊗[R] A) ((1 : R') ⊗ₜ[R] x)) = (1 : R') ⊗ₜ[R] i.e.symm x := rfl
    simp only [baseChange, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]
    rw [hf, Algebra.TensorProduct.map_tmul, hρ x]
    induction d.ρ x using TensorProduct.induction_on with
    | zero => simp
    | tmul b h => simp
    | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]

/-- Being a torsor is invariant under isomorphism of algebras with coaction. -/
theorem IsTorsor.of_iso {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    {c : Coaction R H A} {d : Coaction R H B} (i : Coaction.Iso c d) (hc : IsTorsor c) :
    IsTorsor d := by
  obtain ⟨hA, R', _, _, hR', e, he⟩ := hc
  refine ⟨Module.FaithfullyFlat.of_linearEquiv R A i.e.symm.toLinearEquiv, R', inferInstance,
    inferInstance, hR', ?_⟩
  let f : R' ⊗[R] B ≃ₐ[R'] R' ⊗[R] A :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : R' ≃ₐ[R'] R') i.e.symm
  refine ⟨f.trans e, ?_⟩
  have key := i.baseChange_symm R'
  have hfe : ((f.trans e).toAlgHom.restrictScalars R) =
      (e.toAlgHom.restrictScalars R).comp (f.toAlgHom.restrictScalars R) := rfl
  rw [hfe, ← AlgHom.comp_id (AlgHom.id R H), Algebra.TensorProduct.map_comp, AlgHom.comp_assoc,
    key, ← AlgHom.comp_assoc, he, AlgHom.comp_assoc]

end HopfTorsor
