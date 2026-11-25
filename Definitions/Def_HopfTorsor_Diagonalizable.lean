import Definitions.Def_HopfTorsor_Descent
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Torsors under diagonalizable groups

For a finite commutative group `G`, the group algebra `R[G]` is the coordinate ring of the
diagonalizable group scheme `D(G)`; for `G = ℤ/q` this is `μ_q`, as `R[ℤ/q] = R[x]/(x^q - 1)`.

A coaction of `R[G]` on `A` is a `G`-grading `A = ⊕ A_g`, with `A_g = {a | ρ a = a ⊗ g}`
(`Grading.degPart`) and the degree-`g` component of `a` read off from `ρ a` (`Grading.degProj`).
Equivariant maps preserve degrees, so a trivialisation over `R'` identifies `R' ⊗ A_g` with
`R' ⊗ g`.

Over a principal ideal domain `R` this gives the structure of every torsor:

* `A` is free of rank `|G|`, and each `A_g` is nonzero, so each `A_g` is free of rank one
  (`Diagonalizable.finrank_degPart`). This is where `Pic R = 0` enters.
* the generator of `A_g` is a unit (`Diagonalizable.isUnit_degGen`), and `A_1 = R`
  (`Diagonalizable.exists_algebraMap_of_mem_degPart_one`).
* if `u ↦ u ^ |G|` is bijective on `Rˣ`, each `A_g` contains exactly one `x` with `x ^ |G| = 1`
  (`Diagonalizable.existsUnique_degRoot`). These roots multiply like `G`, so `g ↦ root g` gives an
  isomorphism `R[G] ≅ A` (`Diagonalizable.rootComparison_bijective`), hence an `R`-point.

## Main results

* `HopfTorsor.Diagonalizable.nonempty_iso_trivial`: over a PID on whose units `|G|`-th powers are
  bijective, every `D(G)`-torsor is trivial.
* `HopfTorsor.Diagonalizable.nonempty_iso_trivial_int`: over `ℤ`, for `|G|` odd. With
  `G = ℤ/q` this is `H¹_fppf(Spec ℤ, μ_q) = 0` for odd `q`, proved without sites or Kummer theory.
-/

open TensorProduct MonoidAlgebra

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HopfTorsor

universe u

namespace Grading

variable {R : Type u} [CommRing R] {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The coefficient of `g`, as a linear functional on `R[G]`. -/
noncomputable def lcoeff (g : G) : MonoidAlgebra R G →ₗ[R] R :=
  Finsupp.lapply g ∘ₗ (coeffLinearEquiv R).toLinearMap

lemma lcoeff_single (g h : G) (r : R) :
    lcoeff g (single h r : MonoidAlgebra R G) = if h = g then r else 0 := by
  simp [lcoeff, Finsupp.single_apply]

lemma eq_sum_single_lcoeff (f : MonoidAlgebra R G) : f = ∑ g, single g (lcoeff g f) := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, single_add, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | single h r =>
    simp only [lcoeff_single]
    rw [Finset.sum_eq_single h (fun g _ hg => by rw [if_neg (Ne.symm hg), single_zero])
      (fun h' => absurd (Finset.mem_univ h) h'), if_pos rfl]

lemma comulAH_single (g : G) (r : R) :
    Bialgebra.comulAlgHom R (MonoidAlgebra R G) (single g r) =
      single g r ⊗ₜ[R] single g (1 : R) := by
  rw [Bialgebra.comulAlgHom_apply, MonoidAlgebra.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul]
  simp only [lsingle_apply]
  have h1 : (single g r : MonoidAlgebra R G) = r • single g 1 := by rw [smul_single, smul_eq_mul, mul_one]
  rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

lemma counitAH_single (g : G) (r : R) :
    Bialgebra.counitAlgHom R (MonoidAlgebra R G) (single g r) = r := by
  rw [Bialgebra.counitAlgHom_apply, MonoidAlgebra.counit_single]
  rfl

section Coeff

variable {B : Type u} [AddCommGroup B] [Module R B]

/-- The coefficient of `g` in `B ⊗ R[G] ≅ (G →₀ B)`. -/
noncomputable def coeffAt (g : G) : B ⊗[R] MonoidAlgebra R G →ₗ[R] B :=
  (TensorProduct.rid R B).toLinearMap ∘ₗ LinearMap.lTensor B (lcoeff g)

lemma coeffAt_tmul (g : G) (b : B) (f : MonoidAlgebra R G) :
    coeffAt g (b ⊗ₜ[R] f) = lcoeff g f • b := by
  simp [coeffAt]

lemma coeffAt_tmul_single (g h : G) (b : B) :
    coeffAt g (b ⊗ₜ[R] (single h 1 : MonoidAlgebra R G)) = if h = g then b else 0 := by
  rw [coeffAt_tmul, lcoeff_single]
  split_ifs <;> simp

/-- Every element of `B ⊗ R[G]` is `∑ g, b_g ⊗ g`. -/
lemma eq_sum_coeffAt (y : B ⊗[R] MonoidAlgebra R G) :
    y = ∑ g, coeffAt g y ⊗ₜ[R] (single g 1 : MonoidAlgebra R G) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b f =>
    conv_lhs => rw [eq_sum_single_lcoeff f]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coeffAt_tmul, TensorProduct.smul_tmul, smul_single, smul_eq_mul, mul_one]
  | add y z hy hz =>
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
    rw [← hy, ← hz]

end Coeff

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The degree-`g` component of `a`, for a coaction of `R[G]`. -/
noncomputable def degProj (c : Coaction R (MonoidAlgebra R G) A) (g : G) : A →ₗ[R] A :=
  coeffAt g ∘ₗ c.ρ.toLinearMap

variable (c : Coaction R (MonoidAlgebra R G) A)

lemma degProj_apply (g : G) (a : A) : degProj c g a = coeffAt g (c.ρ a) := rfl

lemma ρ_eq_sum_degProj (a : A) : c.ρ a = ∑ g, degProj c g a ⊗ₜ[R] (single g 1 : MonoidAlgebra R G) :=
  eq_sum_coeffAt (c.ρ a)

/-- Counit: `a = ∑ g, a_g`. -/
lemma eq_sum_degProj (a : A) : a = ∑ g, degProj c g a := by
  have h := congrArg (fun φ : A →ₐ[R] A => φ a) c.counit
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply] at h
  rw [ρ_eq_sum_degProj, map_sum, map_sum] at h
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, counitAH_single] at h
  simpa using h.symm

/-- Coassociativity: `ρ (a_g) = a_g ⊗ g`. -/
lemma ρ_degProj (g : G) (a : A) :
    c.ρ (degProj c g a) = degProj c g a ⊗ₜ[R] (single g 1 : MonoidAlgebra R G) := by
  have h := congrArg (fun φ : A →ₐ[R] A ⊗[R] (MonoidAlgebra R G ⊗[R] MonoidAlgebra R G) => φ a)
    c.coassoc
  simp only [AlgHom.coe_comp, Function.comp_apply] at h
  rw [ρ_eq_sum_degProj, map_sum, map_sum, map_sum] at h
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, comulAH_single] at h
  -- read off the coefficient of `g` in the last factor
  have key := congrArg (LinearMap.lTensor A (coeffAt (B := MonoidAlgebra R G) g)) h
  simp only [map_sum, LinearMap.lTensor_tmul, coeffAt_tmul_single] at key
  have hl : ∀ (h' : G) (y : A ⊗[R] MonoidAlgebra R G),
      LinearMap.lTensor A (coeffAt (B := MonoidAlgebra R G) g)
        ((Algebra.TensorProduct.assoc R R R A (MonoidAlgebra R G) (MonoidAlgebra R G))
          (y ⊗ₜ[R] (single h' 1 : MonoidAlgebra R G))) = if h' = g then y else 0 := by
    intro h' y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x f =>
      simp only [Algebra.TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, coeffAt_tmul_single]
      split_ifs <;> simp
    | add y z hy hz =>
      simp only [TensorProduct.add_tmul, map_add, hy, hz]
      split_ifs <;> simp
  simp only [AlgEquiv.coe_toAlgHom] at key
  simp only [hl] at key
  have hr : ∀ x : G, (degProj c x a ⊗ₜ[R] (if x = g then (single x 1 : MonoidAlgebra R G) else 0)) =
      if x = g then degProj c x a ⊗ₜ[R] (single x 1 : MonoidAlgebra R G) else 0 := by
    intro x; split_ifs <;> simp
  simp only [hr] at key
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq'] at key
  simpa using key

/-- The degree-`g` part `A_g = {a | ρ a = a ⊗ g}`. -/
def degPart (g : G) : Submodule R A where
  carrier := {a | c.ρ a = a ⊗ₜ[R] (single g 1 : MonoidAlgebra R G)}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha, hb, TensorProduct.add_tmul]
  zero_mem' := by simp
  smul_mem' r a ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_smul, ha, TensorProduct.smul_tmul']

variable {c}

lemma mem_degPart {g : G} {a : A} :
    a ∈ degPart c g ↔ c.ρ a = a ⊗ₜ[R] (single g 1 : MonoidAlgebra R G) := Iff.rfl

lemma degProj_mem (g : G) (a : A) : degProj c g a ∈ degPart c g := ρ_degProj c g a

lemma degProj_of_mem {g : G} {a : A} (ha : a ∈ degPart c g) (h : G) :
    degProj c h a = if g = h then a else 0 := by
  rw [degProj_apply, mem_degPart.mp ha, coeffAt_tmul_single]

lemma one_mem_degPart : (1 : A) ∈ degPart c 1 := by
  rw [mem_degPart, map_one, Algebra.TensorProduct.one_def, ← MonoidAlgebra.one_def]

lemma mul_mem_degPart {g h : G} {a b : A} (ha : a ∈ degPart c g) (hb : b ∈ degPart c h) :
    a * b ∈ degPart c (g * h) := by
  rw [mem_degPart] at *
  rw [map_mul, ha, hb, Algebra.TensorProduct.tmul_mul_tmul, single_mul_single, mul_one]

lemma pow_mem_degPart {g : G} {a : A} (ha : a ∈ degPart c g) (n : ℕ) : a ^ n ∈ degPart c (g ^ n) := by
  induction n with
  | zero => simpa using one_mem_degPart
  | succ n ih => rw [pow_succ, pow_succ]; exact mul_mem_degPart ih ha

lemma degProj_degProj (g h : G) (a : A) : degProj c h (degProj c g a) = if g = h then degProj c g a else 0 :=
  degProj_of_mem (degProj_mem g a) h

variable (c) in
/-- `A ≅ ∏ g, A_g`. -/
noncomputable def decompose : A ≃ₗ[R] (∀ g : G, degPart c g) where
  toFun a g := ⟨degProj c g a, degProj_mem g a⟩
  map_add' a b := by ext g; simp
  map_smul' r a := by ext g; simp
  invFun x := ∑ g, (x g : A)
  left_inv a := (eq_sum_degProj c a).symm
  right_inv x := by
    funext h
    apply Subtype.ext
    simp only [map_sum]
    rw [Finset.sum_eq_single h (fun g _ hg => by rw [degProj_of_mem (x g).2, if_neg hg])
      (fun h' => absurd (Finset.mem_univ h) h'), degProj_of_mem (x h).2, if_pos rfl]


section Equivariance

/-- Taking coefficients commutes with algebra maps on the first factor. -/
lemma coeffAt_map {B C : Type u} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (φ : B →ₐ[R] C) (g : G) (y : B ⊗[R] MonoidAlgebra R G) :
    coeffAt g (Algebra.TensorProduct.map φ (AlgHom.id R (MonoidAlgebra R G)) y) =
      φ (coeffAt g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b f => simp [coeffAt_tmul]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- The components of the base-changed coaction are the base-changed components. -/
lemma coeffAt_baseChangeρ (R' : Type u) [CommRing R'] [Algebra R R'] (g : G)
    (y : R' ⊗[R] A) : coeffAt g (c.baseChangeρ R' y) = (degProj c g).lTensor R' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    simp only [Coaction.baseChangeρ, AlgHom.coe_comp, Function.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.lTensor_tmul, degProj_apply,
      AlgEquiv.coe_toAlgHom]
    generalize c.ρ a = w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x f => simp [coeffAt_tmul]
    | add w₁ w₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- The components of the trivial coaction: the degree-`g` part of `f` is its `g`-term. -/
lemma degProj_trivial (g : G) (f : MonoidAlgebra R G) :
    degProj (Coaction.trivial (R := R) (H := MonoidAlgebra R G)) g f = single g (lcoeff g f) := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, single_add]
  | single h r =>
    rw [degProj_apply]
    change coeffAt g (Bialgebra.comulAlgHom R (MonoidAlgebra R G) (single h r)) = _
    rw [comulAH_single, coeffAt_tmul, lcoeff_single, lcoeff_single]
    split_ifs with hh
    · subst hh; rw [smul_single, smul_eq_mul, one_mul]
    · simp

/-- **Equivariance of a trivialisation, degree by degree.** If `c` is a torsor, trivialised by
`e` over `R'`, then `e` carries the degree-`g` component to the degree-`g` component. -/
theorem exists_trivialisation_degProj (hc : IsTorsor c) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'), Module.FaithfullyFlat R R' ∧
      ∃ e : R' ⊗[R] A ≃ₐ[R'] R' ⊗[R] MonoidAlgebra R G, ∀ (g : G) (y : R' ⊗[R] A),
        e ((degProj c g).lTensor R' y) =
          (degProj (Coaction.trivial (R := R) (H := MonoidAlgebra R G)) g).lTensor R' (e y) := by
  obtain ⟨R', _, _, hR', e, he⟩ := hc.locallyTrivial
  refine ⟨R', inferInstance, inferInstance, hR', e, fun g y => ?_⟩
  have h := congrArg (fun φ : R' ⊗[R] A →ₐ[R] (R' ⊗[R] MonoidAlgebra R G) ⊗[R] MonoidAlgebra R G =>
    coeffAt g (φ y)) he
  simp only [AlgHom.coe_comp, Function.comp_apply] at h
  rw [coeffAt_map, coeffAt_baseChangeρ, coeffAt_baseChangeρ] at h
  exact h

end Equivariance

end Grading

/-! ### Over a principal ideal domain: every graded piece is free of rank one -/

namespace Diagonalizable

open Grading Module

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]

instance : Module.Finite R (MonoidAlgebra R G) := Module.Finite.of_basis (MonoidAlgebra.basis G R)
instance : Module.Free R (MonoidAlgebra R G) := Module.Free.of_basis (MonoidAlgebra.basis G R)

variable {A : Type u} [CommRing A] [Algebra R A] {c : Coaction R (MonoidAlgebra R G) A}

omit [IsPrincipalIdealRing R] in
lemma ffBase_nontrivial (R' : Type u) [CommRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R'] : Nontrivial R' :=
  (TensorProduct.lid R R').symm.toEquiv.nontrivial

section Basic

variable (hc : IsTorsor c)
include hc

lemma torsor_faithfullyFlat : Module.FaithfullyFlat R A := hc.faithfullyFlat

lemma finite : Module.Finite R A := hc.torsor_finite

lemma free : Module.Free R A := by
  have := hc.torsor_finite
  have := hc.torsor_flat
  infer_instance

lemma torsor_algebraMap_injective : Function.Injective (algebraMap R A) := by
  have := hc.torsor_flat
  have := hc.torsor_nontrivial
  intro k l hkl
  have h : (k - l) • (1 : A) = 0 := by
    rw [sub_smul, Algebra.smul_def, Algebra.smul_def, hkl, sub_self]
  rcases smul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h one_ne_zero

/-- `A` has rank `|G|`. -/
lemma torsor_finrank_eq_card : finrank R A = Fintype.card G := by
  have := finite hc
  have := free hc
  obtain ⟨R', _, _, hR', e, -⟩ := hc.locallyTrivial
  have := ffBase_nontrivial (R := R) R'
  have h := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_baseChange] at h
  rw [h, Module.finrank_eq_card_basis (MonoidAlgebra.basis G R)]

lemma degPart_isTorsionFree (g : G) : IsTorsionFree R (degPart c g) :=
  have := hc.torsor_flat
  Function.Injective.moduleIsTorsionFree _ Subtype.val_injective (fun _ _ => rfl)

lemma degPart_finite (g : G) : Module.Finite R (degPart c g) := by
  have := finite hc
  infer_instance

lemma degPart_free (g : G) : Module.Free R (degPart c g) := by
  have := degPart_finite hc g
  have := degPart_isTorsionFree hc g
  infer_instance

/-- Every graded piece is nonzero: otherwise its base change, which the trivialisation identifies
with `R' ⊗ g`, would vanish. -/
lemma degPart_nontrivial (g : G) : Nontrivial (degPart c g) := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have hzero : degProj c g = 0 := by
    ext a
    exact congrArg Subtype.val (Subsingleton.elim (⟨degProj c g a, degProj_mem g a⟩ : degPart c g) 0)
  obtain ⟨R', _, _, hR', e, he⟩ := exists_trivialisation_degProj hc
  have := ffBase_nontrivial (R := R) R'
  have h := he g (e.symm (1 ⊗ₜ[R] (single g 1 : MonoidAlgebra R G)))
  rw [hzero, LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero, AlgEquiv.apply_symm_apply,
    LinearMap.lTensor_tmul, degProj_trivial, lcoeff_single, if_pos rfl] at h
  have h' := congrArg (coeffAt (B := R') g) h
  rw [map_zero, coeffAt_tmul_single, if_pos rfl] at h'
  exact zero_ne_one h'

/-- Every graded piece has rank one: the ranks are positive and add up to `|G|`. -/
lemma finrank_degPart (g : G) : finrank R (degPart c g) = 1 := by
  have := finite hc
  have := free hc
  have := fun g => degPart_finite hc g
  have := fun g => degPart_free hc g
  have hsum : ∑ g, finrank R (degPart c g) = ∑ _g : G, 1 := by
    rw [← Module.finrank_pi_fintype, ← (decompose c).finrank_eq, torsor_finrank_eq_card hc]
    simp
  have hpos : ∀ g ∈ Finset.univ, 1 ≤ finrank R (degPart c g) := fun g _ =>
    (finrank_pos_iff_of_free R (degPart c g)).mpr (degPart_nontrivial hc g)
  exact ((Finset.sum_eq_sum_iff_of_le hpos).mp hsum.symm g (Finset.mem_univ g)).symm

/-- A basis of the degree-`g` piece, of size one. -/
noncomputable def basisDegPart (g : G) : Basis (Fin 1) R (degPart c g) :=
  letI := degPart_finite hc g
  letI := degPart_free hc g
  Module.finBasisOfFinrankEq R (degPart c g) (finrank_degPart hc g)

/-- A generator of the degree-`g` piece. -/
noncomputable def degGen (g : G) : A := (basisDegPart hc g 0 : A)

lemma degGen_mem (g : G) : degGen hc g ∈ degPart c g := (basisDegPart hc g 0).2

lemma mem_degPart_iff (g : G) {a : A} : a ∈ degPart c g ↔ ∃ k : R, a = k • degGen hc g := by
  constructor
  · intro ha
    refine ⟨(basisDegPart hc g).repr ⟨a, ha⟩ 0, ?_⟩
    have h := (basisDegPart hc g).sum_repr ⟨a, ha⟩
    rw [Fin.sum_univ_one] at h
    exact (congrArg Subtype.val h).symm
  · rintro ⟨k, rfl⟩
    exact Submodule.smul_mem _ k (degGen_mem hc g)

/-- **The generators are units.** After base change to `R'`, the generator of `R' ⊗ A_g` is
carried to a multiple of `1 ⊗ g`, which is a unit; so `1 ⊗ degGen g` is a unit, and multiplication by
`degGen g` is bijective because it is so after the faithfully flat base change. -/
lemma isUnit_degGen (g : G) : IsUnit (degGen hc g) := by
  obtain ⟨R', _, _, hR', e, he⟩ := exists_trivialisation_degProj hc
  have hspan : ∀ w : R' ⊗[R] A, ∃ t : R', (degProj c g).lTensor R' w = t • (1 ⊗ₜ[R] degGen hc g) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r a =>
      obtain ⟨k, hk⟩ := (mem_degPart_iff hc g).mp (degProj_mem g a)
      refine ⟨k • r, ?_⟩
      rw [LinearMap.lTensor_tmul, hk, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨t₁, ht₁⟩ := h₁
      obtain ⟨t₂, ht₂⟩ := h₂
      exact ⟨t₁ + t₂, by rw [map_add, ht₁, ht₂, add_smul]⟩
  obtain ⟨t, ht⟩ := hspan (e.symm (1 ⊗ₜ[R] (single g 1 : MonoidAlgebra R G)))
  have h := he g (e.symm (1 ⊗ₜ[R] (single g 1 : MonoidAlgebra R G)))
  have hsmul : ∀ y : R' ⊗[R] MonoidAlgebra R G, t • y = (t ⊗ₜ[R] (1 : MonoidAlgebra R G)) * y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r f => rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        smul_eq_mul]
    | add y z hy hz => rw [smul_add, hy, hz, mul_add]
  rw [ht, AlgEquiv.apply_symm_apply, LinearMap.lTensor_tmul, degProj_trivial, lcoeff_single,
    if_pos rfl, map_smul, hsmul] at h
  have hu : e (1 ⊗ₜ[R] degGen hc g) * ((t ⊗ₜ[R] (1 : MonoidAlgebra R G)) *
      (1 ⊗ₜ[R] (single g⁻¹ 1 : MonoidAlgebra R G))) = 1 := by
    rw [← mul_assoc, mul_comm (e _), h, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      single_mul_single, mul_inv_cancel, mul_one, ← MonoidAlgebra.one_def,
      Algebra.TensorProduct.one_def]
  have hunit : IsUnit (1 ⊗ₜ[R] degGen hc g : R' ⊗[R] A) :=
    (isUnit_map_iff e _).mp (IsUnit.of_mul_eq_one _ hu)
  let f : A →ₗ[R] A := LinearMap.mulLeft R (degGen hc g)
  have hf : (f.lTensor R' : R' ⊗[R] A → R' ⊗[R] A) = fun w => (1 ⊗ₜ[R] degGen hc g) * w := by
    funext w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp [f, Algebra.TensorProduct.tmul_mul_tmul]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂, mul_add]
  have hbij : Function.Bijective (f.lTensor R') := by
    rw [hf]
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp hunit
  have hfbij := (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R R' f).mp hbij
  obtain ⟨b, hb⟩ := hfbij.2 1
  exact IsUnit.of_mul_eq_one b hb

/-- An element of `R` that becomes a unit in a faithfully flat `R`-algebra is a unit. -/
lemma torsor_isUnit_of_isUnit_algebraMap {k : R} (hk : IsUnit (algebraMap R A k)) : IsUnit k := by
  have hff := torsor_faithfullyFlat hc
  by_contra hnk
  have hI : Ideal.span {k} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  apply ((Module.FaithfullyFlat.iff_flat_and_proper_ideal R A).mp hff).2 _ hI
  rw [eq_top_iff]
  intro a _
  obtain ⟨v, hv⟩ := hk.exists_right_inv
  have ha : a = k • (v * a) := by rw [Algebra.smul_def, ← mul_assoc, hv, one_mul]
  rw [ha]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self k) Submodule.mem_top

/-- **The invariants are `R`.** -/
lemma exists_algebraMap_of_mem_degPart_one {a : A} (ha : a ∈ degPart c 1) :
    ∃ m : R, a = algebraMap R A m := by
  obtain ⟨k, hk⟩ := (mem_degPart_iff hc 1).mp (one_mem_degPart (c := c))
  rw [Algebra.smul_def] at hk
  have hk' : IsUnit k := torsor_isUnit_of_isUnit_algebraMap hc (IsUnit.of_mul_eq_one _ hk.symm)
  have he1 : degGen hc 1 = algebraMap R A (hk'.unit⁻¹ : Rˣ) := by
    have h2 : algebraMap R A k * algebraMap R A (hk'.unit⁻¹ : Rˣ) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    have hku : IsUnit (algebraMap R A k) := hk'.map _
    exact hku.mul_left_cancel (hk.symm.trans h2.symm)
  obtain ⟨l, hl⟩ := (mem_degPart_iff hc 1).mp ha
  exact ⟨l * (hk'.unit⁻¹ : Rˣ), by rw [hl, he1, Algebra.smul_def, map_mul]⟩

/-- `degGen g ^ |G|` is a unit of `R`. -/
lemma degGen_pow_card (g : G) : ∃ m : Rˣ, degGen hc g ^ Fintype.card G = algebraMap R A m := by
  have hmem := pow_mem_degPart (degGen_mem hc g) (Fintype.card G)
  rw [pow_card_eq_one] at hmem
  obtain ⟨m, hm⟩ := exists_algebraMap_of_mem_degPart_one hc hmem
  have hmu : IsUnit m := torsor_isUnit_of_isUnit_algebraMap hc (hm ▸ (isUnit_degGen hc g).pow _)
  exact ⟨hmu.unit, hm⟩

end Basic

/-! ### The canonical generators, and a point -/

section Point

variable (hc : IsTorsor c) (hroot : Function.Bijective (fun u : Rˣ => u ^ Fintype.card G))
include hc hroot

/-- **In each degree there is exactly one `x` with `x ^ |G| = 1`.** Writing `x = k • degGen g` and
`degGen g ^ |G| = m`, the condition says `k ^ |G| = m⁻¹`, which has exactly one solution `k`
because `u ↦ u ^ |G|` is bijective on `Rˣ`. -/
lemma existsUnique_degRoot (g : G) : ∃! x : A, x ∈ degPart c g ∧ x ^ Fintype.card G = 1 := by
  obtain ⟨m, hm⟩ := degGen_pow_card hc g
  have hinj := torsor_algebraMap_injective hc
  -- the coefficient of a root is a unit whose power is `m⁻¹`
  have hcoeff : ∀ k : R, (k • degGen hc g) ^ Fintype.card G = 1 → k ^ Fintype.card G = ↑m⁻¹ := by
    intro k hk
    rw [Algebra.smul_def, mul_pow, hm, ← map_pow, ← map_mul, ← map_one (algebraMap R A)] at hk
    have hk' := hinj hk
    calc k ^ Fintype.card G = k ^ Fintype.card G * m * ↑m⁻¹ := by rw [mul_assoc, Units.mul_inv,
          mul_one]
      _ = ↑m⁻¹ := by rw [hk', one_mul]
  obtain ⟨n', hn'⟩ : ∃ n', Fintype.card G = n' + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have hunit : ∀ k : R, k ^ Fintype.card G = ↑m⁻¹ → IsUnit k := by
    intro k hk
    refine IsUnit.of_mul_eq_one (k ^ n' * m) ?_
    rw [← mul_assoc, ← pow_succ', ← hn', hk, Units.inv_mul]
  obtain ⟨t, ht⟩ := hroot.2 m⁻¹
  simp only at ht
  refine ⟨(t : R) • degGen hc g, ⟨Submodule.smul_mem _ _ (degGen_mem hc g), ?_⟩, ?_⟩
  · rw [Algebra.smul_def, mul_pow, hm, ← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ht,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  · rintro y ⟨hy, hy1⟩
    obtain ⟨l, rfl⟩ := (mem_degPart_iff hc g).mp hy
    have hl := hcoeff l hy1
    have hlu := hunit l hl
    have : hlu.unit = t := hroot.1 (by
      simp only
      rw [ht]
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hl]))
    rw [← this, IsUnit.unit_spec]

/-- The unique element of degree `g` whose `|G|`-th power is `1`. -/
noncomputable def degRoot (g : G) : A := (existsUnique_degRoot hc hroot g).exists.choose

lemma degRoot_spec (g : G) : degRoot hc hroot g ∈ degPart c g ∧ degRoot hc hroot g ^ Fintype.card G = 1 :=
  (existsUnique_degRoot hc hroot g).exists.choose_spec

lemma eq_degRoot {g : G} {x : A} (hx : x ∈ degPart c g) (hx1 : x ^ Fintype.card G = 1) :
    x = degRoot hc hroot g :=
  (existsUnique_degRoot hc hroot g).unique ⟨hx, hx1⟩ (degRoot_spec hc hroot g)

/-- The roots multiply like the group: a character `G →* A`. -/
noncomputable def rootCharacter : G →* A where
  toFun := degRoot hc hroot
  map_one' := (eq_degRoot hc hroot (one_mem_degPart (c := c)) (one_pow _)).symm
  map_mul' g h := (eq_degRoot hc hroot (mul_mem_degPart (degRoot_spec hc hroot g).1
    (degRoot_spec hc hroot h).1) (by rw [mul_pow, (degRoot_spec hc hroot g).2,
      (degRoot_spec hc hroot h).2, mul_one])).symm

lemma rootCharacter_apply (g : G) : rootCharacter hc hroot g = degRoot hc hroot g := rfl

/-- Every element of degree `g` is an `R`-multiple of `degRoot g`. -/
lemma exists_smul_degRoot {g : G} {x : A} (hx : x ∈ degPart c g) : ∃ k : R, x = k • degRoot hc hroot g := by
  obtain ⟨n', hn'⟩ : ∃ n', Fintype.card G = n' + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have hmem : x * degRoot hc hroot g ^ n' ∈ degPart c 1 := by
    have := mul_mem_degPart hx (pow_mem_degPart (degRoot_spec hc hroot g).1 n')
    rwa [← pow_succ', ← hn', pow_card_eq_one] at this
  obtain ⟨k, hk⟩ := exists_algebraMap_of_mem_degPart_one hc hmem
  refine ⟨k, ?_⟩
  calc x = x * degRoot hc hroot g ^ Fintype.card G := by rw [(degRoot_spec hc hroot g).2, mul_one]
    _ = x * degRoot hc hroot g ^ n' * degRoot hc hroot g := by rw [hn', pow_succ, mul_assoc]
    _ = k • degRoot hc hroot g := by rw [hk, Algebra.smul_def]

/-- The comparison map `R[G] → A`, `g ↦ degRoot g`. -/
noncomputable def rootComparison : MonoidAlgebra R G →ₐ[R] A :=
  MonoidAlgebra.lift R A G (rootCharacter hc hroot)

lemma rootComparison_bijective : Function.Bijective (rootComparison hc hroot) := by
  have := hc.torsor_flat
  have := hc.torsor_nontrivial
  have hΨ : ∀ f : MonoidAlgebra R G,
      rootComparison hc hroot f = ∑ g, lcoeff g f • degRoot hc hroot g := by
    intro f
    conv_lhs => rw [eq_sum_single_lcoeff f]
    simp [rootComparison, rootCharacter_apply]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f hf
    have hcoeff : ∀ h : G, lcoeff h f = 0 := by
      intro h
      have := congrArg (degProj c h) hf
      rw [hΨ, map_sum, map_zero] at this
      simp only [map_smul, degProj_of_mem (degRoot_spec hc hroot _).1] at this
      rw [Finset.sum_eq_single h (fun g _ hg => by rw [if_neg hg, smul_zero])
        (fun h' => absurd (Finset.mem_univ h) h'), if_pos rfl] at this
      have hne : degRoot hc hroot h ≠ 0 := fun h0 => by
        have h1 := (degRoot_spec hc hroot h).2
        rw [h0, zero_pow Fintype.card_ne_zero] at h1
        exact zero_ne_one h1
      rcases smul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd h' hne
    rw [eq_sum_single_lcoeff f]
    simp [hcoeff]
  · intro a
    choose k hk using fun g => exists_smul_degRoot hc hroot (degProj_mem g a)
    refine ⟨∑ g, single g (k g), ?_⟩
    rw [map_sum, eq_sum_degProj c a]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [rootComparison, MonoidAlgebra.lift_single, rootCharacter_apply, hk g]

end Point

/-- **Torsors under a diagonalizable group over a PID are trivial when `|G|`-th powers are
bijective on units.** For `R = ℤ` and `|G|` odd this covers `μ_q` for odd `q`: the two arithmetic
inputs are that finitely generated torsion-free `ℤ`-modules are free (`Pic ℤ = 0`) and that the
units `±1` are their own odd powers. -/
theorem nonempty_iso_trivial (hc : IsTorsor c)
    (hroot : Function.Bijective (fun u : Rˣ => u ^ Fintype.card G)) :
    Nonempty (CoactionIso c (Coaction.trivial (R := R) (H := MonoidAlgebra R G))) :=
  hc.nonempty_iso_trivial_of_point ((Bialgebra.counitAlgHom R (MonoidAlgebra R G)).comp
    (AlgEquiv.ofBijective (rootComparison hc hroot) (rootComparison_bijective hc hroot)).symm.toAlgHom)

/-- Odd powers are bijective on `ℤˣ = {±1}`. -/
lemma int_pow_bijective {n : ℕ} (hn : Odd n) : Function.Bijective (fun u : ℤˣ => u ^ n) := by
  have : (fun u : ℤˣ => u ^ n) = id := by
    funext u
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp
    · exact hn.neg_one_pow
  rw [this]
  exact Function.bijective_id

/-- **`μ_q`-torsors over `ℤ` are trivial for odd `q`**, and more generally torsors under `D(G)`
for any finite commutative group `G` of odd order. -/
theorem nonempty_iso_trivial_int {G : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    (hG : Odd (Fintype.card G)) {A : Type} [CommRing A]
    {c : Coaction ℤ (MonoidAlgebra ℤ G) A} (hc : IsTorsor c) :
    Nonempty (CoactionIso c (Coaction.trivial (R := ℤ) (H := MonoidAlgebra ℤ G))) :=
  nonempty_iso_trivial hc (int_pow_bijective hG)

end Diagonalizable

end HopfTorsor
