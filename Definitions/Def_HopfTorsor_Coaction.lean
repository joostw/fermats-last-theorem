import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Convolution
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
* `HopfTorsor.transl_bijective`: translation of the trivial torsor by a point is bijective; its
  inverse is translation by the convolution inverse `g ∘ S`.
* `HopfTorsor.eq_transl_of_equivariant`: every equivariant endomorphism of the trivial torsor
  over `S` is the translation by an `S`-point.
* `HopfTorsor.IsTorsor.nonempty_iso_trivial_of_point`: a torsor with an `R`-point is isomorphic to
  the trivial torsor. The proof base-changes to a trivialising faithfully flat `R'`, where the map
  becomes an equivariant endomorphism of the trivial torsor, hence a bijective translation, and
  descends bijectivity along `R → R'`.
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

/-! ### Translations of the trivial torsor -/

section Translation

open WithConv

variable {S : Type u} [CommRing S] [Algebra R S]

/-- Translation by an `S`-point `g` of `G = Spec H`, as an `S`-algebra endomorphism of the trivial
torsor `S ⊗ H` over `S`: `s ⊗ h ↦ s · (g ⊗ id)(Δ h)`. -/
noncomputable def transl (g : WithConv (H →ₐ[R] S)) : S ⊗[R] H →ₐ[S] S ⊗[R] H :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft)
    ((Algebra.TensorProduct.map g.ofConv (AlgHom.id R H)).comp (Bialgebra.comulAlgHom R H))
    (fun _ _ => Commute.all _ _)

/-- `(g ⊗ id) ∘ Δ` is the convolution of `g` (pushed into `S ⊗ H`) with the inclusion of `H`. -/
lemma map_comp_comul_eq (g : WithConv (H →ₐ[R] S)) :
    (Algebra.TensorProduct.map g.ofConv (AlgHom.id R H)).comp (Bialgebra.comulAlgHom R H) =
      (toConv ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] H).comp g.ofConv) *
        toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] S ⊗[R] H)).ofConv := by
  rw [AlgHom.convMul_def, ofConv_toConv, ← AlgHom.comp_assoc]
  congr 1
  ext a <;> simp

lemma transl_comp_includeRight (g : WithConv (H →ₐ[R] S)) :
    ((transl (R := R) (H := H) g).restrictScalars R).comp Algebra.TensorProduct.includeRight =
      (Algebra.TensorProduct.map g.ofConv (AlgHom.id R H)).comp (Bialgebra.comulAlgHom R H) := by
  ext h
  simp [transl]

lemma transl_comp_includeLeft (g : WithConv (H →ₐ[R] S)) :
    ((transl (R := R) (H := H) g).restrictScalars R).comp
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] H) =
      Algebra.TensorProduct.includeLeft := by
  ext s
  simp [transl]

/-- Translations compose by convolution. -/
lemma transl_comp (g g' : WithConv (H →ₐ[R] S)) :
    (transl (R := R) (H := H) g').comp (transl g) = transl (g * g') := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · have e1 := transl_comp_includeRight (R := R) (H := H) g
    have e2 := transl_comp_includeRight (R := R) (H := H) g'
    have e3 := transl_comp_includeRight (R := R) (H := H) (g * g')
    have eL := transl_comp_includeLeft (R := R) (H := H) g'
    rw [map_comp_comul_eq] at e1 e2 e3
    change ((transl g').restrictScalars R).comp
        (((transl g).restrictScalars R).comp Algebra.TensorProduct.includeRight) =
      ((transl (g * g')).restrictScalars R).comp Algebra.TensorProduct.includeRight
    rw [e1, e3, AlgHom.comp_convMul_distrib, ← AlgHom.comp_assoc, eL, e2,
      AlgHom.comp_convMul_distrib, toConv_ofConv, toConv_ofConv, toConv_ofConv, mul_assoc]

lemma transl_one : transl (R := R) (H := H) (1 : WithConv (H →ₐ[R] S)) = AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · have e := transl_comp_includeRight (R := R) (H := H) (1 : WithConv (H →ₐ[R] S))
    rw [map_comp_comul_eq] at e
    change ((transl (1 : WithConv (H →ₐ[R] S))).restrictScalars R).comp
        Algebra.TensorProduct.includeRight = Algebra.TensorProduct.includeRight
    have h1 : toConv ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] H).comp
        (1 : WithConv (H →ₐ[R] S)).ofConv) = 1 := by
      rw [AlgHom.convOne_def, AlgHom.convOne_def, ofConv_toConv, ← AlgHom.comp_assoc]
      congr 2
    rw [e, h1, one_mul, ofConv_toConv]

/-- The convolution inverse of a point: `g ∘ S`, with `S` the antipode. (Mathlib's group instance
on `WithConv (H →ₐ[R] C)` asks for a bialgebra structure on `C`, which `S` does not have.) -/
noncomputable def convInv (g : WithConv (H →ₐ[R] S)) : WithConv (H →ₐ[R] S) :=
  toConv (g.ofConv.comp (HopfAlgebra.antipodeAlgHom R H))

lemma convInv_mul (g : WithConv (H →ₐ[R] S)) : convInv g * g = 1 := by
  have h : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map g.ofConv g.ofConv) =
      g.ofConv.comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
  trans toConv <| ((Algebra.TensorProduct.lmul' R).comp
      (Algebra.TensorProduct.map g.ofConv g.ofConv)).comp
      ((Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R H) (.id _ _)).comp
        (Bialgebra.comulAlgHom R H))
  · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map g.ofConv g.ofConv),
      ← Algebra.TensorProduct.map_comp]; rfl
  rw [h, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
  change g.ofConv.toLinearMap.comp
      (toConv (HopfAlgebra.antipode R (A := H)) * toConv LinearMap.id).ofConv =
    ofConv (1 : WithConv <| H →ₗ[R] S)
  rw [LinearMap.antipode_mul_id]
  ext
  simp

lemma mul_convInv (g : WithConv (H →ₐ[R] S)) : g * convInv g = 1 := by
  have h : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map g.ofConv g.ofConv) =
      g.ofConv.comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
  trans toConv <| ((Algebra.TensorProduct.lmul' R).comp
      (Algebra.TensorProduct.map g.ofConv g.ofConv)).comp
      ((Algebra.TensorProduct.map (.id _ _) (HopfAlgebra.antipodeAlgHom R H)).comp
        (Bialgebra.comulAlgHom R H))
  · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map g.ofConv g.ofConv),
      ← Algebra.TensorProduct.map_comp]; rfl
  rw [h, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
  change g.ofConv.toLinearMap.comp
      (toConv LinearMap.id * toConv (HopfAlgebra.antipode R (A := H))).ofConv =
    ofConv (1 : WithConv <| H →ₗ[R] S)
  rw [LinearMap.id_mul_antipode]
  ext
  simp

/-- Every translation is bijective: its inverse is translation by the convolution inverse. -/
lemma transl_bijective (g : WithConv (H →ₐ[R] S)) :
    Function.Bijective (transl (R := R) (H := H) g) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨transl (convInv g), fun y => ?_, fun y => ?_⟩
  · have := congrArg (fun φ : S ⊗[R] H →ₐ[S] S ⊗[R] H => φ y)
      (transl_comp (R := R) (H := H) g (convInv g))
    simpa [mul_convInv, transl_one] using this
  · have := congrArg (fun φ : S ⊗[R] H →ₐ[S] S ⊗[R] H => φ y)
      (transl_comp (R := R) (H := H) (convInv g) g)
    simpa [convInv_mul, transl_one] using this

end Translation

/-! ### A torsor with a point is trivial -/

section Point

open WithConv

variable {S : Type u} [CommRing S] [Algebra R S]

/-- The counit of the trivial torsor over `S`: `S ⊗ H → S`, `s ⊗ h ↦ s ε(h)`. -/
noncomputable def counitS : S ⊗[R] H →ₐ[S] S :=
  (Algebra.TensorProduct.rid R S S : S ⊗[R] R →ₐ[S] S).comp
    (Algebra.TensorProduct.map (AlgHom.id S S) (Bialgebra.counitAlgHom R H))

/-- An equivariant `S`-algebra endomorphism of the trivial torsor over `S` is the translation by
the point `counitS ∘ φ ∘ (h ↦ 1 ⊗ h)`. -/
theorem eq_transl_of_equivariant (φ : S ⊗[R] H →ₐ[S] S ⊗[R] H)
    (hφ : (Algebra.TensorProduct.map (φ.restrictScalars R) (AlgHom.id R H)).comp
        ((Coaction.trivial (R := R) (H := H)).baseChange S) =
      ((Coaction.trivial (R := R) (H := H)).baseChange S).comp (φ.restrictScalars R)) :
    φ = transl (toConv (((counitS (R := R) (H := H)).restrictScalars R).comp
        ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight))) := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · change (φ.restrictScalars R).comp Algebra.TensorProduct.includeRight =
      ((transl _).restrictScalars R).comp Algebra.TensorProduct.includeRight
    rw [transl_comp_includeRight]
    ext h
    let Φ : (S ⊗[R] H) ⊗[R] H →ₐ[R] S ⊗[R] H :=
      Algebra.TensorProduct.map ((counitS (R := R) (H := H)).restrictScalars R) (AlgHom.id R H)
    -- `Φ` undoes the base-changed trivial coaction
    have hcounit : ∀ h : H, Algebra.TensorProduct.map (Bialgebra.counitAlgHom R H) (AlgHom.id R H)
        (Bialgebra.comulAlgHom R H h) = (1 : R) ⊗ₜ[R] h := fun h =>
      LinearMap.congr_fun (Coalgebra.rTensor_counit_comp_comul (R := R) (A := H)) h
    have hΦz : ∀ z : H ⊗[R] H, Φ ((Algebra.TensorProduct.assoc R R R S H H).symm ((1 : S) ⊗ₜ[R] z)) =
        Algebra.TensorProduct.map (Algebra.ofId R S) (AlgHom.id R H)
          (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R H) (AlgHom.id R H) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Φ, counitS, Algebra.algebraMap_eq_smul_one]
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    have key1 : ∀ y : S ⊗[R] H, Φ ((Coaction.trivial (R := R) (H := H)).baseChange S y) = y := by
      intro y
      have : Φ.comp ((Coaction.trivial (R := R) (H := H)).baseChange S) = AlgHom.id R _ := by
        apply Algebra.TensorProduct.ext
        · ext s
          simp [Φ, counitS, Coaction.baseChange, Coaction.trivial, Algebra.TensorProduct.one_def]
        · ext h
          simp only [AlgHom.coe_comp, Function.comp_apply, Coaction.baseChange,
            Algebra.TensorProduct.includeRight_apply]
          change Φ ((Algebra.TensorProduct.assoc R R R S H H).symm
            ((1 : S) ⊗ₜ[R] Bialgebra.comulAlgHom R H h)) = _
          rw [hΦz, hcounit]
          simp
      exact congrArg (fun ψ : S ⊗[R] H →ₐ[R] S ⊗[R] H => ψ y) this
    have key2 : ∀ z : H ⊗[R] H,
        Φ (Algebra.TensorProduct.map (φ.restrictScalars R) (AlgHom.id R H)
          ((Algebra.TensorProduct.assoc R R R S H H).symm ((1 : S) ⊗ₜ[R] z))) =
        Algebra.TensorProduct.map (((counitS (R := R) (H := H)).restrictScalars R).comp
          ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight)) (AlgHom.id R H) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Φ]
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    have hbc : (Coaction.trivial (R := R) (H := H)).baseChange S ((1 : S) ⊗ₜ[R] h) =
        (Algebra.TensorProduct.assoc R R R S H H).symm
          ((1 : S) ⊗ₜ[R] Bialgebra.comulAlgHom R H h) := rfl
    have hφh := congrArg (fun ψ : S ⊗[R] H →ₐ[R] (S ⊗[R] H) ⊗[R] H => ψ ((1 : S) ⊗ₜ[R] h)) hφ
    simp only [AlgHom.coe_comp, Function.comp_apply] at hφh
    rw [hbc] at hφh
    calc (φ.restrictScalars R).comp Algebra.TensorProduct.includeRight h
        = Φ ((Coaction.trivial (R := R) (H := H)).baseChange S (φ ((1 : S) ⊗ₜ[R] h))) :=
          (key1 _).symm
      _ = _ := by
          change Φ (((Coaction.trivial (R := R) (H := H)).baseChange S).comp (φ.restrictScalars R)
            ((1 : S) ⊗ₜ[R] h)) = _
          rw [AlgHom.comp_apply, ← hφh, key2]
          rfl

/-- An equivariant endomorphism of the trivial torsor is bijective. -/
theorem bijective_of_equivariant (φ : S ⊗[R] H →ₐ[S] S ⊗[R] H)
    (hφ : (Algebra.TensorProduct.map (φ.restrictScalars R) (AlgHom.id R H)).comp
        ((Coaction.trivial (R := R) (H := H)).baseChange S) =
      ((Coaction.trivial (R := R) (H := H)).baseChange S).comp (φ.restrictScalars R)) :
    Function.Bijective φ := by
  rw [eq_transl_of_equivariant φ hφ]
  exact transl_bijective _

end Point

/-- Base change preserves equivariance of algebra maps. -/
theorem Coaction.baseChange_map_comm {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] {c : Coaction R H A} {d : Coaction R H B} (f : A →ₐ[R] B)
    (hf : (Algebra.TensorProduct.map f (AlgHom.id R H)).comp c.ρ = d.ρ.comp f)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    (Algebra.TensorProduct.map
        ((Algebra.TensorProduct.map (AlgHom.id R' R') f).restrictScalars R) (AlgHom.id R H)).comp
        (c.baseChange R') =
      (d.baseChange R').comp ((Algebra.TensorProduct.map (AlgHom.id R' R') f).restrictScalars R) := by
  have hρ : ∀ a : A, d.ρ (f a) = Algebra.TensorProduct.map f (AlgHom.id R H) (c.ρ a) := fun a =>
    (congrArg (fun φ : A →ₐ[R] B ⊗[R] H => φ a) hf).symm
  apply Algebra.TensorProduct.ext
  · ext x
    simp [baseChange, Algebra.TensorProduct.one_def]
  · ext a
    simp only [baseChange, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]
    rw [hρ a]
    induction c.ρ a using TensorProduct.induction_on with
    | zero => simp
    | tmul b h => simp
    | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]

/-- **A torsor with an `R`-point is trivial.** If `A` carries a torsor structure and an algebra map
`x : A → R` (a point of `Spec A` over `Spec R`), then `a ↦ (x ⊗ id)(ρ a)` is an isomorphism of
algebras with coaction from `A` to the trivial torsor `H`. -/
theorem IsTorsor.nonempty_iso_trivial_of_point {A : Type u} [CommRing A] [Algebra R A]
    {c : Coaction R H A} (hc : IsTorsor c) (x : A →ₐ[R] R) :
    Nonempty (Coaction.Iso c (Coaction.trivial (R := R) (H := H))) := by
  let κ : A ⊗[R] H →ₐ[R] H := (Algebra.TensorProduct.lid R H : R ⊗[R] H →ₐ[R] H).comp
    (Algebra.TensorProduct.map x (AlgHom.id R H))
  let ψ : A →ₐ[R] H := κ.comp c.ρ
  -- `ψ` is equivariant
  let Θ : A ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] H :=
    (Algebra.TensorProduct.lid R (H ⊗[R] H) : R ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] H).comp
      (Algebra.TensorProduct.map x (AlgHom.id R (H ⊗[R] H)))
  have hΘ1 : Θ.comp (Algebra.TensorProduct.map (AlgHom.id R A) (Bialgebra.comulAlgHom R H)) =
      (Bialgebra.comulAlgHom R H).comp κ := by
    apply Algebra.TensorProduct.ext
    · ext a
      simp [Θ, κ, Algebra.TensorProduct.one_def]
    · ext h
      simp [Θ, κ]
  have hΘ2 : Θ.comp (Algebra.TensorProduct.assoc R R R A H H : (A ⊗[R] H) ⊗[R] H →ₐ[R] _) =
      Algebra.TensorProduct.map κ (AlgHom.id R H) := by
    apply Algebra.TensorProduct.ext
    · apply Algebra.TensorProduct.ext
      · ext a
        simp [Θ, κ]
      · ext h
        simp [Θ, κ]
    · ext h
      simp [Θ, κ, Algebra.TensorProduct.one_def]
  have hψ : (Algebra.TensorProduct.map ψ (AlgHom.id R H)).comp c.ρ =
      (Bialgebra.comulAlgHom R H).comp ψ := by
    have hmap : Algebra.TensorProduct.map ψ (AlgHom.id R H) =
        (Algebra.TensorProduct.map κ (AlgHom.id R H)).comp
          (Algebra.TensorProduct.map c.ρ (AlgHom.id R H)) := by
      rw [← Algebra.TensorProduct.map_comp]; rfl
    rw [hmap, ← hΘ2, AlgHom.comp_assoc, AlgHom.comp_assoc, c.coassoc, ← AlgHom.comp_assoc, hΘ1,
      AlgHom.comp_assoc]
  -- `ψ` is bijective, by faithfully flat descent from a trivialising base change
  have hbij : Function.Bijective ψ := by
    obtain ⟨_, R', _, _, hR', e, he⟩ := hc
    have := hR'
    let Ψ : R' ⊗[R] A →ₐ[R'] R' ⊗[R] H := Algebra.TensorProduct.map (AlgHom.id R' R') ψ
    have hΨ := Coaction.baseChange_map_comm (d := Coaction.trivial) ψ hψ R'
    have hinv : ∀ w : (R' ⊗[R] A) ⊗[R] H,
        Algebra.TensorProduct.map (e.symm.toAlgHom.restrictScalars R) (AlgHom.id R H)
          (Algebra.TensorProduct.map (e.toAlgHom.restrictScalars R) (AlgHom.id R H) w) = w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a h => simp
      | add y z hy hz => simp only [map_add, hy, hz]
    have he' : (Algebra.TensorProduct.map (e.symm.toAlgHom.restrictScalars R) (AlgHom.id R H)).comp
        ((Coaction.trivial (R := R) (H := H)).baseChange R') =
        (c.baseChange R').comp (e.symm.toAlgHom.restrictScalars R) := by
      apply AlgHom.ext
      intro y
      have h1 : Algebra.TensorProduct.map (e.toAlgHom.restrictScalars R) (AlgHom.id R H)
          (c.baseChange R' (e.symm y)) = (Coaction.trivial (R := R) (H := H)).baseChange R' y := by
        have := congrArg (fun φ : R' ⊗[R] A →ₐ[R] (R' ⊗[R] H) ⊗[R] H => φ (e.symm y)) he
        simpa using this
      simp only [AlgHom.coe_comp, Function.comp_apply]
      rw [← h1, hinv]
      rfl
    let φ : R' ⊗[R] H →ₐ[R'] R' ⊗[R] H := Ψ.comp e.symm.toAlgHom
    have hφ : (Algebra.TensorProduct.map (φ.restrictScalars R) (AlgHom.id R H)).comp
        ((Coaction.trivial (R := R) (H := H)).baseChange R') =
        ((Coaction.trivial (R := R) (H := H)).baseChange R').comp (φ.restrictScalars R) := by
      have hsplit : φ.restrictScalars R =
          (Ψ.restrictScalars R).comp (e.symm.toAlgHom.restrictScalars R) := rfl
      rw [hsplit, ← AlgHom.comp_id (AlgHom.id R H), Algebra.TensorProduct.map_comp,
        AlgHom.comp_assoc, he', ← AlgHom.comp_assoc, hΨ, AlgHom.comp_assoc]
    have hφbij := bijective_of_equivariant φ hφ
    have hΨbij : Function.Bijective Ψ := by
      have : (Ψ : R' ⊗[R] A → R' ⊗[R] H) = φ ∘ e := by
        funext y; simp [φ]
      rw [this]
      exact hφbij.comp e.bijective
    have hlt : (ψ.toLinearMap.lTensor R' : R' ⊗[R] A → R' ⊗[R] H) = Ψ := by
      funext y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r a => simp [Ψ]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hdesc := (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R R' ψ.toLinearMap).mp
      (by rw [hlt]; exact hΨbij)
    exact hdesc
  refine ⟨⟨AlgEquiv.ofBijective ψ hbij, ?_⟩⟩
  have hcoe : ((AlgEquiv.ofBijective ψ hbij : A ≃ₐ[R] H) : A →ₐ[R] H) = ψ := AlgHom.ext fun _ => rfl
  rw [hcoe]
  exact hψ

end HopfTorsor
