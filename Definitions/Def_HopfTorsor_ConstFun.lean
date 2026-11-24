import Definitions.Def_HopfTorsor_Descent
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Unramified.Pi

set_option autoImplicit false

/-!
# The constant group scheme

For a finite group `G`, the constant group scheme `G` over `R` is `Spec` of the ring of
functions `G → R`, with comultiplication `Δ f (g, h) = f (g * h)`, counit `f ↦ f 1` and antipode
`f ↦ f ∘ inv`. On the basis of indicator functions `δ k`,
`Δ (δ k) = ∑ g, δ g ⊗ δ (g⁻¹ * k)`.

`ConstFun R G` is a type synonym for `G → R`: Mathlib's instance on `G → R` is the product
coalgebra (each `δ g` grouplike), which is the dual structure and must not be confused with this
one.

## Main results

* `HopfTorsor.ConstFun.instHopfAlgebra`: the Hopf algebra of the constant group scheme.
* `HopfTorsor.ConstFun.isTorsor_trivial`: the trivial torsor under it (for `G` nonempty).
* `HopfTorsor.ConstFun.nonempty_iso_trivial_int_of_minkowski`: given Minkowski's theorem, every
  torsor over `ℤ` under a finite constant group is trivial (unconditionally:
  `HopfTorsor.ConstFun.nonempty_iso_trivial_int` in `Theorems/`). For `G = ℤ/q` this is
  `H¹_fppf(Spec ℤ, ℤ/q) = 0`, the half of Mazur's cohomology input that rests on Minkowski.
-/

open TensorProduct

namespace HopfTorsor

universe u

/-- Functions `G → R`, as the coordinate ring of the constant group scheme `G` over `R`. -/
def ConstFun (R : Type u) (G : Type u) : Type u := G → R

namespace ConstFun

variable (R : Type u) [CommRing R] (G : Type u)

instance : CommRing (ConstFun R G) := inferInstanceAs (CommRing (G → R))
instance : Algebra R (ConstFun R G) := inferInstanceAs (Algebra R (G → R))

section Eval

variable {R G}

@[simp] lemma constFun_sum_apply {ι : Type*} (s : Finset ι) (F : ι → ConstFun R G) (x : G) :
    (∑ i ∈ s, F i) x = ∑ i ∈ s, F i x := Finset.sum_apply x s F
@[simp] lemma constFun_smul_apply (r : R) (f : ConstFun R G) (x : G) : (r • f) x = r * f x := rfl
@[simp] lemma constFun_mul_apply (f f' : ConstFun R G) (x : G) : (f * f') x = f x * f' x := rfl
@[simp] lemma constFun_one_apply (x : G) : (1 : ConstFun R G) x = 1 := rfl
@[simp] lemma constFun_zero_apply (x : G) : (0 : ConstFun R G) x = 0 := rfl
@[simp] lemma constFun_algebraMap_apply (r : R) (x : G) : algebraMap R (ConstFun R G) r x = r := rfl

end Eval

variable [Group G] [Fintype G] [DecidableEq G]

/-- The indicator function of `k`. -/
def δ (k : G) : ConstFun R G := Pi.single k 1

/-- `f ↦ ((h, g) ↦ f (g * h))`, with the pair curried as `G → (G → R)`. -/
def mulPull : ConstFun R G →ₐ[R] (G → ConstFun R G) where
  toFun f h g := f (g * h)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- `(G → R) ⊗ (G → R) ≃ G → (G → R)`, `x ⊗ y ↦ (i ↦ y i • x)`. -/
noncomputable def constTensorEquiv : ConstFun R G ⊗[R] ConstFun R G ≃ₐ[R] (G → ConstFun R G) :=
  Algebra.TensorProduct.piScalarRight R R (ConstFun R G) G

/-- Comultiplication, `Δ f (g, h) = f (g * h)`. -/
noncomputable def comulAH : ConstFun R G →ₐ[R] ConstFun R G ⊗[R] ConstFun R G :=
  (constTensorEquiv R G).symm.toAlgHom.comp (mulPull R G)

/-- Counit, evaluation at `1`. -/
def counitAH : ConstFun R G →ₐ[R] R := Pi.evalAlgHom R (fun _ : G => R) 1

variable {R G}

omit [Group G] [Fintype G] in
lemma δ_apply_eq_ite (k g : G) : δ R G k g = if g = k then 1 else 0 := Pi.single_apply k 1 g

omit [Group G] in
lemma eq_sum_δ (f : ConstFun R G) : f = ∑ g, f g • δ R G g := by
  funext x
  simp only [constFun_sum_apply, constFun_smul_apply, δ_apply_eq_ite, mul_ite, mul_one, mul_zero]
  exact ((Finset.sum_ite_eq Finset.univ x (fun i : G => (f i : R))).trans
    (if_pos (Finset.mem_univ x))).symm

omit [Fintype G] in
lemma counitAH_δ (k : G) : counitAH R G (δ R G k) = if 1 = k then 1 else 0 := δ_apply_eq_ite k 1

lemma comulAH_δ (k : G) : comulAH R G (δ R G k) = ∑ g, δ R G g ⊗ₜ[R] δ R G (g⁻¹ * k) := by
  apply (constTensorEquiv R G).injective
  rw [comulAH, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, map_sum]
  funext i x
  rw [Finset.sum_apply, constFun_sum_apply]
  change δ R G k (x * i) = ∑ g, (δ R G (g⁻¹ * k) i • δ R G g) x
  simp only [constFun_smul_apply, δ_apply_eq_ite, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  by_cases h : x * i = k
  · rw [if_pos h, if_pos (by rw [← h, inv_mul_cancel_left])]
  · rw [if_neg h, if_neg (by rintro rfl; exact h (mul_inv_cancel_left x k))]

omit [Group G] in
lemma algHom_ext_δ {B : Type*} [Semiring B] [Algebra R B] {φ ψ : ConstFun R G →ₐ[R] B}
    (h : ∀ k, φ (δ R G k) = ψ (δ R G k)) : φ = ψ := by
  ext f
  rw [eq_sum_δ f]
  simp only [map_sum, map_smul, h]

lemma coassoc :
    (Algebra.TensorProduct.assoc R R R (ConstFun R G) (ConstFun R G) (ConstFun R G)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAH R G) (.id R (ConstFun R G))).comp (comulAH R G))
      = (Algebra.TensorProduct.map (.id R (ConstFun R G)) (comulAH R G)).comp (comulAH R G) := by
  apply algHom_ext_δ
  intro k
  simp only [AlgHom.comp_apply, comulAH_δ, map_sum, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, TensorProduct.sum_tmul, TensorProduct.tmul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine (Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun b => ?_)).symm
  simp [mul_assoc]

lemma rTensor_counitAH :
    (Algebra.TensorProduct.map (counitAH R G) (.id R (ConstFun R G))).comp (comulAH R G)
      = (Algebra.TensorProduct.lid R (ConstFun R G)).symm := by
  apply algHom_ext_δ
  intro k
  simp only [AlgHom.comp_apply, comulAH_δ, map_sum, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, counitAH_δ, 
]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro g _ hg
    rw [if_neg (Ne.symm hg), TensorProduct.zero_tmul]
  · simp

lemma lTensor_counitAH :
    (Algebra.TensorProduct.map (.id R (ConstFun R G)) (counitAH R G)).comp (comulAH R G)
      = (Algebra.TensorProduct.rid R R (ConstFun R G)).symm := by
  apply algHom_ext_δ
  intro k
  simp only [AlgHom.comp_apply, comulAH_δ, map_sum, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, counitAH_δ, 
]
  rw [Finset.sum_eq_single k]
  · simp
  · intro g _ hg
    rw [if_neg (fun h => hg (by rw [eq_comm, inv_mul_eq_one] at h; exact h)),
      TensorProduct.tmul_zero]
  · simp

noncomputable instance instBialgebra : Bialgebra R (ConstFun R G) :=
  Bialgebra.ofAlgHom (comulAH R G) (counitAH R G) coassoc rTensor_counitAH lTensor_counitAH

lemma comul_eq_comulAH (f : ConstFun R G) : Coalgebra.comul (R := R) f = comulAH R G f := rfl

lemma counit_eq_counitAH (f : ConstFun R G) : Coalgebra.counit (R := R) f = counitAH R G f := rfl

/-- Antipode, `f ↦ f ∘ inv`. -/
def antipodeL : ConstFun R G →ₗ[R] ConstFun R G := LinearMap.funLeft R R (fun g : G => g⁻¹)

omit [Fintype G] in
lemma antipodeL_δ (k : G) : antipodeL (δ R G k) = δ R G k⁻¹ := by
  funext x
  change δ R G k x⁻¹ = δ R G k⁻¹ x
  simp only [δ_apply_eq_ite, inv_eq_iff_eq_inv]

omit [Group G] in
lemma linearMap_ext_δ {B : Type*} [AddCommMonoid B] [Module R B] {φ ψ : ConstFun R G →ₗ[R] B}
    (h : ∀ k, φ (δ R G k) = ψ (δ R G k)) : φ = ψ := by
  ext f
  rw [eq_sum_δ f]
  simp only [map_sum, map_smul, h]

omit [Group G] [Fintype G] in
lemma δ_mul_δ (a b : G) : δ R G a * δ R G b = if a = b then δ R G a else 0 := by
  funext x
  rw [constFun_mul_apply]
  split_ifs with hab
  · subst hab
    rw [δ_apply_eq_ite]
    split_ifs <;> simp
  · rw [constFun_zero_apply, δ_apply_eq_ite, δ_apply_eq_ite]
    split_ifs with h1 h2 <;> simp_all

omit [Group G] in
lemma sum_δ : ∑ g, δ R G g = 1 := by
  funext x
  simp [δ_apply_eq_ite]

noncomputable instance instHopfAlgebra : HopfAlgebra R (ConstFun R G) where
  antipode := antipodeL
  mul_antipode_rTensor_comul := by
    apply linearMap_ext_δ
    intro k
    simp only [LinearMap.comp_apply, comul_eq_comulAH, comulAH_δ, map_sum, LinearMap.rTensor_tmul,
      antipodeL_δ, LinearMap.mul'_apply, δ_mul_δ, counit_eq_counitAH, counitAH_δ, Algebra.linearMap_apply]
    by_cases hk : k = 1
    · subst hk
      simp only [mul_one, if_true]
      rw [map_one, ← sum_δ]
      exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)
    · rw [if_neg (Ne.symm hk), map_zero]
      refine Finset.sum_eq_zero fun g _ => ?_
      rw [if_neg]
      intro h
      exact hk (by simpa using congrArg (g * ·) h |>.symm)
  mul_antipode_lTensor_comul := by
    apply linearMap_ext_δ
    intro k
    simp only [LinearMap.comp_apply, comul_eq_comulAH, comulAH_δ, map_sum, LinearMap.lTensor_tmul,
      antipodeL_δ, LinearMap.mul'_apply, δ_mul_δ, counit_eq_counitAH, counitAH_δ, Algebra.linearMap_apply]
    by_cases hk : k = 1
    · subst hk
      simp only [mul_one, inv_inv, if_true]
      rw [map_one, ← sum_δ]
    · rw [if_neg (Ne.symm hk), map_zero]
      refine Finset.sum_eq_zero fun g _ => ?_
      rw [if_neg]
      intro h
      exact hk (by simpa using h)

instance : Module.Free R (ConstFun R G) := inferInstanceAs (Module.Free R (G → R))
instance : Module.Finite R (ConstFun R G) := inferInstanceAs (Module.Finite R (G → R))
instance : Algebra.FormallyUnramified R (ConstFun R G) :=
  inferInstanceAs (Algebra.FormallyUnramified R (G → R))
instance instFiniteInt (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    Module.Finite ℤ (ConstFun ℤ G) := inferInstanceAs (Module.Finite ℤ (G → ℤ))
instance [Nontrivial R] : Nontrivial (ConstFun R G) := inferInstanceAs (Nontrivial (G → R))
instance [Nontrivial R] : Module.FaithfullyFlat R (ConstFun R G) := inferInstance

theorem isTorsor_trivial [Nontrivial R] :
    IsTorsor (Coaction.trivial (R := R) (H := ConstFun R G)) :=
  Coaction.trivial_isTorsor

/-- **Torsors over `ℤ` under a finite constant group are trivial**, given Minkowski's theorem.
For `G = Multiplicative (ZMod q)` this is `H¹_fppf(Spec ℤ, ℤ/q) = 0`. -/
theorem nonempty_iso_trivial_int_of_minkowski (hM : MinkowskiPoint) (G : Type) [Group G]
    [Fintype G] [DecidableEq G] {A : Type} [CommRing A] {c : Coaction ℤ (ConstFun ℤ G) A} (hc : IsTorsor c) :
    Nonempty (CoactionIso c Coaction.trivial) :=
  IsTorsor.nonempty_iso_trivial_int_of_minkowski hM hc

end ConstFun

end HopfTorsor
