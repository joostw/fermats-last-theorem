import Definitions.Def_HopfTorsor_Descent
import P2M.Util
import P2M.Sol.S_HopfTorsor_IsTorsor_nonempty_iso_trivial_int

/-- **Torsors over `ℤ` under a finite étale group are trivial.** If the Hopf algebra `H` is
finite and formally unramified over `ℤ`, every `H`-torsor over `ℤ` is isomorphic to the trivial
one; in fppf terms, `H¹(Spec ℤ, Spec H) = 0`. The proof uses Minkowski's theorem (in the form
`Algebra.FormallyUnramified.nonempty_ringHom_int`) to find a `ℤ`-point. -/
theorem HopfTorsor.IsTorsor.nonempty_iso_trivial_int
    {H : Type} [CommRing H] [HopfAlgebra ℤ H] [Module.Finite ℤ H]
    [Algebra.FormallyUnramified ℤ H]
    {A : Type} [CommRing A] {c : HopfTorsor.Coaction ℤ H A} (hc : HopfTorsor.IsTorsor c) :
    Nonempty (HopfTorsor.CoactionIso c HopfTorsor.Coaction.trivial) := by p2m_exact_reverting @_root_.P2MW.S_HopfTorsor_IsTorsor_nonempty_iso_trivial_int.solution
