import Definitions.Def_HopfTorsor_Diagonalizable
import P2M.Util
import P2M.Sol.S_HopfTorsor_Diagonalizable_nonempty_iso_trivial_mu

/-- **`μ_q`-torsors over `ℤ` are trivial for odd `q`.** Here `μ_q = Spec ℤ[ℤ/q]`, the group
algebra of `ℤ/q` being `ℤ[x]/(x^q - 1)`; in fppf terms, `H¹(Spec ℤ, μ_q) = 0`. The proof uses only
that finitely generated torsion-free `ℤ`-modules are free (`Pic ℤ = 0`) and that `±1` are their
own odd powers. -/
theorem HopfTorsor.Diagonalizable.nonempty_iso_trivial_mu (q : ℕ) [NeZero q] (hq : Odd q)
    {A : Type} [CommRing A]
    {c : HopfTorsor.Coaction ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod q))) A}
    (hc : HopfTorsor.IsTorsor c) :
    Nonempty (HopfTorsor.CoactionIso c HopfTorsor.Coaction.trivial) := by p2m_exact_reverting @_root_.P2MW.S_HopfTorsor_Diagonalizable_nonempty_iso_trivial_mu.solution
