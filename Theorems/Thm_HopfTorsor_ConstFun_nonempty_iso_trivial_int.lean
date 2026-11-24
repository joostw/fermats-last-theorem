import Definitions.Def_HopfTorsor_ConstFun
import P2M.Util
import P2M.Sol.S_HopfTorsor_ConstFun_nonempty_iso_trivial_int

/-- **Torsors over `ℤ` under a finite constant group are trivial.** For `G = ℤ/q` this is
`H¹_fppf(Spec ℤ, ℤ/q) = 0`: by Minkowski, `ℚ` has no nontrivial everywhere unramified
`ℤ/q`-extension. -/
theorem HopfTorsor.ConstFun.nonempty_iso_trivial_int (G : Type) [Group G] [Fintype G]
    [DecidableEq G] {A : Type} [CommRing A]
    {c : HopfTorsor.Coaction ℤ (HopfTorsor.ConstFun ℤ G) A} (hc : HopfTorsor.IsTorsor c) :
    Nonempty (HopfTorsor.CoactionIso c HopfTorsor.Coaction.trivial) := by p2m_exact_reverting @_root_.P2MW.S_HopfTorsor_ConstFun_nonempty_iso_trivial_int.solution
