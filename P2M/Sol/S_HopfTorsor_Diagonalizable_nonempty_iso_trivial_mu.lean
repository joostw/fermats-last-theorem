import Definitions.Def_HopfTorsor_Diagonalizable
import P2M.Util
namespace P2MW.S_HopfTorsor_Diagonalizable_nonempty_iso_trivial_mu

set_option autoImplicit false

theorem solution (q : ℕ) [NeZero q] (hq : Odd q)
    {A : Type} [CommRing A]
    {c : HopfTorsor.Coaction ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod q))) A}
    (hc : HopfTorsor.IsTorsor c) :
    Nonempty (HopfTorsor.CoactionIso c HopfTorsor.Coaction.trivial) :=
  -- `μ_q` is the diagonalizable group of `ℤ/q`, a group of odd order `q`.
  HopfTorsor.Diagonalizable.nonempty_iso_trivial_int (by simpa using hq) hc

end P2MW.S_HopfTorsor_Diagonalizable_nonempty_iso_trivial_mu
