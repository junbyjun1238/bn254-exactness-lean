import CoreExactness.Prelude

namespace CoreExactness

set_option autoImplicit false

/--
Paper target:
`Bounded deferred-quotient exactness`.

If `L`, `D`, and `q` are represented by canonical integer lifts, and
`D + p * q` stays inside the canonical interval `[0, r)`, then an equality
`L = D + p * q` in `ZMod r` should lift to an exact equality in `Int`.

For the current checkpoint we keep the theorem boundary fixed and leave the
proof as a later step.
-/
theorem boundedDeferredQuotientExactness
  (r p b : Nat)
  (L D q : ZMod r)
  (cL cD : CanonicalLift r)
  (qLift : Int)
  (hL : Represents r L cL)
  (hD : Represents r D cD)
  (_hqRange : InQuotientRange (Int.ofNat b) qLift)
  (hqRep : (qLift : ZMod r) = q)
  (hNoWrap : And (0 <= cD.lift + Int.ofNat p * qLift) (cD.lift + Int.ofNat p * qLift < Int.ofNat r))
  (hEq : L = D + (p : ZMod r) * q) :
  cL.lift = cD.lift + Int.ofNat p * qLift := by
  have hCastEq :
      ((cL.lift : Int) : ZMod r) = (((cD.lift + Int.ofNat p * qLift : Int)) : ZMod r) := by
    calc
      ((cL.lift : Int) : ZMod r) = L := hL
      _ = D + (p : ZMod r) * q := hEq
      _ = (cD.lift : ZMod r) + (p : ZMod r) * (qLift : ZMod r) := by
        rw [← hD, ← hqRep]
      _ = (((cD.lift + Int.ofNat p * qLift : Int)) : ZMod r) := by
        simp
  have hModEq :
      cL.lift % Int.ofNat r = (cD.lift + Int.ofNat p * qLift) % Int.ofNat r :=
    (ZMod.intCast_eq_intCast_iff' cL.lift (cD.lift + Int.ofNat p * qLift) r).mp hCastEq
  rw [Int.emod_eq_of_lt cL.inRange.1 cL.inRange.2, Int.emod_eq_of_lt hNoWrap.1 hNoWrap.2] at hModEq
  exact hModEq

end CoreExactness
