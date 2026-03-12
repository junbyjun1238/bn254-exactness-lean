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
  (hqRange : InQuotientRange (Int.ofNat b) qLift)
  (hqRep : (qLift : ZMod r) = q)
  (hNoWrap : And (0 <= cD.lift + Int.ofNat p * qLift) (cD.lift + Int.ofNat p * qLift < Int.ofNat r))
  (hEq : L = D + (p : ZMod r) * q) :
  cL.lift = cD.lift + Int.ofNat p * qLift := by
  sorry

end CoreExactness
