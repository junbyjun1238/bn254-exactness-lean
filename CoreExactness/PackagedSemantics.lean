import CoreExactness.EuclideanSemantics
import CoreExactness.RangeExclusion

namespace CoreExactness

set_option autoImplicit false

/--
A single manuscript-facing package theorem: under the bounded unsigned quotient
range, explicit headroom, canonical residue range, and a satisfied deferred-
quotient row equality, the specific vacuous witness class `-p^{-1}` is excluded
and the intended Euclidean quotient/remainder semantics are recovered.
-/
theorem boundedRepairExcludesNegInvAndRecoversEuclideanSemantics
  (r p b : Nat) [Fact r.Prime]
  (L D q : ZMod r)
  (cL cD : CanonicalLift r)
  (qLift : Int)
  (hp : 0 < p)
  (hpr : p < r)
  (hRange : InQuotientRange (Int.ofNat b) qLift)
  (hHeadroom : p * b < r)
  (hL : Represents r L cL)
  (hD : Represents r D cD)
  (hResidue : InCanonicalResidueRange (Int.ofNat p) cD.lift)
  (hqRep : (qLift : ZMod r) = q)
  (hNoWrap :
    And (0 <= cD.lift + Int.ofNat p * qLift)
        (cD.lift + Int.ofNat p * qLift < Int.ofNat r))
  (hEq : L = D + (p : ZMod r) * q) :
  ((qLift : ZMod r) ≠ -((p : ZMod r)⁻¹)) /\
    (cD.lift = cL.lift % Int.ofNat p /\ qLift = cL.lift / Int.ofNat p) := by
  constructor
  case left =>
    exact quotientRangeExcludesNegInv r p b qLift hp hpr hRange hHeadroom
  case right =>
    exact euclideanQuotientRemainderFromCanonicalLifts
      r p hp L D q cL cD qLift hL hD hResidue hqRep hNoWrap hEq

end CoreExactness