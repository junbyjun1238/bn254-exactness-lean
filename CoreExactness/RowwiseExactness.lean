import CoreExactness.BoundedExactness

namespace CoreExactness

set_option autoImplicit false

/--
Paper target:
`Core rowwise exactness from canonical lifts`.

This packages the bounded exactness lemma into the rowwise theorem form used by
the manuscript, while leaving designated-residue corollaries and backend-level
premises outside this Lean package.
-/
theorem coreRowwiseExactnessFromCanonicalLifts
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
  simpa using
    boundedDeferredQuotientExactness r p b L D q cL cD qLift hL hD _hqRange hqRep hNoWrap hEq

end CoreExactness
