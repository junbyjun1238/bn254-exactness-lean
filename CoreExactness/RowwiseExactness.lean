import CoreExactness.BoundedExactness

namespace CoreExactness

set_option autoImplicit false

/--
Paper target:
`Core rowwise exactness from canonical lifts`.

This packages the bounded exactness lemma into the manuscript-facing theorem
shape: canonical lifts for `L` and `D`, a chosen integer lift for the quotient,
a no-wrap bound for `D + p * q`, and a satisfied row equality in `ZMod r`.
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
  (hNoWrap :
    And (0 <= cD.lift + Int.ofNat p * qLift)
        (cD.lift + Int.ofNat p * qLift < Int.ofNat r))
  (hEq : L = D + (p : ZMod r) * q) :
  cL.lift = cD.lift + Int.ofNat p * qLift := by
  have hCast :
      ((cL.lift : Int) : ZMod r) =
        (((cD.lift + Int.ofNat p * qLift : Int)) : ZMod r) := by
    calc
      ((cL.lift : Int) : ZMod r) = L := hL
      _ = D + (p : ZMod r) * q := hEq
      _ = (cD.lift : ZMod r) + (p : ZMod r) * (qLift : ZMod r) := by
        rw [show D = (cD.lift : ZMod r) from hD.symm, show q = (qLift : ZMod r) from hqRep.symm]
      _ = (((cD.lift + Int.ofNat p * qLift : Int)) : ZMod r) := by
        simp
  exact boundedDeferredQuotientExactness r p cL cD qLift hCast hNoWrap

end CoreExactness
