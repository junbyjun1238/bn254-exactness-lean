import CoreExactness.BoundedExactness

namespace CoreExactness

set_option autoImplicit false

/--
Paper target:
`Core rowwise exactness from canonical lifts`.

This packages the bounded exactness lemma into the rowwise theorem form used by
the manuscript. The designated-residue conclusion is kept at the theorem
boundary, while backend-, wiring-, and appendix-specific premises remain out of
scope for this Lean package.
-/
theorem coreRowwiseExactnessFromCanonicalLifts
  (r p B : ℕ)
  (L D q : ZMod r)
  (cL cD : CanonicalLift r)
  (qLift : ℤ)
  (hL : Represents r L cL)
  (hD : Represents r D cD)
  (hqRange : InQuotientRange B qLift)
  (hqRep : (qLift : ZMod r) = q)
  (hNoWrap : 0 ≤ cD.lift + (p : ℤ) * qLift ∧ cD.lift + (p : ℤ) * qLift < r)
  (hEq : L = D + (p : ZMod r) * q) :
  cL.lift = cD.lift + (p : ℤ) * qLift := by
  sorry

end CoreExactness
