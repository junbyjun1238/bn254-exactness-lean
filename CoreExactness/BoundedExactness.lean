import CoreExactness.Prelude

namespace CoreExactness

set_option autoImplicit false

/--
Paper target:
`Bounded deferred-quotient exactness`.

If `L`, `D`, and `q` are represented by canonical integer lifts, and
`D + p * q` is known to stay in `[0, r)`, then an equality
`L = D + p*q` in `ZMod r` upgrades to an exact equality in `ℤ`.
-/
theorem boundedDeferredQuotientExactness
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
