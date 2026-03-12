import CoreExactness.Prelude

namespace CoreExactness

set_option autoImplicit false

/--
Paper target:
`Polynomial-level vacuity under unbounded quotient witnesses`.

This is the highest-risk formalization component. The eventual theorem should
show that, after interpolating the rowwise quotient values chosen from the
vacuity construction, the remainder polynomial vanishes on the row domain and
is divisible by the row-domain vanishing polynomial.

For Day 1 we only fix the theorem boundary as a theorem skeleton.
-/
def PolynomialLevelVacuityStatement
  {F : Type} [Field F]
  (p : F) (_hp : Ne p 0) :
  Prop := True

theorem polynomialLevelVacuity
  {F : Type} [Field F]
  (p : F) (hp : Ne p 0) :
  PolynomialLevelVacuityStatement p hp := by
  sorry

end CoreExactness
