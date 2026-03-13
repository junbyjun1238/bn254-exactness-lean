import CoreExactness.RangeExclusion

namespace CoreExactness

set_option autoImplicit false
set_option linter.style.nativeDecide false
set_option linter.style.whitespace false

/-- BN254 scalar-field modulus used as the outer field modulus in the paper context. -/
def bn254ScalarModulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- The 31-bit Mersenne prime used as the inner field modulus in the paper context. -/
def m31Prime : Nat := 2 ^ 31 - 1

/-- Unsigned quotient bound corresponding to the 31-bit class used in the note. -/
def quotientBound31 : Nat := 2 ^ 31

/-- Unsigned quotient bound corresponding to the 66-bit class used in the note. -/
def quotientBound66 : Nat := 2 ^ 66

/-- Basic size sanity check for the concrete paper constants. -/
theorem m31Prime_lt_bn254ScalarModulus : m31Prime < bn254ScalarModulus := by
  native_decide

/-- Concrete arithmetic headroom for the 31-bit quotient class. -/
theorem m31Prime_mul_quotientBound31_lt_bn254ScalarModulus :
  m31Prime * quotientBound31 < bn254ScalarModulus := by
  native_decide

/-- Concrete arithmetic headroom for the 66-bit quotient class. -/
theorem m31Prime_mul_quotientBound66_lt_bn254ScalarModulus :
  m31Prime * quotientBound66 < bn254ScalarModulus := by
  native_decide

/--
BN254/M31 specialization shell for the 31-bit quotient class.

This theorem is still conditional on primality of the outer modulus, matching
what `quotientRangeExcludesNegInv` itself requires. The purpose of this file is
not to prove primality of the BN254 scalar modulus inside Lean, but to pin the
paper constants and their arithmetic headroom in one concrete place.
-/
theorem bn254M31QuotientBound31ExcludesNegInv
  [Fact bn254ScalarModulus.Prime]
  (qLift : Int)
  (hRange : InQuotientRange (Int.ofNat quotientBound31) qLift) :
  (qLift : ZMod bn254ScalarModulus) ≠ -((m31Prime : ZMod bn254ScalarModulus)⁻¹) := by
  have hp : 0 < m31Prime := by
    native_decide
  have hpr : m31Prime < bn254ScalarModulus := m31Prime_lt_bn254ScalarModulus
  have hHeadroom : m31Prime * quotientBound31 < bn254ScalarModulus :=
    m31Prime_mul_quotientBound31_lt_bn254ScalarModulus
  exact quotientRangeExcludesNegInv
    bn254ScalarModulus m31Prime quotientBound31 qLift hp hpr hRange hHeadroom

/-- BN254/M31 specialization shell for the 66-bit quotient class. -/
theorem bn254M31QuotientBound66ExcludesNegInv
  [Fact bn254ScalarModulus.Prime]
  (qLift : Int)
  (hRange : InQuotientRange (Int.ofNat quotientBound66) qLift) :
  (qLift : ZMod bn254ScalarModulus) ≠ -((m31Prime : ZMod bn254ScalarModulus)⁻¹) := by
  have hp : 0 < m31Prime := by
    native_decide
  have hpr : m31Prime < bn254ScalarModulus := m31Prime_lt_bn254ScalarModulus
  have hHeadroom : m31Prime * quotientBound66 < bn254ScalarModulus :=
    m31Prime_mul_quotientBound66_lt_bn254ScalarModulus
  exact quotientRangeExcludesNegInv
    bn254ScalarModulus m31Prime quotientBound66 qLift hp hpr hRange hHeadroom

end CoreExactness
