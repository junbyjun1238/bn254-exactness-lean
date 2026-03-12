import CoreExactness.Prelude

namespace CoreExactness

set_option autoImplicit false

/--
If a natural quotient witness `q` is bounded by `q < b`, the modulus headroom
`p * b < r` holds, and `p` is a positive residue modulo the prime field
`ZMod r`, then `q` cannot equal the vacuous `-p^{-1}` witness class.
-/
theorem natQuotientRangeExcludesNegInv
  (r p b q : Nat) [Fact r.Prime]
  (hp : 0 < p)
  (hpr : p < r)
  (hq : q < b)
  (hHeadroom : p * b < r) :
  (q : ZMod r) ≠ -((p : ZMod r)⁻¹) := by
  have hpz : (p : ZMod r) ≠ 0 := by
    intro hpzero
    have hdiv : r ∣ p := (ZMod.natCast_eq_zero_iff p r).mp hpzero
    exact Nat.not_lt_of_ge (Nat.le_of_dvd hp hdiv) hpr
  intro hEq
  have hMul : ((p * q : Nat) : ZMod r) = (-1 : ZMod r) := by
    calc
      ((p * q : Nat) : ZMod r) = (p : ZMod r) * (q : ZMod r) := by simp
      _ = (p : ZMod r) * (-((p : ZMod r)⁻¹)) := by rw [hEq]
      _ = -((p : ZMod r) * (p : ZMod r)⁻¹) := by rw [mul_neg]
      _ = -1 := by simp [hpz]
  have hZero : ((p * q + 1 : Nat) : ZMod r) = 0 := by
    calc
      ((p * q + 1 : Nat) : ZMod r) = ((p * q : Nat) : ZMod r) + 1 := by simp
      _ = (-1 : ZMod r) + 1 := by rw [hMul]
      _ = 0 := by ring
  have hLe_pb : p * q + 1 ≤ p * b := by
    have hp1 : 1 ≤ p := Nat.succ_le_of_lt hp
    have h1 : p * q + 1 ≤ p * q + p := Nat.add_le_add_left hp1 (p * q)
    have h2 : p * q + p = p * (q + 1) := by ring
    have h3 : q + 1 ≤ b := Nat.succ_le_of_lt hq
    have h4 : p * (q + 1) ≤ p * b := Nat.mul_le_mul_left p h3
    exact le_trans (by simpa [h2] using h1) h4
  have hLt : p * q + 1 < r := lt_of_le_of_lt hLe_pb hHeadroom
  have hNonzero : ((p * q + 1 : Nat) : ZMod r) ≠ 0 := by
    intro hz
    have hdiv : r ∣ (p * q + 1) := (ZMod.natCast_eq_zero_iff (p * q + 1) r).mp hz
    exact Nat.not_lt_of_ge (Nat.le_of_dvd (Nat.succ_pos _) hdiv) hLt
  exact hNonzero hZero

/--
Integer-lift form of the same exclusion theorem, matching the unsigned
`InQuotientRange` predicate used in the exactness package.
-/
theorem quotientRangeExcludesNegInv
  (r p b : Nat) [Fact r.Prime]
  (qLift : Int)
  (hp : 0 < p)
  (hpr : p < r)
  (hRange : InQuotientRange (Int.ofNat b) qLift)
  (hHeadroom : p * b < r) :
  (qLift : ZMod r) ≠ -((p : ZMod r)⁻¹) := by
  let q : Nat := Int.toNat qLift
  have hqEq : qLift = Int.ofNat q := by
    exact (Int.toNat_of_nonneg hRange.1).symm
  have hq : q < b := by
    have hqInt' : Int.ofNat qLift.toNat < Int.ofNat b := by
      have hcast : Int.ofNat qLift.toNat = qLift := Int.toNat_of_nonneg hRange.1
      rw [hcast]
      exact hRange.2
    have hqInt : Int.ofNat q < Int.ofNat b := by
      simpa [q] using hqInt'
    exact Int.ofNat_lt.mp hqInt
  have hNat :
      (q : ZMod r) ≠ -((p : ZMod r)⁻¹) :=
    natQuotientRangeExcludesNegInv r p b q hp hpr hq hHeadroom
  have hqCast : (qLift : ZMod r) = (q : ZMod r) := by
    rw [hqEq]
    simp
  intro hEq
  apply hNat
  calc
    (q : ZMod r) = (qLift : ZMod r) := hqCast.symm
    _ = -((p : ZMod r)⁻¹) := hEq

end CoreExactness
