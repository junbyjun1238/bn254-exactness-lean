import CoreExactness.RowwiseExactness

namespace CoreExactness

set_option autoImplicit false

/--
From an exact integer identity `L = D + p * q` with a canonical residue
representative `D ∈ [0, p)`, recover the Euclidean remainder and quotient.
-/
theorem euclideanQuotientRemainderOfExactness
  (p : Nat)
  (hp : 0 < p)
  (l d q : Int)
  (hResidue : InCanonicalResidueRange (Int.ofNat p) d)
  (hEq : l = d + Int.ofNat p * q) :
  d = l % Int.ofNat p ∧ q = l / Int.ofNat p := by
  have hp0 : Int.ofNat p ≠ 0 := by
    exact Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hp)
  have hMod :
      d = l % Int.ofNat p := by
    calc
      d = d % Int.ofNat p := by
        symm
        exact Int.emod_eq_of_lt hResidue.1 hResidue.2
      _ = (d + Int.ofNat p * q) % Int.ofNat p := by
        symm
        exact Int.add_mul_emod_self_left d (Int.ofNat p) q
      _ = l % Int.ofNat p := by
        simp [hEq]
  have hDivZero : d / Int.ofNat p = 0 := by
    exact Int.ediv_eq_zero_of_lt hResidue.1 hResidue.2
  have hDiv :
      q = l / Int.ofNat p := by
    calc
      q = 0 + q := by simp
      _ = d / Int.ofNat p + q := by rw [hDivZero]
      _ = (d + Int.ofNat p * q) / Int.ofNat p := by
        symm
        exact Int.add_mul_ediv_left d q hp0
      _ = l / Int.ofNat p := by
        simp [hEq]
  exact ⟨hMod, hDiv⟩

/--
Manuscript-facing Euclidean corollary: once the rowwise exactness theorem has
produced an exact integer identity and the designated residue lift is canonical
in `[0, p)`, the residue is `L mod p` and the quotient is `L / p`.
-/
theorem euclideanQuotientRemainderFromCanonicalLifts
  (r p : Nat)
  (hp : 0 < p)
  (L D q : ZMod r)
  (cL cD : CanonicalLift r)
  (qLift : Int)
  (hL : Represents r L cL)
  (hD : Represents r D cD)
  (hResidue : InCanonicalResidueRange (Int.ofNat p) cD.lift)
  (hqRep : (qLift : ZMod r) = q)
  (hNoWrap :
    And (0 <= cD.lift + Int.ofNat p * qLift)
        (cD.lift + Int.ofNat p * qLift < Int.ofNat r))
  (hEq : L = D + (p : ZMod r) * q) :
  cD.lift = cL.lift % Int.ofNat p ∧ qLift = cL.lift / Int.ofNat p := by
  have hExact :
      cL.lift = cD.lift + Int.ofNat p * qLift := by
    exact coreRowwiseExactnessFromCanonicalLifts r p L D q cL cD qLift hL hD hqRep hNoWrap hEq
  exact euclideanQuotientRemainderOfExactness p hp cL.lift cD.lift qLift hResidue hExact

end CoreExactness
