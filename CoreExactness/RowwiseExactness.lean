import CoreExactness.BoundedExactness

namespace CoreExactness

set_option autoImplicit false

/--
Minimal rowwise exactness packaging:
a canonical lift for `L`, an arbitrary integer representative for `D`, a chosen
integer lift for the quotient, a no-wrap bound for `dLift + p * q`, and a
satisfied row equality in `ZMod r` imply exact integer equality.
-/
theorem coreRowwiseExactnessFromRepresentativeD
  (r p : Nat)
  (L D q : ZMod r)
  (cL : CanonicalLift r)
  (dLift qLift : Int)
  (hL : Represents r L cL)
  (hDRep : (dLift : ZMod r) = D)
  (hqRep : (qLift : ZMod r) = q)
  (hNoWrap :
    And (0 <= dLift + Int.ofNat p * qLift)
        (dLift + Int.ofNat p * qLift < Int.ofNat r))
  (hEq : L = D + (p : ZMod r) * q) :
  cL.lift = dLift + Int.ofNat p * qLift := by
  have hCast :
      ((cL.lift : Int) : ZMod r) =
        (((dLift + Int.ofNat p * qLift : Int)) : ZMod r) := by
    calc
      ((cL.lift : Int) : ZMod r) = L := hL
      _ = D + (p : ZMod r) * q := hEq
      _ = (dLift : ZMod r) + (p : ZMod r) * (qLift : ZMod r) := by
        rw [show D = (dLift : ZMod r) from hDRep.symm, show q = (qLift : ZMod r) from hqRep.symm]
      _ = (((dLift + Int.ofNat p * qLift : Int)) : ZMod r) := by
        simp
  exact equalOfBoundedCastEq r cL.lift (dLift + Int.ofNat p * qLift) hCast cL.inRange hNoWrap

/--
Paper target:
`Core rowwise exactness from canonical lifts`.

This packages the bounded exactness lemma into the manuscript-facing theorem
shape: canonical lifts for `L` and `D`, a chosen integer lift for the quotient,
a no-wrap bound for `D + p * q`, and a satisfied row equality in `ZMod r`.
-/
theorem coreRowwiseExactnessFromCanonicalLifts
  (r p : Nat)
  (L D q : ZMod r)
  (cL cD : CanonicalLift r)
  (qLift : Int)
  (hL : Represents r L cL)
  (hD : Represents r D cD)
  (hqRep : (qLift : ZMod r) = q)
  (hNoWrap :
    And (0 <= cD.lift + Int.ofNat p * qLift)
        (cD.lift + Int.ofNat p * qLift < Int.ofNat r))
  (hEq : L = D + (p : ZMod r) * q) :
  cL.lift = cD.lift + Int.ofNat p * qLift := by
  exact coreRowwiseExactnessFromRepresentativeD
    r p L D q cL cD.lift qLift hL hD hqRep hNoWrap hEq

end CoreExactness
