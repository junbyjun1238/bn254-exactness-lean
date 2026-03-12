import CoreExactness.Prelude

namespace CoreExactness

set_option autoImplicit false

/--
Paper target:
`Bounded deferred-quotient exactness`.

This is the algebraic heart of the repair: if two integer lifts define the same
residue in `ZMod r`, and both lifts are already known to lie in `[0, r)`, then
those lifts are equal as integers.
-/
theorem boundedDeferredQuotientExactness
  (r p : Nat)
  (cL cD : CanonicalLift r)
  (qLift : Int)
  (hCast :
    ((cL.lift : Int) : ZMod r) =
      (((cD.lift + Int.ofNat p * qLift : Int)) : ZMod r))
  (hNoWrap :
    And (0 <= cD.lift + Int.ofNat p * qLift)
        (cD.lift + Int.ofNat p * qLift < Int.ofNat r)) :
  cL.lift = cD.lift + Int.ofNat p * qLift := by
  have hModEq :
      cL.lift % Int.ofNat r = (cD.lift + Int.ofNat p * qLift) % Int.ofNat r :=
    (ZMod.intCast_eq_intCast_iff' cL.lift (cD.lift + Int.ofNat p * qLift) r).mp hCast
  rw [Int.emod_eq_of_lt cL.inRange.1 cL.inRange.2, Int.emod_eq_of_lt hNoWrap.1 hNoWrap.2] at hModEq
  exact hModEq

end CoreExactness
