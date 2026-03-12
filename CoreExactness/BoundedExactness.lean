import CoreExactness.Prelude

namespace CoreExactness

set_option autoImplicit false

/--
Minimal modular-to-integer exactness core:
if two integer representatives land in the same residue class in `ZMod r`
and both representatives already lie in `[0, r)`, then they are equal as
integers.
-/
theorem equalOfBoundedCastEq
  (r : Nat)
  (x y : Int)
  (hCast : ((x : Int) : ZMod r) = ((y : Int) : ZMod r))
  (hx : And (0 <= x) (x < Int.ofNat r))
  (hy : And (0 <= y) (y < Int.ofNat r)) :
  x = y := by
  have hModEq :
      x % Int.ofNat r = y % Int.ofNat r :=
    (ZMod.intCast_eq_intCast_iff' x y r).mp hCast
  rw [Int.emod_eq_of_lt hx.1 hx.2, Int.emod_eq_of_lt hy.1 hy.2] at hModEq
  exact hModEq

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
  exact equalOfBoundedCastEq r cL.lift (cD.lift + Int.ofNat p * qLift) hCast cL.inRange hNoWrap

end CoreExactness
