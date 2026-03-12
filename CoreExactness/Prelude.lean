import Mathlib

namespace CoreExactness

set_option autoImplicit false

/--
`CanonicalLift r` packages an integer representative for a residue modulo `r`
together with the claim that the representative lies in the canonical interval
`[0, r)`.
-/
structure CanonicalLift (r : Nat) where
  lift : Int
  inRange : And (0 <= lift) (lift < Int.ofNat r)

/--
`Represents r x c` means that the integer representative stored in `c` maps to
`x : ZMod r`.
-/
def Represents (r : Nat) (x : ZMod r) (c : CanonicalLift r) : Prop :=
  (c.lift : ZMod r) = x

/--
Canonical residue interval for an integer modulus `p`.
-/
def InCanonicalResidueRange (p x : Int) : Prop :=
  And (0 <= x) (x < p)

/--
The bounded quotient interval used by the core exactness statements.
-/
def InQuotientRange (b q : Int) : Prop :=
  And (0 <= q) (q < b)

end CoreExactness
