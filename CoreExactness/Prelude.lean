import Mathlib

namespace CoreExactness

set_option autoImplicit false

/--
`CanonicalLift r x` means that the residue-class value `x : ZMod r`
is represented by the integer `lift`, and that `lift` lies in `[0, r)`.
-/
structure CanonicalLift (r : ℕ) where
  lift : ℤ
  inRange : 0 ≤ lift ∧ lift < r

/--
`Represents r x c` packages the fact that `x : ZMod r` is the image of the
integer lift stored in `c`.
-/
def Represents (r : ℕ) (x : ZMod r) (c : CanonicalLift r) : Prop :=
  (c.lift : ZMod r) = x

/--
The canonical residue interval for a modulus `p`.
-/
def InCanonicalResidueRange (p x : ℤ) : Prop :=
  0 ≤ x ∧ x < p

/--
The bounded quotient interval used by the core exactness statements.
-/
def InQuotientRange (B q : ℤ) : Prop :=
  0 ≤ q ∧ q < B

end CoreExactness
