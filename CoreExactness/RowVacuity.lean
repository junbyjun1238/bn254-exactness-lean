import CoreExactness.Prelude

namespace CoreExactness

set_option autoImplicit false

/--
Paper target:
`The deferred-quotient vacuity pathology is outer-field generic`.

This is the rowwise version of the vacuity mechanism: once `p` is invertible,
the prover can define `Q[j] = p⁻¹ (L[j] - D[j])`, making `L = D + pQ`
tautologically true over the outer field.
-/
theorem outerFieldGenericRowwiseVacuity
  {F : Type} [Field F]
  (n : ℕ)
  (p : F) (hp : p ≠ 0)
  (L D : Fin n → F) :
  ∃ Q : Fin n → F, ∀ j : Fin n, L j = D j + p * Q j := by
  sorry

end CoreExactness
