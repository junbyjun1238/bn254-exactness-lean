import CoreExactness.Prelude

namespace CoreExactness

set_option autoImplicit false

/--
Paper target:
`The deferred-quotient vacuity pathology is outer-field generic`.

This is the rowwise version of the vacuity mechanism: once `p` is invertible,
the prover can define `Q[j] = (L[j] - D[j]) / p`, making `L = D + p * Q`
tautologically true over the outer field.
-/
theorem outerFieldGenericRowwiseVacuity
  {F : Type} [Field F]
  (n : Nat)
  (p : F) (hp : Ne p 0)
  (L D : Fin n -> F) :
  Exists (fun Q : Fin n -> F => (j : Fin n) -> L j = D j + p * Q j) := by
  refine Exists.intro (fun j => (L j - D j) / p) ?_
  intro j
  have hcancel : p * ((L j - D j) / p) = L j - D j := by
    field_simp [hp]
  calc
    L j = D j + (L j - D j) := by
      ring
    _ = D j + p * ((L j - D j) / p) := by
      rw [hcancel]

end CoreExactness
