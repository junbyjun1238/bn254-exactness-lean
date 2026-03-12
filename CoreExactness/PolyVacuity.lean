import CoreExactness.Prelude

open Lagrange

namespace CoreExactness

set_option autoImplicit false

noncomputable section

/--
The vacuous quotient values chosen pointwise from polynomial evaluations.
-/
def quotientValues
  {F : Type} [Field F] {n : Nat}
  (omega : Fin n -> F) (p : F) (L D : Polynomial F) : Fin n -> F :=
  fun i => p⁻¹ * (L.eval (omega i) - D.eval (omega i))

/--
The polynomial remainder used by the deferred-quotient quotient-check layer.
-/
def vacuityRemainder
  {F : Type} [Field F]
  (p : F) (L D Q : Polynomial F) : Polynomial F :=
  L - D - Polynomial.C p * Q

/--
`InterpolatesOn omega Q v` means that `Q` matches the row values `v` on the
row-domain nodes defined by `omega`.
-/
def InterpolatesOn
  {F : Type} [Field F] {n : Nat}
  (omega : Fin n -> F) (Q : Polynomial F) (v : Fin n -> F) : Prop :=
  forall i : Fin n, Polynomial.eval (omega i) Q = v i

/--
Core polynomial-level vacuity: any quotient polynomial that interpolates the
vacuous pointwise quotient values forces the quotient-check remainder to vanish
on every row-domain node.
-/
theorem polynomialLevelVacuityOfInterpolates
  {F : Type} [Field F]
  (n : Nat)
  (omega : Fin n -> F)
  (p : F) (hp : Ne p 0)
  (L D Q : Polynomial F)
  (hQ : InterpolatesOn omega Q (quotientValues omega p L D)) :
  forall i : Fin n,
    Polynomial.eval (omega i) (vacuityRemainder p L D Q) = 0 := by
  intro i
  have hInv : p * p⁻¹ = 1 := by
    simpa using mul_inv_cancel₀ hp
  calc
    Polynomial.eval (omega i) (vacuityRemainder p L D Q)
        = L.eval (omega i) - D.eval (omega i) - p * Polynomial.eval (omega i) Q := by
            simp [vacuityRemainder]
    _ = L.eval (omega i) - D.eval (omega i) - p * quotientValues omega p L D i := by
      rw [hQ i]
    _ = L.eval (omega i) - D.eval (omega i)
          - p * (p⁻¹ * (L.eval (omega i) - D.eval (omega i))) := by
      rfl
    _ = L.eval (omega i) - D.eval (omega i)
          - (L.eval (omega i) - D.eval (omega i)) := by
      rw [← mul_assoc, hInv, one_mul]
    _ = 0 := by
      ring

/--
Paper target:
`Polynomial-level vacuity under unbounded quotient witnesses`.

This corollary packages the core vacuity statement with the concrete Lagrange
interpolant over the row domain.
-/
theorem polynomialLevelVacuity
  {F : Type} [Field F]
  (n : Nat)
  (omega : Fin n -> F)
  (hOmega : Set.InjOn omega Set.univ)
  (p : F) (hp : Ne p 0)
  (L D : Polynomial F) :
  let qVals := quotientValues omega p L D
  let qPoly : Polynomial F := Lagrange.interpolate Finset.univ omega qVals
  forall i : Fin n,
    Polynomial.eval (omega i) (vacuityRemainder p L D qPoly) = 0 := by
  classical
  dsimp
  have hOmegaFinset : Set.InjOn omega ↑(Finset.univ : Finset (Fin n)) := by
    simpa using hOmega
  have hQ :
      InterpolatesOn omega (Lagrange.interpolate Finset.univ omega (quotientValues omega p L D))
        (quotientValues omega p L D) := by
    intro i
    simpa using
      Lagrange.eval_interpolate_at_node (quotientValues omega p L D) hOmegaFinset
        (by simp : i ∈ Finset.univ)
  exact polynomialLevelVacuityOfInterpolates n omega p hp L D
    (Lagrange.interpolate Finset.univ omega (quotientValues omega p L D)) hQ

end

end CoreExactness
