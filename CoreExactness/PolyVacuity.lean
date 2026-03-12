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
The row-domain vanishing polynomial attached to the sampled nodes `omega`.
-/
def rowVanishingPolynomial
  {F : Type} [Field F] {n : Nat}
  (omega : Fin n -> F) : Polynomial F :=
  ∏ i : Fin n, (Polynomial.X - Polynomial.C (omega i))

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
If the quotient polynomial interpolates the vacuous pointwise quotient values,
then the row-domain vanishing polynomial divides the quotient-check remainder.
-/
theorem rowVanishingPolynomial_dvd_of_interpolates
  {F : Type} [Field F]
  (n : Nat)
  (omega : Fin n -> F)
  (hOmega : Set.InjOn omega Set.univ)
  (p : F) (hp : Ne p 0)
  (L D Q : Polynomial F)
  (hQ : InterpolatesOn omega Q (quotientValues omega p L D)) :
  rowVanishingPolynomial omega ∣ vacuityRemainder p L D Q := by
  classical
  have hZero := polynomialLevelVacuityOfInterpolates n omega p hp L D Q hQ
  have hInj : Function.Injective omega := by
    intro a b hab
    exact hOmega (by simp) (by simp) hab
  have hPairwise :
      ((↑(Finset.univ : Finset (Fin n)) : Set (Fin n))).Pairwise
        (Function.onFun IsCoprime fun i => Polynomial.X - Polynomial.C (omega i)) := by
    simpa [Set.pairwise_univ] using
      (Polynomial.pairwise_coprime_X_sub_C hInj :
        Pairwise (Function.onFun IsCoprime fun i => Polynomial.X - Polynomial.C (omega i)))
  have hFactor :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (Polynomial.X - Polynomial.C (omega i)) ∣ vacuityRemainder p L D Q := by
    intro i _
    apply (Polynomial.dvd_iff_isRoot).2
    simpa [Polynomial.IsRoot] using hZero i
  simpa [rowVanishingPolynomial] using
    (Finset.prod_dvd_of_coprime (t := Finset.univ) hPairwise hFactor)

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

/--
Divisibility form of polynomial-level vacuity under the Lagrange interpolant.
-/
theorem polynomialLevelVacuity_dvd
  {F : Type} [Field F]
  (n : Nat)
  (omega : Fin n -> F)
  (hOmega : Set.InjOn omega Set.univ)
  (p : F) (hp : Ne p 0)
  (L D : Polynomial F) :
  let qVals := quotientValues omega p L D
  let qPoly : Polynomial F := Lagrange.interpolate Finset.univ omega qVals
  rowVanishingPolynomial omega ∣ vacuityRemainder p L D qPoly := by
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
  exact rowVanishingPolynomial_dvd_of_interpolates n omega hOmega p hp L D
    (Lagrange.interpolate Finset.univ omega (quotientValues omega p L D)) hQ

end

end CoreExactness
