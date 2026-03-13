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

/--
Degree-facing corollary for the concrete Lagrange-interpolated vacuous quotient:
the interpolant used to witness vacuity still has degree strictly below the row
domain size.
-/
theorem vacuousInterpolant_degree_lt
  {F : Type} [Field F]
  (n : Nat)
  (omega : Fin n -> F)
  (hOmega : Set.InjOn omega Set.univ)
  (p : F)
  (L D : Polynomial F) :
  let qVals := quotientValues omega p L D
  let qPoly : Polynomial F := Lagrange.interpolate Finset.univ omega qVals
  qPoly.degree < n := by
  classical
  dsimp
  have hOmegaFinset : Set.InjOn omega (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
    simpa using hOmega
  simpa using
    (Lagrange.degree_interpolate_lt (s := Finset.univ) (v := omega)
      (r := quotientValues omega p L D) hOmegaFinset)

/--
Combined manuscript-facing polynomial vacuity package:
the concrete Lagrange-interpolated quotient both makes the quotient-check
remainder divisible by the row-domain vanishing polynomial and still satisfies
the expected low-degree bound.
-/
theorem polynomialLevelVacuity_dvd_and_degree
  {F : Type} [Field F]
  (n : Nat)
  (omega : Fin n -> F)
  (hOmega : Set.InjOn omega Set.univ)
  (p : F) (hp : Ne p 0)
  (L D : Polynomial F) :
  let qVals := quotientValues omega p L D
  let qPoly : Polynomial F := Lagrange.interpolate Finset.univ omega qVals
  rowVanishingPolynomial omega ∣ vacuityRemainder p L D qPoly ∧ qPoly.degree < n := by
  classical
  dsimp
  exact ⟨polynomialLevelVacuity_dvd n omega hOmega p hp L D,
    vacuousInterpolant_degree_lt n omega hOmega p L D⟩

 
/--
The row-domain vanishing polynomial is monic.
-/
theorem rowVanishingPolynomial_monic
  {F : Type} [Field F] {n : Nat}
  (omega : Fin n -> F) :
  (rowVanishingPolynomial omega).Monic := by
  classical
  simpa [rowVanishingPolynomial] using
    (Polynomial.monic_prod_of_monic (s := Finset.univ)
      (f := fun i : Fin n => Polynomial.X - Polynomial.C (omega i))
      (fun i _ => Polynomial.monic_X_sub_C (omega i)))

/--
The row-domain vanishing polynomial has natDegree exactly equal to the size of
the sampled row domain.
-/
theorem rowVanishingPolynomial_natDegree
  {F : Type} [Field F] {n : Nat}
  (omega : Fin n -> F) :
  (rowVanishingPolynomial omega).natDegree = n := by
  classical
  simpa [rowVanishingPolynomial, Finset.card_univ] using
    (Polynomial.natDegree_prod_of_monic (s := Finset.univ)
      (f := fun i : Fin n => Polynomial.X - Polynomial.C (omega i))
      (h := fun i _ => Polynomial.monic_X_sub_C (omega i)))

/--
Aggregated numerator vacuity: any finite linear combination of vacuous
per-relation remainders is still divisible by the row-domain vanishing
polynomial.
-/
theorem aggregatedNumeratorVacuity_dvd
  {F : Type} [Field F]
  {idx : Type}
  (s : Finset idx)
  (n : Nat)
  (omega : Fin n -> F)
  (hOmega : Set.InjOn omega Set.univ)
  (p : F) (hp : Ne p 0)
  (L D : idx -> Polynomial F)
  (coeff : idx -> F) :
  let qPoly : idx -> Polynomial F :=
    fun t => Lagrange.interpolate Finset.univ omega (quotientValues omega p (L t) (D t))
  let N : Polynomial F :=
    Finset.sum s (fun t => Polynomial.C (coeff t) * vacuityRemainder p (L t) (D t) (qPoly t))
  rowVanishingPolynomial omega ∣ N := by
  classical
  dsimp
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha hs =>
      have hDivA :
          rowVanishingPolynomial omega ∣
            Polynomial.C (coeff a) *
              vacuityRemainder p (L a) (D a)
                (Lagrange.interpolate Finset.univ omega (quotientValues omega p (L a) (D a))) := by
        rcases polynomialLevelVacuity_dvd n omega hOmega p hp (L a) (D a) with ⟨H, hH⟩
        refine ⟨Polynomial.C (coeff a) * H, ?_⟩
        calc
          Polynomial.C (coeff a) *
              vacuityRemainder p (L a) (D a)
                (Lagrange.interpolate Finset.univ omega (quotientValues omega p (L a) (D a))) =
              Polynomial.C (coeff a) * (rowVanishingPolynomial omega * H) := by
            rw [hH]
          _ = rowVanishingPolynomial omega * (Polynomial.C (coeff a) * H) := by
            ring
      simpa [Finset.sum_insert, ha] using dvd_add hDivA hs

/--
Existence form of aggregated numerator vacuity. The aggregated numerator can be
written as the row-domain vanishing polynomial times an explicit quotient
polynomial.
-/
theorem aggregatedNumeratorVacuity_existsQuotient
  {F : Type} [Field F]
  {idx : Type}
  (s : Finset idx)
  (n : Nat)
  (omega : Fin n -> F)
  (hOmega : Set.InjOn omega Set.univ)
  (p : F) (hp : Ne p 0)
  (L D : idx -> Polynomial F)
  (coeff : idx -> F) :
  let qPoly : idx -> Polynomial F :=
    fun t => Lagrange.interpolate Finset.univ omega (quotientValues omega p (L t) (D t))
  let N : Polynomial F :=
    Finset.sum s (fun t => Polynomial.C (coeff t) * vacuityRemainder p (L t) (D t) (qPoly t))
  ∃ HN : Polynomial F, N = rowVanishingPolynomial omega * HN := by
  classical
  dsimp
  simpa using aggregatedNumeratorVacuity_dvd s n omega hOmega p hp L D coeff

/--
Generic quotient-degree lemma for row-domain divisibility.

Once a numerator `N` is known to factor as `Z_Ω * HN` and already satisfies the
manuscript-side bound `natDegree N ≤ 2*n - 2`, the divided quotient `HN` has
natDegree at most `n - 2`.
-/
theorem quotientNatDegree_le_of_rowVanishing_mul
  {F : Type} [Field F]
  (n : Nat)
  (omega : Fin n -> F)
  (hn : 2 <= n)
  (N HN : Polynomial F)
  (hHN : N = rowVanishingPolynomial omega * HN)
  (hNatDegreeN : N.natDegree <= 2 * n - 2) :
  HN.natDegree <= n - 2 := by
  by_cases hZero : HN = 0
  · have hBound : 0 <= n - 2 := by omega
    simpa [hZero] using hBound
  · have hZMonic : (rowVanishingPolynomial omega).Monic :=
      rowVanishingPolynomial_monic omega
    have hZNe : rowVanishingPolynomial omega ≠ 0 := hZMonic.ne_zero
    have hMulDeg :
        (rowVanishingPolynomial omega * HN).natDegree =
          (rowVanishingPolynomial omega).natDegree + HN.natDegree := by
      simpa using Polynomial.natDegree_mul hZNe hZero
    have hStep :
        (rowVanishingPolynomial omega * HN).natDegree <= 2 * n - 2 := by
      simpa [hHN] using hNatDegreeN
    have hStep' : n + HN.natDegree <= 2 * n - 2 := by
      simpa [rowVanishingPolynomial_natDegree omega, hMulDeg] using hStep
    omega

end

end CoreExactness
