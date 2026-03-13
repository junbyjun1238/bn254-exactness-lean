# Paper to Lean Map

This note maps the paper-level theorem spine to the current Lean 4 repository.
It is intentionally conservative: if a paper statement is only partially
formalized or formalized at a more abstract level, that is stated explicitly.

## Formalized As Algebraic Core

### Outer-field generic rowwise vacuity
- Paper meaning: a deferred-quotient row `L = D + pQ` is vacuous over the outer field when `Q` is unconstrained and `p` is invertible.
- Lean status: formalized.
- Lean theorem: `outerFieldGenericRowwiseVacuity`
- File: `CoreExactness/RowVacuity.lean`

### Polynomial-level vacuity on a finite evaluation domain
- Paper meaning: if vacuous quotient values are interpolated across the sampled rows, the quotient-check remainder vanishes on the row domain.
- Lean status: formalized.
- Lean theorems: `polynomialLevelVacuity`, `rowVanishingPolynomial_dvd_of_interpolates`, `polynomialLevelVacuity_dvd`, `aggregatedNumeratorVacuity_dvd`, `aggregatedNumeratorVacuity_existsQuotient`
- File: `CoreExactness/PolyVacuity.lean`

### Low-degree bound for the concrete vacuous interpolant
- Paper meaning: the concrete interpolated vacuous quotient remains low degree on the sampled row domain.
- Lean status: formalized for the concrete interpolant.
- Lean theorems: `vacuousInterpolant_degree_lt`, `polynomialLevelVacuity_dvd_and_degree`, `quotientNatDegree_le_of_rowVanishing_mul`
- File: `CoreExactness/PolyVacuity.lean`

### Modular-to-integer exactness upgrade
- Paper meaning: once the modular equality is paired with canonical lifts and no-wrap, it upgrades to exact equality in `Z`.
- Lean status: formalized.
- Lean theorems: `equalOfBoundedCastEq`, `boundedDeferredQuotientExactness`, `coreRowwiseExactnessFromRepresentativeD`, `coreRowwiseExactnessFromCanonicalLifts`
- Files: `CoreExactness/BoundedExactness.lean`, `CoreExactness/RowwiseExactness.lean`

### Euclidean quotient/remainder recovery
- Paper meaning: on designated residue rows, exactness plus canonical residue range recovers the intended Euclidean remainder and quotient.
- Lean status: formalized.
- Lean theorems: `euclideanQuotientRemainderOfExactness`, `euclideanQuotientRemainderFromCanonicalLifts`
- File: `CoreExactness/EuclideanSemantics.lean`

### Exclusion of the specific vacuous `-p^{-1}` witness class
- Paper meaning: under the manuscript's bounded unsigned quotient range and arithmetic headroom, the specific vacuous witness class is not admissible.
- Lean status: formalized.
- Lean theorems: `natQuotientRangeExcludesNegInv`, `quotientRangeExcludesNegInv`
- File: `CoreExactness/RangeExclusion.lean`

### Packaged manuscript-facing algebraic repair theorem
- Paper meaning: bounded quotient-range exclusion, rowwise exactness, and Euclidean recovery appear together as one algebraic package theorem.
- Lean status: formalized at the algebraic-core level.
- Lean theorem: `boundedRepairExcludesNegInvAndRecoversEuclideanSemantics`
- File: `CoreExactness/PackagedSemantics.lean`

## Abstracted Relative To The Paper

### BN254/M31 concrete instantiation
- Lean status: partially reflected.
- What is present: the algebraic core is formalized generically, and `CoreExactness/BN254Instance.lean` pins the paper constants and basic arithmetic headroom inequalities.
- What is not present: the full concrete family audit, selector wiring, and per-family catalogue closure are not formalized.

### Subgroup-specific vanishing polynomial form
- Lean status: abstracted.
- Current Lean uses a general injective finite evaluation domain and the row-domain vanishing polynomial given by the product of `(X - C (omega i))`.
- It does not specialize that result to a subgroup-specific form such as `X^n - 1`.

## Not Yet Formalized

### Backend/circuit enforcement of the premises
- Not formalized in Lean.
- This repository does not prove that a concrete Halo2 or other backend enforces canonical lifts, quotient-range membership, no-wrap bounds, selector coverage, or transcript-side obligations.

### Full manuscript family/certificate/wiring theorem
- Not formalized in Lean.
- The Lean repo covers the algebraic theorem spine, not the full concrete instantiated theorem with family coverage, appendix audits, and backend closure.

### Universal classification of all bad quotient witnesses
- Not formalized in Lean.
- The range-exclusion result is intentionally specific to the manuscript's highlighted `-p^{-1}` witness class.
