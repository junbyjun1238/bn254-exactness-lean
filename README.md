# BN254 Exactness Lean Formalization

This repository contains a standalone Lean 4 formalization of the algebraic
core behind the BN254 deferred-quotient exactness repair note.

The scope is intentionally narrow. It isolates the vacuity diagnosis and the
exactness-repair spine at the theorem level, while leaving backend, circuit,
and catalogue-specific obligations out of scope.

## What Is Proved

The current package proves the following core results.

1. `outerFieldGenericRowwiseVacuity`
   - In any field, if `p != 0`, then a deferred-quotient row equation
     `L = D + p * Q` can be made tautologically true by choosing the quotient
     witness pointwise as `(L - D) / p`.

2. `equalOfBoundedCastEq`
   - If two integers map to the same residue in `ZMod r` and both already lie
     in `[0, r)`, then they are equal as integers.

3. `boundedDeferredQuotientExactness`
   - A manuscript-facing wrapper around the bounded cast-equality core:
     canonical lifts and a no-wrap bound upgrade modular equality to exact
     integer equality.

4. `coreRowwiseExactnessFromCanonicalLifts`
   - The rowwise exactness theorem in the concrete manuscript shape: canonical
     lifts for `L` and `D`, an integer lift for the quotient, a no-wrap bound,
     and a satisfied modular row equality imply exact integer equality.

5. `euclideanQuotientRemainderFromCanonicalLifts`
   - Once exactness is established and the designated residue lift lies in
     `[0, p)`, the residue is recovered as `L mod p` and the quotient is
     recovered as `L / p`.

6. `polynomialLevelVacuity`
   - If the quotient witness polynomial is chosen by interpolating the vacuous
     rowwise quotient values over a finite evaluation domain, then the
     deferred-quotient remainder vanishes on every sampled node.

7. `polynomialLevelVacuity_dvd_and_degree`
   - The concrete Lagrange-interpolated vacuous quotient simultaneously gives
     row-domain divisibility and the expected low-degree bound
     `degree qPoly < n`.

8. `quotientRangeExcludesNegInv`
   - Under the manuscript-style unsigned quotient bound and explicit headroom,
     the bounded quotient interval excludes the specific vacuous witness class
     `-p^{-1}` in the prime-field outer modulus.

9. `boundedRepairExcludesNegInvAndRecoversEuclideanSemantics`
   - A single manuscript-facing package theorem combines the bounded range
     exclusion, rowwise exactness path, and Euclidean recovery path into one
     result.

## Current Mathematical Boundary

This repository proves the algebraic core only.

In scope:

- outer-field generic rowwise vacuity,
- bounded exactness over canonical integer lifts,
- manuscript-facing rowwise exactness from those lifts,
- Euclidean quotient/remainder recovery from exactness plus canonical residue
  range,
- polynomial vacuity over a finite injective evaluation domain,
- divisibility by the row-domain vanishing polynomial,
- a degree-facing corollary for the concrete interpolated vacuous quotient,
- explicit exclusion of the `-p^{-1}` vacuous witness class under bounded
  unsigned quotient ranges.

Out of scope:

- family-specific appendix audits,
- selector wiring and catalogue coverage proofs,
- Halo2 circuit semantics,
- backend transcript extraction,
- PCS or Fiat-Shamir soundness,
- benchmark correctness or performance claims.

## Important Scope Notes

### General Evaluation Domains

The polynomial divisibility result is stated for a general finite evaluation
domain `omega : Fin n -> F` with an injectivity hypothesis. The divisor is the
row-domain vanishing polynomial, i.e. the product over the sampled nodes of
`(X - C (omega i))`.

This is more general than a subgroup-specific statement such as `X^n - 1`. If
the evaluation domain later specializes to a multiplicative subgroup, that
specialization should be stated separately.

### Conditional Exactness

The exactness theorems here are conditional theorems. They assume the
canonical-lift and no-wrap premises required for the integer lift step. This
repository does not prove that a particular circuit backend enforces those
premises automatically.

## Repository Layout

- `CoreExactness/Prelude.lean`
- `CoreExactness/RowVacuity.lean`
- `CoreExactness/PolyVacuity.lean`
- `CoreExactness/BoundedExactness.lean`
- `CoreExactness/RowwiseExactness.lean`
- `CoreExactness/EuclideanSemantics.lean`
- `CoreExactness/RangeExclusion.lean`
- `CoreExactness/PackagedSemantics.lean`
- `CoreExactness.lean`
- `docs/lean_formalization_scope_estimate.md`
- `docs/lean_formalization_work_plan.md`
- `docs/lean_codespaces_workflow.md`

## Build

This repo is designed to work both locally and in GitHub Codespaces.

Required checkpoint:

```bash
lake exe cache get
lake build
```

The intended state is a clean successful `lake build` with no `sorry`
placeholders in the core theorem files.

## Codespaces

The repository includes a `.devcontainer/` setup that installs Lean, warms the
mathlib cache, and runs the standard build path automatically.

## Working Style

These rules were used to build the current package and are kept explicit for
future contributors:

1. Modularize aggressively.
2. Stabilize theorem boundaries before proof search.
3. Use full `lake build` checkpoints instead of trusting local incremental
   success.
