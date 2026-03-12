# BN254 Exactness Lean Formalization

This repository contains a standalone Lean 4 formalization of the core theorem
spine behind the BN254 deferred-quotient exactness repair note.

The formalization is intentionally narrow. It isolates the mathematical core of
the vacuity diagnosis and the exactness repair, while leaving backend,
catalogue, and circuit-integration questions outside the current scope.

## What Is Proved

The current Lean package proves the following core statements.

1. `outerFieldGenericRowwiseVacuity`
   - In any field, if `p != 0`, then a deferred-quotient row equation of the
     form `L = D + p * Q` can be made tautologically true by choosing the
     quotient witness pointwise as `(L - D) / p`.

2. `boundedDeferredQuotientExactness`
   - If two integer lifts represent the same residue in `ZMod r` and both lifts
     lie in the canonical interval `[0, r)`, then they are equal as integers.

3. `coreRowwiseExactnessFromCanonicalLifts`
   - This packages the bounded exactness lemma in the manuscript-facing rowwise
     form: canonical lifts for the residue side, an integer lift for the
     quotient, a no-wrap bound, and a satisfied modular equality imply exact
     integer equality.

4. `euclideanQuotientRemainderFromCanonicalLifts`
   - Once the rowwise exactness theorem has produced an exact identity and the
     designated residue lift lies in `[0, p)`, the residue is recovered as
     `L mod p` and the quotient is recovered as `L / p`.

5. `polynomialLevelVacuity`
   - If the quotient witness polynomial is chosen by interpolating the vacuous
     rowwise quotient values over a finite evaluation domain, then the
     deferred-quotient remainder vanishes on every sampled node.

6. `polynomialLevelVacuity_dvd`
   - The same polynomial-level vacuity construction implies that the
     row-domain vanishing polynomial divides the deferred-quotient remainder.

7. `polynomialLevelVacuity_dvd_and_degree`
   - The concrete Lagrange-interpolated vacuous quotient simultaneously yields
     row-domain divisibility and still satisfies the expected low-degree bound
     `degree qPoly < n`.

8. `quotientRangeExcludesNegInv`
   - Under the manuscript-style unsigned quotient bound and explicit headroom,
     the bounded quotient interval excludes the specific vacuous witness class
     `-p^{-1}` in the prime-field outer modulus.

## Current Mathematical Boundary

This repository proves the core algebraic spine only.

In scope:

- outer-field generic rowwise vacuity,
- bounded exactness over canonical integer lifts,
- manuscript-facing rowwise exactness from those lifts,
- Euclidean quotient/remainder recovery from exactness plus canonical residue
  range,
- polynomial vacuity over a finite evaluation domain,
- divisibility by the row-domain vanishing polynomial.
- a degree-facing corollary for the concrete interpolated vacuous quotient.
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
row-domain vanishing polynomial

`rowVanishingPolynomial omega = ∏ i, (X - C (omega i))`.

This is more general than a subgroup-specific statement such as `X^n - 1`. If
the evaluation domain later specializes to a multiplicative subgroup, that
specialization should be stated separately at the manuscript level.

### Conditional Exactness

The exactness theorems here are conditional theorems. They assume the
canonical-lift and no-wrap premises required for the integer lift step. This
repository does not yet prove that a particular circuit backend enforces those
premises automatically.

## Repository Layout

- `CoreExactness/Prelude.lean`
- `CoreExactness/RowVacuity.lean`
- `CoreExactness/PolyVacuity.lean`
- `CoreExactness/BoundedExactness.lean`
- `CoreExactness/RowwiseExactness.lean`
- `CoreExactness/EuclideanSemantics.lean`
- `CoreExactness/RangeExclusion.lean`
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

The current intended state is a full successful `lake build` with no remaining
`sorry` placeholders in the core theorem files.

## Codespaces

The repository includes a `.devcontainer/` setup that warms the environment by
installing Lean, fetching the mathlib cache, and running the standard build
path automatically.

## Working Style

These rules were used to build the current package and are kept explicit for
future contributors:

1. Modularize aggressively.
2. Stabilize theorem boundaries before proof search.
3. Use full `lake build` checkpoints instead of trusting local incremental
   success.
