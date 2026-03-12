# Lean Formalization Scope Estimate

## Goal

Estimate the smallest credible Lean formalization package for:

1. the deferred-quotient vacuity diagnosis, and
2. the core exactness-repair theorem,

while explicitly excluding corollaries, Halo2/backend claims, and catalogue-specific appendix machinery.

## Recommended Formalization Boundary

### In scope

The smallest high-value Lean target is:

1. **Outer-field generic rowwise vacuity**
   - manuscript slice: Proposition `The deferred-quotient vacuity pathology is outer-field generic`
   - core statement:
     - for any field `F`,
     - any invertible `p : F`,
     - arbitrary rowwise values `L[j], D[j]`,
     - define `Q[j] = p^{-1}(L[j] - D[j])`,
     - then `L[j] = D[j] + p * Q[j]` holds pointwise.
   - value:
     - this captures the algebraic vacuity mechanism itself in the cleanest possible form.

2. **Polynomial-level vacuity under unbounded quotient witnesses**
   - manuscript slice: Proposition `Polynomial-level vacuity under unbounded quotient witnesses`
   - core statement:
     - define the rowwise quotient values as above,
     - interpolate a low-degree `Q_t(X)` through them,
     - define `R_t(X) = L_t(X) - D_t(X) - p Q_t(X)`,
     - prove `R_t` vanishes on the row domain and is divisible by the row-domain vanishing polynomial.
   - value:
     - this is the paper's real bridge from rowwise vacuity to quotient-check vacuity.

3. **Bounded deferred-quotient exactness**
   - manuscript slice: Lemma `Bounded deferred-quotient exactness`
   - core statement:
     - if `L`, `D`, `q` are canonical lifts of integers,
     - if `0 <= D + p q < r`,
     - and `L = D + p q` in `R = ZMod r`,
     - then the equality lifts to an exact identity in `Z`.
   - value:
     - this is the algebraic heart of the repair.

4. **Core rowwise exactness from canonical lifts**
   - manuscript slice: Theorem `Core rowwise exactness from canonical lifts`
   - core statement:
     - package the integer-lift assumptions for one satisfied row,
     - conclude exact integer equality,
     - and on canonical residue rows recover Euclidean quotient/remainder.
   - value:
     - this is the clean theorem-level statement to cite as the Lean-mechanized core.

### Explicitly out of scope

The following should stay out:

1. aggregated-numerator corollaries,
2. family-specific audited bounds,
3. template/realization coherence for the full BN254 catalogue,
4. complete wiring/coverage proofs,
5. 31/66-bit lookup gadget realization details,
6. Halo2 circuit semantics,
7. backend conformance / Fiat-Shamir / PCS closure,
8. full wrapper theorem.

## Why this boundary is credible

This boundary captures:

- the exact failure mode that makes `L = D + pQ` vacuous without quotient binding, and
- the exact algebraic theorem that repairs the interpretation once canonical lifts and no-wrap conditions are present.

It avoids the implementation-heavy layers that would turn the effort into a full backend or circuit formalization project.

## Difficulty by component

### Easy / moderate

1. **Bounded exactness lemma**
   - mostly integer arithmetic plus equality in `ZMod r`
   - likely the cleanest first Lean target

2. **Core rowwise exactness theorem**
   - mostly a packaging theorem on top of the bounded exactness lemma
   - low conceptual risk once the lemma is done

### Moderate

3. **Outer-field generic rowwise vacuity**
   - algebraically simple
   - mostly depends on how the row-domain indexing is encoded

### Main difficulty

4. **Polynomial-level vacuity**
   - this is the hardest part
   - the issue is not the mathematics itself, but the Lean encoding:
     - finite-domain interpolation,
     - evaluation on a finite row set,
     - vanishing polynomial divisibility,
     - degree bookkeeping.

This part likely dominates the time budget.

## Practical recommendation

There are really two sensible Lean packages:

### Option A: Minimum strong signal

Formalize:

- outer-field generic rowwise vacuity,
- bounded deferred-quotient exactness,
- core rowwise exactness theorem.

Do **not** formalize polynomial-level vacuity yet.

Pros:

- much faster,
- still proves the core theorem-level algebra,
- strong enough as a credibility signal in a grant/profile context.

Cons:

- does not cover the full vacuity story stated in the paper.

### Option B: Full "core paper result" package

Formalize:

- rowwise vacuity,
- polynomial-level vacuity,
- bounded exactness,
- core rowwise exactness.

Pros:

- this is the most honest formal counterpart to "the vacuity problem plus the repair theorem."

Cons:

- substantially more work,
- polynomial interpolation/divisibility will dominate the schedule.

## Estimate

### If the goal is a serious, clean Lean package

Assuming no existing Lean project/toolchain is already set up in this repository:

#### Option A

- Lean toolchain + project bootstrap: `0.5-1 day`
- rowwise vacuity: `0.5-1 day`
- bounded exactness + core rowwise theorem: `1-2 days`
- cleanup, comments, theorem naming, compile stability: `0.5-1 day`

**Estimate:** `3-5 focused days`

#### Option B

- everything in Option A: `3-5 days`
- polynomial-level vacuity formalization: `3-6 additional days`
- cleanup and proof refactors: `1-2 additional days`

**Estimate:** `7-13 focused days`

## Recommendation

If the objective is:

- "show I can also do theorem-assistant work,"

then **Option A is the best ROI**.

If the objective is:

- "formalize the actual vacuity diagnosis and repair core from the paper, not just the repair theorem,"

then **Option B is the correct target**, but it should be treated as a real side project rather than a quick credibility add-on.

## Bottom line

The core exactness theorem itself is not the hard part. The hard part is the polynomial-level vacuity statement, because Lean must encode interpolation and vanishing-polynomial divisibility cleanly.

So the honest estimate is:

- **repair theorem only**: small-to-medium effort,
- **vacuity diagnosis plus repair theorem**: medium effort, with the polynomial layer as the main cost driver.
