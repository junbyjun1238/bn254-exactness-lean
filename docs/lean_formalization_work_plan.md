# Lean Formalization Work Plan

## Purpose

This plan turns the core paper result into a staged Lean project with useful intermediate outputs.

Target scope:

- include:
  - rowwise vacuity,
  - polynomial-level vacuity,
  - bounded deferred-quotient exactness,
  - core rowwise exactness from canonical lifts.
- exclude:
  - corollaries,
  - familywise audit appendices,
  - wiring/coverage proofs,
  - Halo2/backend semantics,
  - benchmark correctness.

## Success Standard

The best outcome is not merely "some Lean file exists."

The useful outcome is:

1. a clean Lean project,
2. a small, readable theorem spine matching the paper's central narrative,
3. enough structure to cite this as evidence of machine-checked reasoning ability in ESP/profile material,
4. a graceful fallback if the polynomial layer takes longer than expected.

## Project Shape

Recommended file structure:

- `CoreExactness/Prelude.lean`
  - parameters, notation, helper lemmas
- `CoreExactness/RowVacuity.lean`
  - outer-field generic rowwise vacuity
- `CoreExactness/PolyVacuity.lean`
  - polynomial-level vacuity
- `CoreExactness/BoundedExactness.lean`
  - bounded deferred-quotient exactness
- `CoreExactness/RowwiseExactness.lean`
  - core rowwise exactness from canonical lifts
- `CoreExactness.lean`
  - umbrella import file

## Suggested 10-Day Plan

### Day 1: Environment and theorem skeleton

Goal:

- install Lean toolchain,
- bootstrap a tiny project,
- create theorem/file skeletons,
- write the central definitions and theorem statements before proving everything.

Deliverables:

- compilable Lean project,
- theorem declarations for all four targets,
- short `README` note describing scope.

Why this day matters:

- if Day 1 slips badly, the rest of the schedule must be adjusted immediately.

### Day 2: Shared helper layer

Goal:

- define the minimum common setup:
  - field parameter,
  - invertible `p`,
  - rowwise value conventions,
  - canonical integer-lift assumptions,
  - helper lemmas for equality in `ZMod r` versus equality in `Z`.

Deliverables:

- `Prelude.lean`,
- reusable helper lemmas for range-bounded lift arguments.

Key risk:

- avoid overbuilding abstraction.
- this should support only the four target theorems.

### Day 3: Rowwise vacuity

Goal:

- prove the outer-field generic rowwise vacuity proposition.

Deliverables:

- `RowVacuity.lean` complete,
- one short prose note mapping it to the manuscript proposition.

Expected difficulty:

- low to moderate.

This is the first visible milestone that already has standalone value:

- it shows the failure mode itself is machine-checkable.

### Day 4: Bounded exactness lemma

Goal:

- prove the bounded deferred-quotient exactness lemma.

Deliverables:

- `BoundedExactness.lean` complete,
- exact statement aligned with the manuscript lemma,
- supporting helper lemmas factored cleanly.

Expected difficulty:

- moderate.

This is the most reusable positive theorem in the package.

### Day 5: Core rowwise exactness theorem

Goal:

- prove the core rowwise exactness theorem from canonical lifts.

Deliverables:

- `RowwiseExactness.lean` complete,
- theorem statement and proof matching the manuscript core theorem,
- explicit note that this is the mechanized repair theorem.

Expected difficulty:

- moderate once Day 4 is done.

### Checkpoint A: End of Day 5

If Days 1-5 succeed, the project is already useful even if the polynomial layer remains unfinished.

At that point, you can truthfully say:

- the core repair theorem is mechanized,
- the outer-field vacuity mechanism is mechanized,
- the remaining unfinished work is the polynomial quotient-check layer.

This is already a strong credibility signal.

### Day 6: Polynomial-layer setup

Goal:

- choose the Lean representation for:
  - finite row domain,
  - evaluation on a finite set,
  - vanishing polynomial,
  - interpolation assumptions.

Deliverables:

- design decision note,
- minimal working encoding for the polynomial layer.

Expected difficulty:

- high relative to previous days.

This is the main architectural day.

### Day 7: Vanishing-on-domain argument

Goal:

- prove the part of polynomial vacuity that shows:
  - the constructed remainder polynomial vanishes on the row domain.

Deliverables:

- first half of `PolyVacuity.lean`,
- evaluation lemmas and row-domain argument.

Expected difficulty:

- moderate to high.

### Day 8: Divisibility by the vanishing polynomial

Goal:

- finish the implication from vanishing on the domain to divisibility by `Z_Omega`.

Deliverables:

- core divisibility theorem used by the polynomial vacuity statement.

Expected difficulty:

- high.

This is likely the single hardest proof step in the whole package.

### Day 9: Degree bookkeeping and final polynomial vacuity theorem

Goal:

- finish degree bounds,
- state and prove the full polynomial-level vacuity proposition in one place.

Deliverables:

- `PolyVacuity.lean` complete,
- theorem comments matching the paper wording.

Expected difficulty:

- moderate to high.

### Day 10: Cleanup and packaging

Goal:

- refactor names,
- add theorem-to-paper mapping comments,
- make imports clean,
- produce one short markdown summary explaining what is mechanized and what is not.

Deliverables:

- clean build,
- tidy theorem names,
- `docs/lean_formalization_note.md` or equivalent short summary.

## Fallback Boundaries

### Fallback 1: Stop after Day 5

If the polynomial layer becomes a time sink, stop after:

- rowwise vacuity,
- bounded exactness,
- core rowwise exactness.

This still gives a strong package.

Best use:

- profile / prior evidence,
- grant credibility signal,
- "I can mechanize the core theorem spine."

### Fallback 2: Partial polynomial package

If divisibility turns out to be the blocker, keep:

- rowwise vacuity,
- bounded exactness,
- core rowwise exactness,
- the polynomial setup plus vanishing-on-domain lemma.

This is weaker than the full target, but still honest and technically meaningful.

## Decision Rule

Use this rule during execution:

1. If Day 6 is not resolved by the end of Day 7, switch to Fallback 1 or 2.
2. Do not let the polynomial layer consume unlimited time.
3. The goal is a strong mechanized theorem spine, not an endless formalization detour.

## Recommendation

Recommended execution mode:

- plan for the full 10-day package,
- commit psychologically to Checkpoint A by Day 5,
- treat Days 6-10 as the higher-risk polynomial extension.

This gives the best balance:

- if everything works, you get the full vacuity-plus-repair Lean story,
- if not, you still end with a very strong partial package rather than a half-broken project.

## Bottom Line

The best practical framing is:

- **Days 1-5** buy a strong machine-checked repair core,
- **Days 6-10** buy the additional credibility of formalizing the vacuity story all the way up to the polynomial quotient-check layer.

That makes the extra investment attractive, but only if the polynomial layer is managed as a bounded risk rather than an open-ended rabbit hole.


