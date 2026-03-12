# BN254 Exactness Lean Formalization

This repository isolates the Lean 4 formalization of the core theorem spine
behind the deferred-quotient exactness note.

The goal is deliberately narrow:

- formalize the vacuity diagnosis,
- formalize the bounded exactness repair core,
- keep the project machine-checkable and Codespaces-friendly,
- avoid dragging in Halo2/backend/catalogue machinery too early.

## Scope

In scope:

- outer-field generic rowwise vacuity,
- polynomial-level vacuity,
- bounded deferred-quotient exactness,
- core rowwise exactness from canonical lifts.

Out of scope:

- corollaries,
- family-specific appendix audits,
- wiring and coverage proofs,
- Halo2 circuit semantics,
- backend transcript or Fiat-Shamir claims,
- benchmark correctness.

## Layout

- `CoreExactness/Prelude.lean`
- `CoreExactness/RowVacuity.lean`
- `CoreExactness/PolyVacuity.lean`
- `CoreExactness/BoundedExactness.lean`
- `CoreExactness/RowwiseExactness.lean`
- `CoreExactness.lean`
- `docs/lean_formalization_scope_estimate.md`
- `docs/lean_formalization_work_plan.md`
- `docs/lean_codespaces_workflow.md`

## Working Discipline

These rules are mandatory:

1. **Modularize aggressively**
   - Keep one conceptual theorem family per module.
   - If a file starts to mix setup, vacuity, and exactness, split it.

2. **Use `sorry` first**
   - Stabilize imports, definitions, and theorem statements before fighting proofs.
   - Replace `sorry` incrementally.

3. **Run `lake build` at every checkpoint**
   - Small inner-loop builds are fine during proof work.
   - The checkpoint rule is still a full `lake build`.

## Codespaces

This repo is meant to be opened directly in GitHub Codespaces.

The `.devcontainer/` warm-up installs Lean, fetches mathlib cache, and runs:

```bash
lake exe cache get
lake build
```

If you are working locally, the same commands are the first required checkpoint.
