# Lean Codespaces Workflow

## Why Codespaces

This repository is intentionally Lean-only. The theorem-development workspace is
kept separate from the Rust benchmark harness so that Codespaces can boot
straight into mathlib-backed proof work.

Codespaces is the preferred remote environment because:

- the Lean toolchain is easy to bootstrap there,
- mathlib cache warming is straightforward,
- the project can be resumed without depending on the local Windows setup.

## Required Working Discipline

These rules are mandatory:

1. **Modularization is not optional**
   - One theorem family per module.
   - Keep setup code in `Prelude.lean`.
   - Do not accumulate large mixed proof files.

2. **Start with `sorry`**
   - First stabilize imports, definitions, and theorem statements.
   - Then replace `sorry` in small increments.
   - This keeps long sessions from stalling on one proof.

3. **Run `lake build` constantly**
   - full `lake build` at every real checkpoint,
   - narrower builds are allowed only as a short inner loop.

## Recommended Checkpoints

### Checkpoint 1

- project boots,
- `lake exe cache get` works,
- theorem skeleton modules compile.

### Checkpoint 2

- `RowVacuity.lean` complete,
- `BoundedExactness.lean` complete,
- full `lake build` passes.

### Checkpoint 3

- `RowwiseExactness.lean` complete,
- full `lake build` passes.

### Checkpoint 4

- polynomial layer complete,
- full `lake build` passes,
- README and scope note updated.

## First Commands in Codespaces

```bash
lake exe cache get
lake build
```

## Practical Advice

- If the polynomial vacuity layer starts dominating the schedule, stop and keep
  the rowwise vacuity + repair theorem package as the first credible release.
- Do not let one hard divisibility proof block the whole project.
