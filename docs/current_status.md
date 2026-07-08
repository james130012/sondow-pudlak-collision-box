# Current Formal Status

The current public artifact is a Lean-checked clean Sondow-Pudlak collision
route. It should be read as a reproducible formal certificate for the
proof-level/collision-level threshold

```lean
N = max upperN threshold
```

not as a final unconditional proof of the irrationality of Euler's constant and
not as a decimal extraction of `N`.

## Reproducible Checkpoint

The audited release is `bigN-halfden-full-20260708`, pinned to commit:

```text
2a7458c253aae4050a0a3a18424abea952d26bc3
```

The clean submission theorem is:

```lean
cleanUpperProvider_submissionRoute
```

defined in:

```text
integration/SondowProjectBigNCleanSubmissionRoute.lean
```

It demonstrates:

- the clean rational branch computes `N = max upperN threshold`;
- the `upperN` and `threshold` come from the same clean checker route;
- the route derives the contradiction on the rational branch;
- the audited axiom profile is `[propext, Classical.choice, Quot.sound]`;
- the theorem does not depend on `partial_consistency_payload`, `proof_length`,
  or `strengthened_partial_consistency_payload`.

## Not Claimed

- a printed concrete numeric value of `N`;
- an unconditional proof of the irrationality of Euler's constant;
- a completed clean upstream construction of the half-denominator formula-level
  cutoff.

## Remaining Work

- Clean upstream construction of the half-denominator upper provider.
- Formula-level refinement to
  `17 * (max 3 ((rat.q.den + 1) / 2)) + 8`.
- Decimal numerical extraction after the formula-level and executable threshold
  work is complete.
