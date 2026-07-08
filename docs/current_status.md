# Current Formal Status

The current public artifact is a Lean-checked Sondow-Pudlak collision route
with the two earlier public parameters `upper_provider` and `tail_gap` pushed
upstream.  It should be read as a reproducible formal certificate for the
formula-level threshold

```lean
bigN = thresholdOfMonomial upper_data.coeff upper_data.degree
```

under the displayed monomial growth input for `minCheckedCodeSize`, not as a
final unconditional proof of the irrationality of Euler's constant and not as a
decimal extraction of `N`.

## Reproducible Checkpoint

The audited release is `bigN-halfden-full-20260708`, pinned to commit:

```text
2a7458c253aae4050a0a3a18424abea952d26bc3
```

The current submission theorem is:

```lean
singletonMonomialLowerBound_submissionRoute
```

defined in:

```text
integration/SondowProjectBigNParameterClosureAudit.lean
```

It demonstrates:

- the public theorem surface no longer exposes `upper_provider`, `tail_gap`, or
  `eventually_strict_length`;
- the certified collision index is
  `thresholdOfMonomial upper_data.coeff upper_data.degree`;
- the route derives the formal collision contradiction from the monomial
  growth input;
- the audited axiom profile is `[propext, Classical.choice, Quot.sound]`;
- the theorem does not depend on `partial_consistency_payload`, `proof_length`,
  or `strengthened_partial_consistency_payload`.

## Not Claimed

- a printed concrete numeric value of `N`;
- an unconditional proof of the irrationality of Euler's constant;
- a completed clean upstream construction of the half-denominator formula-level
  cutoff.

## Remaining Work

- Close the monomial growth theorem
  `thresholdOfMonomial coeff degree <= n ->
    coeff * (n + 1)^degree < minCheckedCodeSize n`.
- Clean upstream construction of the old half-denominator upper provider, if
  the half-denominator formula is needed later.
- Decimal numerical extraction after the formula-level and executable threshold
  work is complete.
