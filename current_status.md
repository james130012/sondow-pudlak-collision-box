# Current Formal Status

The current public artifact is a Lean-checked Sondow-Pudlak symbolic collision
checkpoint. It should be read as a reproducible formal certificate for the
same-`bigN` collision core, not as a final unconditional proof of the
irrationality of Euler's constant.

## Reproducible Checkpoint

The release `fcce697-symbolic-collision-checkpoint` is pinned to commit
`fcce697c60adfe87d4d33515ff965322962fc994`.

It demonstrates:

- The checked lower-bound route reaches the fallback-free target-upper `bigN`
  certificate.
- The same symbolic `bigN` carries both
  `upper.U bigN < measured bigN` and `measured bigN <= upper.U bigN`.
- The Lean certificate therefore derives `False` at that same `bigN`.
- The follow-up normal form identifies the computation target as the rejection
  extractor witness at threshold `0`.

It does not claim:

- a printed concrete numeric value of `N`;
- an unconditional proof of the irrationality of Euler's constant;
- a parameter-free internal construction of every Sondow/Pudlak input.

## Closed Formal Work

- The formal collision kernel is callable and reproducible.
- The checked lower-bound input is connected to the no-fallback target-upper
  route.
- The target `bigN` is identified with
  `rejectionExtractor.witness upper.U upper.polynomial 0`.
- The contradiction package contains the two opposite inequalities and `False`
  for one shared witness.
- The project has separated the public collision kernel from the
  project-specific checker/project-length instantiation layer.

## Remaining Work

- Numeric extraction of the concrete natural number `N`.
- Parameter-free construction or exact citation of the external Sondow and
  Pudlak mathematical inputs used by the checked-lower interface.
- Internal or fully audited treatment of the payload semantics.
- Publication-grade appendices for theorem names, axiom audits, release tags,
  and reproduction commands.
