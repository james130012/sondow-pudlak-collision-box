# Current Formal Status

The public repository freezes the interface-level state of the project.

## Reproducible Checkpoint

The release `fcce697-symbolic-collision-checkpoint` is the current public
symbolic-collision checkpoint. It is pinned to commit
`fcce697c60adfe87d4d33515ff965322962fc994`.

What it demonstrates:

- `checked_lower` is routed to the no-fallback target `bigN` certificate.
- The same symbolic `bigN` carries `upper.U bigN < measured bigN`,
  `measured bigN <= upper.U bigN`, and therefore `False`.
- The checkpoint is reproducible by checking
  `integration/SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint.lean`.

What it does not claim:

- It does not compute a concrete numeric value of `N`.
- It is not an unconditional proof of the irrationality of Euler's constant.

## Closed Interface Work

- The Sondow/Pudlak collision endpoint is callable.
- A formal/symbolic collision checkpoint is pinned and released at
  `fcce697-symbolic-collision-checkpoint`.
- Exact strengthened-family lengths can be connected to project proof-length
  semantics.
- Partial-consistency and reflection-graft minChecked exactness are split into
  separate certificates.
- Semantic proof-length convention inputs can be converted into the exact split
  minChecked collision input.
- The Month 7 final theorem surface separates the proof-length-free
  `GenericRationalCollisionInputs` skeleton from the project proof-length
  instantiation layer.
- The Month 7 pre-merge audit certificate relates the public residual inputs,
  the minimal theorem surface, and the Month 8 residual frontier.

## Open Internalization Work

- Internal Pudlak theorem 5 lower bound.
- Internal PA/Hilbert proof-length convention.
- Internal Sondow parameter-free verifier and infrastructure package.
- Structured replacement for payload-truth axioms.
- Elimination or internalization of `Month8ProofLengthResidualFrontier`.
- Elimination or internalization of `Month8PayloadLiteratureResidualFrontier`.
