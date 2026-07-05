# Project Status

Date: 2026-07-05

## Current Release Target

`v0.1.7-month7-prooflength-frontier-alpha`: interface-level conditional
collision box with Month 7 final theorem compression and proof-length
instantiation boundary metadata.

## Completed at This Stage

- A callable Lean endpoint exists:

```lean
SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
```

- The endpoint concludes:

```lean
¬ is_rational euler_mascheroni
```

- The endpoint is conditional: it requires explicit Sondow-side, Pudlak-side,
  proof-length calibration, and payload-truth inputs.
- The current bridge from project proof-length semantics to exact split
  minChecked witnesses is implemented and checked.
- The public repository separates the Lean code, papers, audit guide, and
  axiom ledger.
- The Month 1 public bridge closure theorem layer exposes a single public
  surface for the CnBox/Pudlak concrete route, paper route, release checkpoint,
  and public-origin equivalences.
- The public layer includes CnBox target/box equation endpoints, code
  roundtrip, PA finite-consistency payload equivalence, same-object closure,
  public gap instantiation, and public collision instantiation.
- Month 3/Month 4 expose the accepted Sondow object, bounded PA proof
  predicate interface, and Pudlak theorem-5 exact external boundary through a
  public completion surface.
- Month 5/Month 6 expose the computable gap certificate and proof-code checker
  calibration frontier.
- Month 7 separates the final contradiction into a proof-length-free
  `GenericRationalCollisionInputs` skeleton and a project proof-length
  instantiation layer.
- Month 7 also exposes `Month7MinimalTheoremSurface`,
  `Month7CompletionChecklist`, `Month7PreMergeAuditCertificate`,
  `Month8ProofLengthResidualFrontier`, and
  `Month8PayloadLiteratureResidualFrontier`.

## Not Claimed

- No unconditional proof of \(\gamma\notin\mathbb Q\) is claimed.
- No internal proof of Pudlak theorem 5 is claimed.
- No complete internal construction of PA proof length is claimed.
- No claim is made that the Month 7 project instantiation has eliminated the
  `proof_length`, payload-truth, or Pudlak literature residuals.  It isolates
  them into the Month 8 residual frontiers.
- No claim is made that natural Sondow certificates themselves already have a
  known Pudlak/Friedman/Buss lower bound.

## Next Research Targets

1. Eliminate or internalize `Month8ProofLengthResidualFrontier` by replacing
   abstract proof-length instantiation with concrete checker exactness,
   proof-object encoding, and minProofCodeSize calibration.
2. Replace payload-truth axioms by structured certificate inputs.
3. Internalize or cite a precise Pudlak theorem 5 instance matching the local
   formula family and scale.
4. Expand the Sondow analytic and verification bridges.
5. Instantiate the final project gap element and parameter-free Sondow verifier
   inside the existing Month 1 public bridge closure interface.
