# Project Status

Date: 2026-07-04

## Current Release Target

`v0.1.3-public-bridge-alpha`: interface-level conditional collision box with
Month 1 public bridge closure metadata.

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

## Not Claimed

- No unconditional proof of \(\gamma\notin\mathbb Q\) is claimed.
- No internal proof of Pudlak theorem 5 is claimed.
- No complete internal construction of PA proof length is claimed.
- No claim is made that natural Sondow certificates themselves already have a
  known Pudlak/Friedman/Buss lower bound.

## Next Research Targets

1. Replace payload-truth axioms by structured certificate inputs.
2. Internalize or cite a precise Pudlak theorem 5 instance matching the local
   formula family and scale.
3. Replace abstract `proof_length` assumptions by a concrete PA/Hilbert
   checked-code proof-length convention.
4. Expand the Sondow analytic and verification bridges.
5. Instantiate the final project gap element and parameter-free Sondow verifier
   inside the existing Month 1 public bridge closure interface.
