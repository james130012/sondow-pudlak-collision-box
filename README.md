# Sondow-Pudlak Conditional Collision Box

This repository is a Lean 4 research artifact for a conditional
proof-complexity collision framework around the Euler-Mascheroni constant
\(\gamma\).

**Status.** This repository does **not** contain an unconditional proof of the
irrationality of \(\gamma\).  The current strongest endpoint is an
interface-level conditional collision theorem: under explicitly listed Sondow,
Pudlak-Friedman-Buss, proof-length calibration, and payload-truth inputs, the
Lean composition derives

```lean
¬ is_rational euler_mascheroni
```

The goal of this project is to make the remaining mathematical and
proof-complexity obligations explicit, not to hide them behind successful
compilation.

## Main Entry Points

- Paper, English: [`paper/paper_new_en.md`](paper/paper_new_en.md)
- Paper, Chinese: [`paper/paper_new_zh.md`](paper/paper_new_zh.md)
- Current status: [`STATUS.md`](STATUS.md)
- Axiom ledger: [`AXIOM_LEDGER.md`](AXIOM_LEDGER.md)
- Audit guide: [`docs/audit_guide.md`](docs/audit_guide.md)
- Main callable collision endpoint:

```lean
SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
```

The endpoint is defined in:

```text
integration/SondowProjectPudlakInstantiation.lean
```

## Build

The repository is pinned to Lean `v4.31.0`.

```bash
lake exe cache get
lake build EulerLimit.StrengthenedConsistency
lake build EulerLimit.ProjectionBridge
lake build integration.SondowProjectPudlakInstantiation
```

After these modules have been built, source-file probes such as

```bash
lake env lean integration/SondowProjectPudlakInstantiation.lean
```

are also expected to work.

## Audit

Before citing an endpoint as fully formalized, inspect its assumptions:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakInstantiation

#check SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
#print axioms SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
EOF
```

The expected core external or abstract inputs are listed in
[`AXIOM_LEDGER.md`](AXIOM_LEDGER.md).

## What Is Formalized

- Formula families are organized through `FormulaCode`.
- The common proof system is `ProofSystem.PA`.
- The proof-length measure is `ProofLengthMeasure.symbolSize`.
- The collision endpoint is callable and returns the intended irrationality
  conclusion under explicit inputs.
- The bridge from semantic proof-length conventions to exact split minChecked
  witnesses is machine checked.

## What Is Not Yet Internalized

- Pudlak theorem 5 / Pudlak-Friedman-Buss finite-consistency proof-length
  lower bounds.
- A from-scratch PA/Hilbert proof-length convention.
- The full Sondow analytic package and short-verification theorem inside Lean.
- Payload truth for the finite-consistency/reflection content.

## License

Code is released under Apache-2.0.  Paper text and documentation are intended
to be cited with attribution; see [`CITATION.cff`](CITATION.cff).
