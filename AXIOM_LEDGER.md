# Axiom Ledger

This file records the assumptions that matter for the public collision
endpoint.  It is part of the scientific boundary of this repository.

## Main Endpoint

```lean
SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
```

## Audit Command

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakInstantiation

#print axioms SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
EOF
```

## Month 7 Audit Commands

The Month 7 final theorem compression layer separates the proof-length-free
generic collision skeleton from the project instantiation layer:

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth7FinalCollisionSurface
open SondowMainCheckedCodeBridge.SondowProjectMonth7FinalCollisionSurface

#print axioms SondowMainCheckedCodeBridge.GenericRationalCollisionInputs.not_rational
#print axioms Month7MinimalTheoremSurface.not_rational
#print axioms Month7PreMergeAuditCertificate.not_rational
EOF
```

## Current Core Dependencies

The current callable endpoint depends on these project-level external or
abstract inputs:

```text
literaturePudlakTheorem5ExternalRescaledLowerBound
literaturePudlakTheorem5ExternalScaleData
proof_length
partial_consistency_payload
strengthened_partial_consistency_payload
```

It also uses standard Lean/Mathlib principles such as:

```text
propext
Classical.choice
Quot.sound
```

## Interpretation

- `literaturePudlakTheorem5ExternalRescaledLowerBound` and
  `literaturePudlakTheorem5ExternalScaleData` are the external Pudlak theorem 5
  inputs.
- `proof_length` is the abstract project-level proof-length function.
- `partial_consistency_payload` and `strengthened_partial_consistency_payload`
  are payload vocabularies.  Their intended truth must be supplied through
  explicit inputs, not inferred for free.

The repository therefore proves an interface-level conditional theorem, not an
unconditional theorem in bare Lean.

## Month 7 Interpretation

`GenericRationalCollisionInputs.not_rational` is the proof-length-free generic
collision skeleton.  Its axiom audit should not contain `proof_length`.

`Month7MinimalTheoremSurface.not_rational` and
`Month7PreMergeAuditCertificate.not_rational` instantiate that skeleton with
the project-local proof-length box and the remaining payload/literature
certificates.  Their axiom audits still contain `proof_length`,
`partial_consistency_payload`, and `strengthened_partial_consistency_payload`.

The remaining project obligations have been split into:

```text
Month8ProofLengthResidualFrontier
Month8PayloadLiteratureResidualFrontier
```

This is a compression and localization of the residual assumptions, not their
unconditional elimination.
