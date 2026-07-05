# Audit Guide

This guide explains how to inspect the public conditional collision endpoint.

## 1. Probe the Public Surface

For routine audits, start with lightweight Lean probes.  They use the same
elaborator and typechecker as `lake build`, but they avoid starting a long
full build.

```bash
lake env lean -o bounded_arithmetic_lab/.lake/build/lib/lean/BoundedArithmeticLab.olean bounded_arithmetic_lab/BoundedArithmeticLab.lean
lake env lean --stdin <<'EOF'
import BoundedArithmeticLab.PublicCollisionExportSurface
open BoundedArithmeticLab
#check PublicCollisionExportSurface.collision
#check PublicCollisionAPI.collision_from_checklist
EOF
```

## 2. Build the Core Files

The full build is a heavier final check:

```bash
lake build EulerLimit.StrengthenedConsistency
lake build EulerLimit.ProjectionBridge
lake build integration.SondowProjectPudlakInstantiation
```

## 3. Check the Main Endpoint

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakInstantiation

#check SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
EOF
```

Expected conclusion:

```lean
¬ is_rational euler_mascheroni
```

## 3a. Check the Month 1 Public Bridge Closure Surface

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface
open SondowMainCheckedCodeBridge.SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface

#check Month1PublicBridgeClosureTheoremLayer
#check Month1PublicBridgeClosureTheoremLayer.concrete_iff_public_origin
#check Month1PublicBridgeClosureTheoremLayer.target_eq_box_formula
#check Month1PublicBridgeClosureTheoremLayer.carries_iff_pa_finite_consistency
#check Month1PublicBridgeClosureTheoremLayer.public_gap_instantiation
#check Month1PublicBridgeClosureTheoremLayer.public_collision_instantiation
EOF
```

This surface is the public same-object and CnBox/Pudlak bridge closure layer.
It is not a replacement for Pudlak theorem 5 or for the final parameter-free
Sondow verifier.

## 3b. Check the Month 7 Final Theorem Compression Surface

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectMonth7FinalCollisionSurface
open SondowMainCheckedCodeBridge.SondowProjectMonth7FinalCollisionSurface

#check SondowMainCheckedCodeBridge.GenericRationalCollisionInputs.not_rational
#check Month7MinimalTheoremSurface.not_rational
#check Month7PreMergeAuditCertificate.nonempty_iff_literature_frontier_vector_nonempty
#check month7_minimal_theorem_surface_nonempty_iff_month8_residual_frontiers_nonempty
#print axioms SondowMainCheckedCodeBridge.GenericRationalCollisionInputs.not_rational
#print axioms Month7PreMergeAuditCertificate.not_rational
EOF
```

The generic skeleton should not depend on `proof_length`.  The project
instantiation layer should still expose the proof-length, payload, and
literature residuals.

## 4. Print Axiom Dependencies

```bash
lake env lean --stdin <<'EOF'
import integration.SondowProjectPudlakInstantiation

#print axioms SondowMainCheckedCodeBridge.callCollisionBox_from_semanticConventionViaExactSplit
EOF
```

The output should be compared against `AXIOM_LEDGER.md`.

## 5. What to Look For

- Does the theorem type expose its input packages?
- Does `#print axioms` include the expected external Pudlak and proof-length
  dependencies?
- Are the Sondow upper side and Pudlak lower side stated over the same
  `FormulaCode`, `ProofSystem.PA`, and `ProofLengthMeasure.symbolSize`
  coordinate?
- Does any statement claim an unconditional proof of gamma irrationality?

If a theorem removes inputs without also removing their corresponding axiom
dependencies, it should not be cited as a closed result.
