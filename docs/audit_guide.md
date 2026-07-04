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
