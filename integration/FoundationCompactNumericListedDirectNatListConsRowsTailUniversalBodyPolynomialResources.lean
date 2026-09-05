import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyDefinitions
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds

/-! # Polynomial resources for closing the cons-tail witnesses -/

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyPolynomialResources

open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailSourceTerminalSyntaxUniformBound

def natListConsRowsTailBodyAfter04FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 4 numericBound
    (natListConsRowsTailSourceTerminalFormulaCodePolynomial bitBound)

def natListConsRowsTailBodyAfter03FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
    (natListConsRowsTailBodyAfter04FormulaCodePolynomial numericBound bitBound)

def natListConsRowsTailBodyAfter02FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
    (natListConsRowsTailBodyAfter03FormulaCodePolynomial numericBound bitBound)

def natListConsRowsTailUniversalBodyFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
    (natListConsRowsTailBodyAfter02FormulaCodePolynomial numericBound bitBound)

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyPolynomialResources
