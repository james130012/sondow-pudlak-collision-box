import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPreparedTerminalCore

/-! # Context-code bound for the prepared endpoint terminal -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPreparedTerminal

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFreeVariables

theorem compactFormulaTransformInitialFinalBoundedDirectRawContextCode_le_zero
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    formulaCodeSum
      (valuationContext
        (compactFormulaTransformInitialFinalBoundedDirectRawTerminal tokenTable
          width tokenCount stateBoundary stateCount fuel inputBoundary
          inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity).freeVariables
        compactFormulaTransformInitialFinalBoundedDirectZeroValuation) <= 0 := by
  rw [compactFormulaTransformInitialFinalBoundedDirectRawTerminal_freeVariables_eq_empty]
  simp [valuationContext, formulaCodeSum]

#print axioms
  compactFormulaTransformInitialFinalBoundedDirectRawContextCode_le_zero

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPreparedTerminal
