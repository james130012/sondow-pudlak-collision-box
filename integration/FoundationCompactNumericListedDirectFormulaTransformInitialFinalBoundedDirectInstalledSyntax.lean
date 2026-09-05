import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFreeVariables

/-! # Installed formula for the thirty-one endpoint witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPreparedTerminal

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax

def compactFormulaTransformInitialFinalBoundedDirectZeroValuation : Nat -> Nat :=
  fun _ => 0

def compactFormulaTransformInitialFinalBoundedDirectInstalledFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    ValuationFormula :=
  compactFormulaTransformInitialFinalBoundedDirectRawTerminal tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity ⇜
    fun coordinate => shortBinaryNumeralTerm
      (compactFormulaTransformInitialFinalBoundedDirectWitnessValues witness
        coordinate)

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPreparedTerminal
