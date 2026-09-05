import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFullyFixedDirectBound

/-! # Fixed public terminal for the thirty-one bounded endpoint witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectTerminal

open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedSyntaxBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFullyFixedDirectBound
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectData
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPublicBoundsSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectPublicBounds

def compactFormulaTransformInitialFinalBoundedDirectTerminalPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat) :
    Nat :=
  let numericBound :=
    compactFormulaTransformInitialFinalBoundedDirectNumericBound tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound
  let bitBound :=
    compactFormulaTransformInitialFinalBoundedDirectBitBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound
  formulaTransformInitialFinalRowsFullyFixedPayloadPolynomial stateCount fuel
    tokenCount numericBound bitBound

noncomputable def formulaTransformInitialFinalBoundedDirectTerminalOfData
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (data : FormulaTransformInitialFinalBoundedDirectData tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound) :
    ParserInitialFinalClosedDirectBound
      (compactFormulaTransformInitialFinalRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity data.witness)
      (compactFormulaTransformInitialFinalBoundedDirectTerminalPayloadEnvelope
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound) := by
  let numericBound :=
    compactFormulaTransformInitialFinalBoundedDirectNumericBound tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound
  let bitBound :=
    compactFormulaTransformInitialFinalBoundedDirectBitBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound
  simpa only [
    compactFormulaTransformInitialFinalBoundedDirectTerminalPayloadEnvelope,
    numericBound, bitBound] using
    compactFormulaTransformInitialFinalRowsClosedDirectBoundOfGraph tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity numericBound bitBound data.witness
      data.graph
      (formulaTransformInitialFinalBoundedDirectData_valueBound tokenTable
        width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound data)
      (formulaTransformInitialFinalBoundedDirectData_sizeBound tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound data)
      (compactFormulaTransformInitialFinalBoundedDirectNumericSize_le_bitBound
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound)
      (compactFormulaTransformInitialFinalBoundedDirectNumeric_le_bitBound
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound)
      (formulaTransformInitialFinalBoundedDirectData_finalTasksFinishSucc
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound data)
      (compactFormulaTransformInitialFinalBoundedDirectBitBound_positive
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound)

#print axioms formulaTransformInitialFinalBoundedDirectTerminalOfData

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectTerminal
