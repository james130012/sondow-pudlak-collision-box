import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFixedCodeBounds
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment
import integration.FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds

/-! # Fixed code envelope for the exact-fuel endpoint terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFixedCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment
open FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds

def compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope
    (numericBound bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound + 1

def compactParserInitialFinalBoundedExactFuelDirectRawTerminalFixedCodeEnvelope
    (numericBound bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 23
    (compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope numericBound
      bitBound)
    (binaryFormulaCode
      compactParserInitialFinalBoundedDirectSourceRawTerminal).length

private theorem
    compactParserInitialFinalBoundedExactFuelDirectPublicTerms_code_length_le
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hstateBoundary : Nat.size stateBoundary <= bitBound)
    (hstateCount : Nat.size stateCount <= bitBound)
    (hinputBoundary : Nat.size inputBoundary <= bitBound)
    (hinputCountSize : Nat.size inputCount <= bitBound)
    (hinputCountValue : inputCount <= numericBound)
    (hexpectedBoundary : Nat.size expectedBoundary <= bitBound)
    (hexpectedCount : Nat.size expectedCount <= bitBound)
    (htaskKind : Nat.size taskKind <= bitBound)
    (htaskBinderArity : Nat.size taskBinderArity <= bitBound)
    (htaskRepeatCount : Nat.size taskRepeatCount <= bitBound)
    (coordinate : Fin 13) :
    (binaryTermCode
      (compactParserInitialFinalBoundedExactFuelDirectPublicTerms tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
        coordinate)).length <=
      compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope
        numericBound bitBound := by
  have hnumeral (value : Nat) (hvalue : Nat.size value <= bitBound) :
      (binaryTermCode (shortBinaryNumeralTerm value : ValuationTerm)).length <=
        compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope
          numericBound bitBound := by
    exact (binaryNumeralTerm_code_length_le_envelope value bitBound hvalue).trans
      (by
        unfold
          compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope
        omega)
  fin_cases coordinate
  · exact hnumeral tokenTable htokenTable
  · exact hnumeral width hwidth
  · exact hnumeral tokenCount htokenCount
  · exact hnumeral stateBoundary hstateBoundary
  · exact hnumeral stateCount hstateCount
  · exact
      (compactParserSyntaxExactFuelTerm_code_length_le_fixed inputCount
        numericBound hinputCountValue).trans (by
          unfold
            compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope
          omega)
  · exact hnumeral inputBoundary hinputBoundary
  · exact hnumeral inputCount hinputCountSize
  · exact hnumeral expectedBoundary hexpectedBoundary
  · exact hnumeral expectedCount hexpectedCount
  · exact hnumeral taskKind htaskKind
  · exact hnumeral taskBinderArity htaskBinderArity
  · exact hnumeral taskRepeatCount htaskRepeatCount

theorem
    compactParserInitialFinalBoundedExactFuelDirectSourceTerms_code_length_le
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound numericBound bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hstateBoundary : Nat.size stateBoundary <= bitBound)
    (hstateCount : Nat.size stateCount <= bitBound)
    (hinputBoundary : Nat.size inputBoundary <= bitBound)
    (hinputCountSize : Nat.size inputCount <= bitBound)
    (hinputCountValue : inputCount <= numericBound)
    (hexpectedBoundary : Nat.size expectedBoundary <= bitBound)
    (hexpectedCount : Nat.size expectedCount <= bitBound)
    (htaskKind : Nat.size taskKind <= bitBound)
    (htaskBinderArity : Nat.size taskBinderArity <= bitBound)
    (htaskRepeatCount : Nat.size taskRepeatCount <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    forall coordinate,
      (binaryTermCode
        (compactParserInitialFinalBoundedExactFuelDirectSourceTerms tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount valueBound coordinate)).length <=
        compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope
          numericBound bitBound := by
  intro coordinate
  unfold compactParserInitialFinalBoundedExactFuelDirectSourceTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · let publicCoordinate : Fin 13 := ⟨coordinate, hcoordinate⟩
    change
      (binaryTermCode
        (compactParserInitialFinalBoundedExactFuelDirectPublicTerms tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount publicCoordinate)).length <= _
    exact
      compactParserInitialFinalBoundedExactFuelDirectPublicTerms_code_length_le
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount numericBound bitBound htokenTable hwidth htokenCount
        hstateBoundary hstateCount hinputBoundary hinputCountSize
        hinputCountValue hexpectedBoundary hexpectedCount htaskKind
        htaskBinderArity htaskRepeatCount publicCoordinate
  · let boundCoordinate : Fin 1 := ⟨coordinate - 13, by omega⟩
    change
      (binaryTermCode
        (![shortBinaryNumeralTerm valueBound] boundCoordinate)).length <=
          compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope
            numericBound bitBound
    have hcode := binaryNumeralTerm_code_length_le_envelope valueBound bitBound
      hvalueBound
    have hceiling : binaryNumeralTermCodeEnvelope bitBound <=
        compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope
          numericBound bitBound := by
      unfold compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope
      omega
    have hzero : boundCoordinate = 0 := Fin.eq_zero boundCoordinate
    rw [hzero]
    exact hcode.trans hceiling

theorem
    compactParserInitialFinalBoundedExactFuelDirectRawTerminal_code_length_le_fixed
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound numericBound bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hstateBoundary : Nat.size stateBoundary <= bitBound)
    (hstateCount : Nat.size stateCount <= bitBound)
    (hinputBoundary : Nat.size inputBoundary <= bitBound)
    (hinputCountSize : Nat.size inputCount <= bitBound)
    (hinputCountValue : inputCount <= numericBound)
    (hexpectedBoundary : Nat.size expectedBoundary <= bitBound)
    (hexpectedCount : Nat.size expectedCount <= bitBound)
    (htaskKind : Nat.size taskKind <= bitBound)
    (htaskBinderArity : Nat.size taskBinderArity <= bitBound)
    (htaskRepeatCount : Nat.size taskRepeatCount <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    (binaryFormulaCode
      (compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount)).length <=
      compactParserInitialFinalBoundedExactFuelDirectRawTerminalFixedCodeEnvelope
        numericBound bitBound := by
  rw [<-
    compactParserInitialFinalBoundedExactFuelDirectSourceRawTerminal_rewriting
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound]
  exact
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      23
      (compactParserInitialFinalBoundedExactFuelDirectTermCodeEnvelope
        numericBound bitBound)
      (binaryFormulaCode
        compactParserInitialFinalBoundedDirectSourceRawTerminal).length
      (compactParserInitialFinalBoundedExactFuelDirectSourceTerms tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
        valueBound)
      compactParserInitialFinalBoundedDirectSourceRawTerminal
      (compactParserInitialFinalBoundedExactFuelDirectSourceTerms_code_length_le
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound numericBound bitBound htokenTable hwidth
        htokenCount hstateBoundary hstateCount hinputBoundary hinputCountSize
        hinputCountValue hexpectedBoundary hexpectedCount htaskKind
        htaskBinderArity htaskRepeatCount hvalueBound)
      le_rfl

#print axioms
  compactParserInitialFinalBoundedExactFuelDirectSourceTerms_code_length_le
#print axioms
  compactParserInitialFinalBoundedExactFuelDirectRawTerminal_code_length_le_fixed

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFixedCodeBounds
