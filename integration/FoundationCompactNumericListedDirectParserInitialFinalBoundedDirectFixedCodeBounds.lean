import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectStructuralCompiler
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds

/-! # Fixed code envelope for the bounded parser endpoint terminal -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFixedCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTerminalSubstitution

def compactParserInitialFinalBoundedDirectRawTerminalFixedCodeEnvelope
    (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 23
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      compactParserInitialFinalBoundedDirectSourceRawTerminal).length

private theorem
    compactParserInitialFinalBoundedDirectPublicTerms_code_length_le
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount bitBound : Nat)
    (htokenTable : Nat.size tokenTable ≤ bitBound)
    (hwidth : Nat.size width ≤ bitBound)
    (htokenCount : Nat.size tokenCount ≤ bitBound)
    (hstateBoundary : Nat.size stateBoundary ≤ bitBound)
    (hstateCount : Nat.size stateCount ≤ bitBound)
    (hfuel : Nat.size fuel ≤ bitBound)
    (hinputBoundary : Nat.size inputBoundary ≤ bitBound)
    (hinputCount : Nat.size inputCount ≤ bitBound)
    (hexpectedBoundary : Nat.size expectedBoundary ≤ bitBound)
    (hexpectedCount : Nat.size expectedCount ≤ bitBound)
    (htaskKind : Nat.size taskKind ≤ bitBound)
    (htaskBinderArity : Nat.size taskBinderArity ≤ bitBound)
    (htaskRepeatCount : Nat.size taskRepeatCount ≤ bitBound)
    (coordinate : Fin 13) :
    (binaryTermCode
      (compactParserInitialFinalBoundedDirectPublicTerms tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount coordinate)).length ≤
      binaryNumeralTermCodeEnvelope bitBound := by
  fin_cases coordinate
  · exact binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
      htokenTable
  · exact binaryNumeralTerm_code_length_le_envelope width bitBound hwidth
  · exact binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
      htokenCount
  · exact binaryNumeralTerm_code_length_le_envelope stateBoundary bitBound
      hstateBoundary
  · exact binaryNumeralTerm_code_length_le_envelope stateCount bitBound
      hstateCount
  · exact binaryNumeralTerm_code_length_le_envelope fuel bitBound hfuel
  · exact binaryNumeralTerm_code_length_le_envelope inputBoundary bitBound
      hinputBoundary
  · exact binaryNumeralTerm_code_length_le_envelope inputCount bitBound
      hinputCount
  · exact binaryNumeralTerm_code_length_le_envelope expectedBoundary bitBound
      hexpectedBoundary
  · exact binaryNumeralTerm_code_length_le_envelope expectedCount bitBound
      hexpectedCount
  · exact binaryNumeralTerm_code_length_le_envelope taskKind bitBound
      htaskKind
  · exact binaryNumeralTerm_code_length_le_envelope taskBinderArity bitBound
      htaskBinderArity
  · exact binaryNumeralTerm_code_length_le_envelope taskRepeatCount bitBound
      htaskRepeatCount

theorem compactParserInitialFinalBoundedDirectSourceTerms_code_length_le
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound bitBound : Nat)
    (htokenTable : Nat.size tokenTable ≤ bitBound)
    (hwidth : Nat.size width ≤ bitBound)
    (htokenCount : Nat.size tokenCount ≤ bitBound)
    (hstateBoundary : Nat.size stateBoundary ≤ bitBound)
    (hstateCount : Nat.size stateCount ≤ bitBound)
    (hfuel : Nat.size fuel ≤ bitBound)
    (hinputBoundary : Nat.size inputBoundary ≤ bitBound)
    (hinputCount : Nat.size inputCount ≤ bitBound)
    (hexpectedBoundary : Nat.size expectedBoundary ≤ bitBound)
    (hexpectedCount : Nat.size expectedCount ≤ bitBound)
    (htaskKind : Nat.size taskKind ≤ bitBound)
    (htaskBinderArity : Nat.size taskBinderArity ≤ bitBound)
    (htaskRepeatCount : Nat.size taskRepeatCount ≤ bitBound)
    (hvalueBound : Nat.size valueBound ≤ bitBound) :
    ∀ coordinate,
      (binaryTermCode
        (compactParserInitialFinalBoundedDirectSourceTerms tokenTable width
          tokenCount stateBoundary stateCount fuel inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount valueBound coordinate)).length ≤
        binaryNumeralTermCodeEnvelope bitBound := by
  intro coordinate
  unfold compactParserInitialFinalBoundedDirectSourceTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · let publicCoordinate : Fin 13 := ⟨coordinate, hcoordinate⟩
    change
      (binaryTermCode
        (compactParserInitialFinalBoundedDirectPublicTerms tokenTable width
          tokenCount stateBoundary stateCount fuel inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount publicCoordinate)).length ≤
        binaryNumeralTermCodeEnvelope bitBound
    exact
      compactParserInitialFinalBoundedDirectPublicTerms_code_length_le
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount bitBound htokenTable hwidth
        htokenCount hstateBoundary hstateCount hfuel hinputBoundary
        hinputCount hexpectedBoundary hexpectedCount htaskKind
        htaskBinderArity htaskRepeatCount publicCoordinate
  · let boundCoordinate : Fin 1 := ⟨coordinate - 13, by omega⟩
    change
      (binaryTermCode
        (![shortBinaryNumeralTerm valueBound] boundCoordinate)).length ≤
        binaryNumeralTermCodeEnvelope bitBound
    simpa using
      binaryNumeralTerm_code_length_le_envelope valueBound bitBound
        hvalueBound

theorem
    compactParserInitialFinalBoundedDirectRawTerminal_code_length_le_fixed
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound bitBound : Nat)
    (htokenTable : Nat.size tokenTable ≤ bitBound)
    (hwidth : Nat.size width ≤ bitBound)
    (htokenCount : Nat.size tokenCount ≤ bitBound)
    (hstateBoundary : Nat.size stateBoundary ≤ bitBound)
    (hstateCount : Nat.size stateCount ≤ bitBound)
    (hfuel : Nat.size fuel ≤ bitBound)
    (hinputBoundary : Nat.size inputBoundary ≤ bitBound)
    (hinputCount : Nat.size inputCount ≤ bitBound)
    (hexpectedBoundary : Nat.size expectedBoundary ≤ bitBound)
    (hexpectedCount : Nat.size expectedCount ≤ bitBound)
    (htaskKind : Nat.size taskKind ≤ bitBound)
    (htaskBinderArity : Nat.size taskBinderArity ≤ bitBound)
    (htaskRepeatCount : Nat.size taskRepeatCount ≤ bitBound)
    (hvalueBound : Nat.size valueBound ≤ bitBound) :
    (binaryFormulaCode
      (compactParserInitialFinalBoundedDirectRawTerminal tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount)).length ≤
      compactParserInitialFinalBoundedDirectRawTerminalFixedCodeEnvelope
        bitBound := by
  rw [←
    compactParserInitialFinalBoundedDirectSourceRawTerminal_rewriting
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound]
  exact
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      23 (binaryNumeralTermCodeEnvelope bitBound)
      (binaryFormulaCode
        compactParserInitialFinalBoundedDirectSourceRawTerminal).length
      (compactParserInitialFinalBoundedDirectSourceTerms tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound)
      compactParserInitialFinalBoundedDirectSourceRawTerminal
      (compactParserInitialFinalBoundedDirectSourceTerms_code_length_le
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount valueBound bitBound htokenTable hwidth
        htokenCount hstateBoundary hstateCount hfuel hinputBoundary
        hinputCount hexpectedBoundary hexpectedCount htaskKind
        htaskBinderArity htaskRepeatCount hvalueBound)
      le_rfl

#print axioms
  compactParserInitialFinalBoundedDirectSourceTerms_code_length_le
#print axioms
  compactParserInitialFinalBoundedDirectRawTerminal_code_length_le_fixed

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFixedCodeBounds
