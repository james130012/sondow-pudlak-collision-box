import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedProof
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData

/-! # Six fully fixed open-index table-entry leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedLeaves

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFixedBounds
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedProof

def compactSequentFormulaStepOpenEntryNumericBound
    (numericBound tokenCount valueBound : Nat) : Nat :=
  numericBound + tokenCount + valueBound + 2

def compactSequentFormulaStepOpenEntryBitBound
    (numericBound bitBound tokenCount valueBound : Nat) : Nat :=
  bitBound + Nat.size
    (compactSequentFormulaStepOpenEntryNumericBound numericBound tokenCount
      valueBound)

def compactSequentFormulaStepOpenEntryIndexCodeBound : Nat :=
  (binaryTermCode (&0 : ValuationTerm)).length +
    (binaryTermCode
      (compactSequentFormulaStepIndexSuccessorTermAtValuation
        (&0 : ValuationTerm))).length +
    (binaryTermCode
      (compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
        (&0 : ValuationTerm))).length

def compactSequentFormulaStepOpenEntryFullyFixedPayload
    (numericBound bitBound tokenCount valueBound : Nat) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayloadPolynomial
    (compactSequentFormulaStepOpenEntryNumericBound numericBound tokenCount
      valueBound)
    (compactSequentFormulaStepOpenEntryBitBound numericBound bitBound tokenCount
      valueBound)
    compactSequentFormulaStepOpenEntryIndexCodeBound

structure CompactSequentFormulaStepOpenEntryFullyFixedLeaves
    (tokenCount suffixBoundary valueBoundary : Nat)
    (valuation : Nat -> Nat) (row : CompactSequentFormulaStepCoordinates)
    (resource : Nat) where
  currentStart : ExplicitDirectFormulaBound valuation
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
      (shortBinaryNumeralTerm row.current.start)) resource
  currentFinish : ExplicitDirectFormulaBound valuation
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTermAtValuation
        (&0 : ValuationTerm))
      (shortBinaryNumeralTerm row.current.finish)) resource
  nextStart : ExplicitDirectFormulaBound valuation
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTermAtValuation
        (&0 : ValuationTerm))
      (shortBinaryNumeralTerm row.next.start)) resource
  nextFinish : ExplicitDirectFormulaBound valuation
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
        (&0 : ValuationTerm))
      (shortBinaryNumeralTerm row.next.finish)) resource
  valueStart : ExplicitDirectFormulaBound valuation
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
      (shortBinaryNumeralTerm row.value.start)) resource
  valueFinish : ExplicitDirectFormulaBound valuation
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTermAtValuation
        (&0 : ValuationTerm))
      (shortBinaryNumeralTerm row.value.finish)) resource

noncomputable def compactSequentFormulaStepOpenEntryFullyFixedLeavesOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound)
    (hrowIndex : rowIndex <= numericBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hsuffixBoundary : Nat.size suffixBoundary <= bitBound)
    (hvalueBoundary : Nat.size valueBoundary <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    CompactSequentFormulaStepOpenEntryFullyFixedLeaves tokenCount suffixBoundary
      valueBoundary (extendValuation rowIndex zeroValuation) data.row
      (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
        tokenCount valueBound) := by
  let valuation := extendValuation rowIndex zeroValuation
  let indexTerm : ValuationTerm := &0
  let successorIndexTerm :=
    compactSequentFormulaStepIndexSuccessorTermAtValuation indexTerm
  let secondSuccessorIndexTerm :=
    compactSequentFormulaStepIndexSecondSuccessorTermAtValuation indexTerm
  let entryNumeric := compactSequentFormulaStepOpenEntryNumericBound numericBound
    tokenCount valueBound
  let entryBit := compactSequentFormulaStepOpenEntryBitBound numericBound bitBound
    tokenCount valueBound
  let indexCode := compactSequentFormulaStepOpenEntryIndexCodeBound
  have hcurrentStartValue : data.row.current.start <= valueBound := by
    simpa [compactSequentFormulaStepRowBoundedDirectWitnessValues] using
      data.values_le 17
  have hcurrentFinishValue : data.row.current.finish <= valueBound := by
    simpa [compactSequentFormulaStepRowBoundedDirectWitnessValues] using
      data.values_le 16
  have hnextStartValue : data.row.next.start <= valueBound := by
    simpa [compactSequentFormulaStepRowBoundedDirectWitnessValues] using
      data.values_le 12
  have hnextFinishValue : data.row.next.finish <= valueBound := by
    simpa [compactSequentFormulaStepRowBoundedDirectWitnessValues] using
      data.values_le 11
  have hvalueStartValue : data.row.value.start <= valueBound := by
    simpa [compactSequentFormulaStepRowBoundedDirectWitnessValues] using
      data.values_le 7
  have hvalueFinishValue : data.row.value.finish <= valueBound := by
    simpa [compactSequentFormulaStepRowBoundedDirectWitnessValues] using
      data.values_le 6
  have hrowIndexEntry : rowIndex <= entryNumeric := by
    unfold entryNumeric compactSequentFormulaStepOpenEntryNumericBound
    omega
  have htokenCountEntry : tokenCount <= entryNumeric := by
    unfold entryNumeric compactSequentFormulaStepOpenEntryNumericBound
    omega
  have hvalueBoundEntry : valueBound <= entryNumeric := by
    unfold entryNumeric compactSequentFormulaStepOpenEntryNumericBound
    omega
  have hvaluation : valuation 0 <= entryNumeric := by
    simpa only [valuation, extendValuation_zero] using hrowIndexEntry
  have hindexValue : termValue valuation indexTerm <= entryNumeric := by
    simpa only [valuation, indexTerm,
      termValue_indexTerm_bvarZero_under_extendValuation] using hrowIndexEntry
  have hsuccessorValue : termValue valuation successorIndexTerm <=
      entryNumeric := by
    simp only [valuation, successorIndexTerm, indexTerm,
      compactSequentFormulaStepIndexSuccessorTermAtValuation,
      termValue_indexTerm_bvarZeroAddOne_under_extendValuation]
    unfold entryNumeric compactSequentFormulaStepOpenEntryNumericBound
    omega
  have hsecondSuccessorValue : termValue valuation secondSuccessorIndexTerm <=
      entryNumeric := by
    simp only [valuation, secondSuccessorIndexTerm, indexTerm,
      termValue_compactSequentFormulaStepIndexSecondSuccessorTermAtValuation]
    unfold entryNumeric compactSequentFormulaStepOpenEntryNumericBound
    omega
  have hbitBase : bitBound <= entryBit := by
    unfold entryBit compactSequentFormulaStepOpenEntryBitBound
    omega
  have hentryNumericSize : Nat.size entryNumeric <= entryBit := by
    unfold entryBit compactSequentFormulaStepOpenEntryBitBound
    dsimp only [entryNumeric]
    omega
  have htokenCountSize : Nat.size tokenCount <= entryBit :=
    htokenCount.trans hbitBase
  have hsuffixBoundarySize : Nat.size suffixBoundary <= entryBit :=
    hsuffixBoundary.trans hbitBase
  have hvalueBoundarySize : Nat.size valueBoundary <= entryBit :=
    hvalueBoundary.trans hbitBase
  have hindexSize : Nat.size (termValue valuation indexTerm) <= entryBit :=
    (Nat.size_le_size hindexValue).trans hentryNumericSize
  have hsuccessorSize : Nat.size (termValue valuation successorIndexTerm) <=
      entryBit :=
    (Nat.size_le_size hsuccessorValue).trans hentryNumericSize
  have hsecondSuccessorSize :
      Nat.size (termValue valuation secondSuccessorIndexTerm) <= entryBit :=
    (Nat.size_le_size hsecondSuccessorValue).trans hentryNumericSize
  have hcurrentStartSize : Nat.size data.row.current.start <= entryBit :=
    (Nat.size_le_size hcurrentStartValue).trans (hvalueBound.trans hbitBase)
  have hcurrentFinishSize : Nat.size data.row.current.finish <= entryBit :=
    (Nat.size_le_size hcurrentFinishValue).trans (hvalueBound.trans hbitBase)
  have hnextStartSize : Nat.size data.row.next.start <= entryBit :=
    (Nat.size_le_size hnextStartValue).trans (hvalueBound.trans hbitBase)
  have hnextFinishSize : Nat.size data.row.next.finish <= entryBit :=
    (Nat.size_le_size hnextFinishValue).trans (hvalueBound.trans hbitBase)
  have hvalueStartSize : Nat.size data.row.value.start <= entryBit :=
    (Nat.size_le_size hvalueStartValue).trans (hvalueBound.trans hbitBase)
  have hvalueFinishSize : Nat.size data.row.value.finish <= entryBit :=
    (Nat.size_le_size hvalueFinishValue).trans (hvalueBound.trans hbitBase)
  have hindexCode : (binaryTermCode indexTerm).length <= indexCode := by
    unfold indexTerm indexCode compactSequentFormulaStepOpenEntryIndexCodeBound
    omega
  have hsuccessorCode : (binaryTermCode successorIndexTerm).length <=
      indexCode := by
    unfold successorIndexTerm indexTerm indexCode
      compactSequentFormulaStepOpenEntryIndexCodeBound
    omega
  have hsecondSuccessorCode :
      (binaryTermCode secondSuccessorIndexTerm).length <= indexCode := by
    unfold secondSuccessorIndexTerm indexTerm indexCode
      compactSequentFormulaStepOpenEntryIndexCodeBound
    omega
  have hindexVariables : indexTerm.freeVariables ⊆ {0} := by
    simpa only [indexTerm] using
      compactSequentFormulaStepIndexTerm_freeVariables_subset_singleton
  have hsuccessorVariables : successorIndexTerm.freeVariables ⊆ {0} := by
    simpa only [successorIndexTerm, indexTerm] using
      compactSequentFormulaStepIndexSuccessorTermAtValuation_freeVariables_subset_singleton
  have hsecondSuccessorVariables :
      secondSuccessorIndexTerm.freeVariables ⊆ {0} := by
    simpa only [secondSuccessorIndexTerm, indexTerm] using
      compactSequentFormulaStepIndexSecondSuccessorTermAtValuation_freeVariables_subset_singleton
  rcases data.graph with
    ⟨_, _, _, _, _, _, _, _, _, hcurrentStartEntry, hcurrentFinishEntry,
      hnextStartEntry, hnextFinishEntry, hvalueStartEntry, hvalueFinishEntry,
      _, _, _, _, _, _⟩
  have hcurrentStartEntry' : CompactFixedWidthEntry suffixBoundary tokenCount
      (termValue valuation indexTerm) data.row.current.start := by
    simpa only [valuation, indexTerm,
      termValue_indexTerm_bvarZero_under_extendValuation] using
        hcurrentStartEntry
  have hcurrentFinishEntry' : CompactFixedWidthEntry suffixBoundary tokenCount
      (termValue valuation successorIndexTerm) data.row.current.finish := by
    simpa only [valuation, successorIndexTerm, indexTerm,
      compactSequentFormulaStepIndexSuccessorTermAtValuation,
      termValue_indexTerm_bvarZeroAddOne_under_extendValuation] using
        hcurrentFinishEntry
  have hnextStartEntry' : CompactFixedWidthEntry suffixBoundary tokenCount
      (termValue valuation successorIndexTerm) data.row.next.start := by
    simpa only [valuation, successorIndexTerm, indexTerm,
      compactSequentFormulaStepIndexSuccessorTermAtValuation,
      termValue_indexTerm_bvarZeroAddOne_under_extendValuation] using
        hnextStartEntry
  have hnextFinishEntry' : CompactFixedWidthEntry suffixBoundary tokenCount
      (termValue valuation secondSuccessorIndexTerm) data.row.next.finish := by
    simpa only [valuation, secondSuccessorIndexTerm, indexTerm,
      termValue_compactSequentFormulaStepIndexSecondSuccessorTermAtValuation]
      using hnextFinishEntry
  have hvalueStartEntry' : CompactFixedWidthEntry valueBoundary tokenCount
      (termValue valuation indexTerm) data.row.value.start := by
    simpa only [valuation, indexTerm,
      termValue_indexTerm_bvarZero_under_extendValuation] using hvalueStartEntry
  have hvalueFinishEntry' : CompactFixedWidthEntry valueBoundary tokenCount
      (termValue valuation successorIndexTerm) data.row.value.finish := by
    simpa only [valuation, successorIndexTerm, indexTerm,
      compactSequentFormulaStepIndexSuccessorTermAtValuation,
      termValue_indexTerm_bvarZeroAddOne_under_extendValuation] using
        hvalueFinishEntry
  let currentStart :=
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexFullyFixedBound valuation
      suffixBoundary tokenCount data.row.current.start indexTerm entryNumeric
      entryBit indexCode htokenCountEntry hindexValue hvaluation
      hsuffixBoundarySize htokenCountSize hindexSize hcurrentStartSize hindexCode
      hindexVariables hcurrentStartEntry'
  let currentFinish :=
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexFullyFixedBound valuation
      suffixBoundary tokenCount data.row.current.finish successorIndexTerm
      entryNumeric entryBit indexCode htokenCountEntry hsuccessorValue hvaluation
      hsuffixBoundarySize htokenCountSize hsuccessorSize hcurrentFinishSize
      hsuccessorCode hsuccessorVariables hcurrentFinishEntry'
  let nextStart :=
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexFullyFixedBound valuation
      suffixBoundary tokenCount data.row.next.start successorIndexTerm entryNumeric
      entryBit indexCode htokenCountEntry hsuccessorValue hvaluation
      hsuffixBoundarySize htokenCountSize hsuccessorSize hnextStartSize
      hsuccessorCode hsuccessorVariables hnextStartEntry'
  let nextFinish :=
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexFullyFixedBound valuation
      suffixBoundary tokenCount data.row.next.finish secondSuccessorIndexTerm
      entryNumeric entryBit indexCode htokenCountEntry hsecondSuccessorValue
      hvaluation hsuffixBoundarySize htokenCountSize hsecondSuccessorSize
      hnextFinishSize hsecondSuccessorCode hsecondSuccessorVariables
      hnextFinishEntry'
  let valueStart :=
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexFullyFixedBound valuation
      valueBoundary tokenCount data.row.value.start indexTerm entryNumeric entryBit
      indexCode htokenCountEntry hindexValue hvaluation hvalueBoundarySize
      htokenCountSize hindexSize hvalueStartSize hindexCode hindexVariables
      hvalueStartEntry'
  let valueFinish :=
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexFullyFixedBound valuation
      valueBoundary tokenCount data.row.value.finish successorIndexTerm
      entryNumeric entryBit indexCode htokenCountEntry hsuccessorValue hvaluation
      hvalueBoundarySize htokenCountSize hsuccessorSize hvalueFinishSize
      hsuccessorCode hsuccessorVariables hvalueFinishEntry'
  simpa only [valuation, indexTerm, successorIndexTerm, secondSuccessorIndexTerm,
    entryNumeric, entryBit, indexCode,
    compactSequentFormulaStepOpenEntryFullyFixedPayload] using
    (show CompactSequentFormulaStepOpenEntryFullyFixedLeaves tokenCount
      suffixBoundary valueBoundary valuation data.row
      (compactSequentFormulaStepOpenEntryFullyFixedPayloadPolynomial entryNumeric
        entryBit indexCode) from
      { currentStart := currentStart
        currentFinish := currentFinish
        nextStart := nextStart
        nextFinish := nextFinish
        valueStart := valueStart
        valueFinish := valueFinish })

#print axioms compactSequentFormulaStepOpenEntryFullyFixedLeavesOfData

end FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedLeaves
