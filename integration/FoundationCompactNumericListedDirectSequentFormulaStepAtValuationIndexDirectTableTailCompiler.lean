import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectTailCompiler

/-! # Open table-entry conjuncts 10--15 of the sequent-step compiler -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax

def compactSequentFormulaStepDirectTail10AtValuationIndex
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  let indexTerm : ValuationTerm := &0
  let successorIndexTerm :=
    compactSequentFormulaStepIndexSuccessorTermAtValuation indexTerm
  let secondSuccessorIndexTerm :=
    compactSequentFormulaStepIndexSecondSuccessorTermAtValuation indexTerm
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      indexTerm
      (shortBinaryNumeralTerm row.current.start) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      successorIndexTerm
      (shortBinaryNumeralTerm row.current.finish) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      successorIndexTerm
      (shortBinaryNumeralTerm row.next.start) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      secondSuccessorIndexTerm
      (shortBinaryNumeralTerm row.next.finish) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount)
      indexTerm
      (shortBinaryNumeralTerm row.value.start) ⋏
  (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount)
      successorIndexTerm
      (shortBinaryNumeralTerm row.value.finish) ⋏
    compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
      tokenCount suffixCount valueCount row)))))

noncomputable def
    compactSequentFormulaStepDirectTail10AtValuationIndexBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ExactContextBoundedProof
      (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepDirectTail10AtValuationIndex tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount row) := by
  let tail16 :=
    compactSequentFormulaStepDirectTail16AtValuationIndexBoundOfGraph
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex row hgraph
  rcases hgraph with
    ⟨_, _, _, _, _, _, _, _, _,
      hcurrentStartEntry, hcurrentFinishEntry,
      hnextStartEntry, hnextFinishEntry,
      hvalueStartEntry, hvalueFinishEntry,
      _, _, _, _, _, _⟩
  let valuation := extendValuation rowIndex zeroValuation
  let indexTerm : ValuationTerm := &0
  let successorIndexTerm :=
    compactSequentFormulaStepIndexSuccessorTermAtValuation indexTerm
  let secondSuccessorIndexTerm :=
    compactSequentFormulaStepIndexSecondSuccessorTermAtValuation indexTerm
  have hindexVariables : indexTerm.freeVariables ⊆ {0} := by
    simpa only [indexTerm] using
      compactSequentFormulaStepIndexTerm_freeVariables_subset_singleton
  have hsuccessorIndexVariables :
      successorIndexTerm.freeVariables ⊆ {0} := by
    simpa only [successorIndexTerm, indexTerm] using
      compactSequentFormulaStepIndexSuccessorTermAtValuation_freeVariables_subset_singleton
  have hsecondSuccessorIndexVariables :
      secondSuccessorIndexTerm.freeVariables ⊆ {0} := by
    simpa only [secondSuccessorIndexTerm, indexTerm] using
      compactSequentFormulaStepIndexSecondSuccessorTermAtValuation_freeVariables_subset_singleton
  have hcurrentStartEntry' : CompactFixedWidthEntry suffixBoundary tokenCount
      (termValue valuation indexTerm) row.current.start := by
    simpa only [valuation, indexTerm,
      termValue_indexTerm_bvarZero_under_extendValuation] using
        hcurrentStartEntry
  have hcurrentFinishEntry' : CompactFixedWidthEntry suffixBoundary tokenCount
      (termValue valuation successorIndexTerm) row.current.finish := by
    simpa only [valuation, successorIndexTerm, indexTerm,
      compactSequentFormulaStepIndexSuccessorTermAtValuation,
      termValue_indexTerm_bvarZeroAddOne_under_extendValuation] using
        hcurrentFinishEntry
  have hnextStartEntry' : CompactFixedWidthEntry suffixBoundary tokenCount
      (termValue valuation successorIndexTerm) row.next.start := by
    simpa only [valuation, successorIndexTerm, indexTerm,
      compactSequentFormulaStepIndexSuccessorTermAtValuation,
      termValue_indexTerm_bvarZeroAddOne_under_extendValuation] using
        hnextStartEntry
  have hnextFinishEntry' : CompactFixedWidthEntry suffixBoundary tokenCount
      (termValue valuation secondSuccessorIndexTerm) row.next.finish := by
    simpa only [valuation, secondSuccessorIndexTerm, indexTerm,
      termValue_compactSequentFormulaStepIndexSecondSuccessorTermAtValuation]
      using hnextFinishEntry
  have hvalueStartEntry' : CompactFixedWidthEntry valueBoundary tokenCount
      (termValue valuation indexTerm) row.value.start := by
    simpa only [valuation, indexTerm,
      termValue_indexTerm_bvarZero_under_extendValuation] using
        hvalueStartEntry
  have hvalueFinishEntry' : CompactFixedWidthEntry valueBoundary tokenCount
      (termValue valuation successorIndexTerm) row.value.finish := by
    simpa only [valuation, successorIndexTerm, indexTerm,
      compactSequentFormulaStepIndexSuccessorTermAtValuation,
      termValue_indexTerm_bvarZeroAddOne_under_extendValuation] using
        hvalueFinishEntry
  let proof10 := compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound
    valuation suffixBoundary tokenCount row.current.start indexTerm
    hindexVariables hcurrentStartEntry'
  let proof11 := compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound
    valuation suffixBoundary tokenCount row.current.finish successorIndexTerm
    hsuccessorIndexVariables hcurrentFinishEntry'
  let proof12 := compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound
    valuation suffixBoundary tokenCount row.next.start successorIndexTerm
    hsuccessorIndexVariables hnextStartEntry'
  let proof13 := compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound
    valuation suffixBoundary tokenCount row.next.finish
    secondSuccessorIndexTerm hsecondSuccessorIndexVariables hnextFinishEntry'
  let proof14 := compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound
    valuation valueBoundary tokenCount row.value.start indexTerm
    hindexVariables hvalueStartEntry'
  let proof15 := compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound
    valuation valueBoundary tokenCount row.value.finish successorIndexTerm
    hsuccessorIndexVariables hvalueFinishEntry'
  let tail15 := ExactContextBoundedProof.conjunction proof15 tail16
  let tail14 := ExactContextBoundedProof.conjunction proof14 tail15
  let tail13 := ExactContextBoundedProof.conjunction proof13 tail14
  let tail12 := ExactContextBoundedProof.conjunction proof12 tail13
  let tail11 := ExactContextBoundedProof.conjunction proof11 tail12
  let assembled := ExactContextBoundedProof.conjunction proof10 tail11
  simpa only [compactSequentFormulaStepDirectTail10AtValuationIndex,
    indexTerm, successorIndexTerm, secondSuccessorIndexTerm] using assembled

#print axioms
  compactSequentFormulaStepDirectTail10AtValuationIndexBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
