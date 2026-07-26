import integration.FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowFullyFixedBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData

/-! # Install the three fully fixed natural-list row leaves from one graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedOfGraph

open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowFullyFixedBound

structure CompactSequentFormulaStepNatListRowsFullyFixedBounds
    (tokenTable width tokenCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) where
  current : ClosedDirectFormulaBound
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.current.start row.current.count row.current.finish
      row.current.boundary row.current.boundarySize)
    (compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount)
  next : ClosedDirectFormulaBound
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.next.start row.next.count row.next.finish row.next.boundary
      row.next.boundarySize)
    (compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount)
  value : ClosedDirectFormulaBound
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      row.value.start row.value.count row.value.finish row.value.boundary
      row.value.boundarySize)
    (compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
      tokenCount)

noncomputable def compactSequentFormulaStepNatListRowsFullyFixedBoundsOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount index row) :
    CompactSequentFormulaStepNatListRowsFullyFixedBounds tokenTable width
      tokenCount row := by
  rcases hgraph with
    ⟨_hcurrentStart, _hcurrentFinish, hcurrentCount,
      _hnextStart, _hnextFinish, hnextCount,
      _hvalueStart, _hvalueFinish, hvalueCount,
      _hcurrentStartEntry, _hcurrentFinishEntry,
      _hnextStartEntry, _hnextFinishEntry,
      _hvalueStartEntry, _hvalueFinishEntry,
      hcurrentRows, hnextRows, hvalueRows,
      _hparser, _happend, _hsuccessorCount⟩
  exact
    { current := compactSequentFormulaStepNatListRowFullyFixedBound tokenTable
        width tokenCount row.current.start row.current.count
        row.current.finish row.current.boundary row.current.boundarySize
        hcurrentCount hcurrentRows
      next := compactSequentFormulaStepNatListRowFullyFixedBound tokenTable
        width tokenCount row.next.start row.next.count row.next.finish
        row.next.boundary row.next.boundarySize hnextCount hnextRows
      value := compactSequentFormulaStepNatListRowFullyFixedBound tokenTable
        width tokenCount row.value.start row.value.count row.value.finish
        row.value.boundary row.value.boundarySize hvalueCount hvalueRows }

noncomputable def
    compactSequentFormulaStepNatListRowsFullyFixedBoundsOfCheckedData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    CompactSequentFormulaStepNatListRowsFullyFixedBounds tokenTable width
      tokenCount data.row :=
  compactSequentFormulaStepNatListRowsFullyFixedBoundsOfGraph tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    data.row data.graph

#print axioms compactSequentFormulaStepNatListRowsFullyFixedBoundsOfGraph
#print axioms compactSequentFormulaStepNatListRowsFullyFixedBoundsOfCheckedData

end FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedOfGraph
