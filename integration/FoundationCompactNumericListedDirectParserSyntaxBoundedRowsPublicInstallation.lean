import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation

/-!
# Installation of publicly fitted syntax-parser rows

This small bridge keeps the expensive row-to-bounded-formula elaboration opaque
to later trace-level quantitative proofs.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxBoundedRowsPublicInstallation

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

set_option maxHeartbeats 500000 in
theorem compactParserSyntaxAdjacentRowsBoundedGraph_of_valid_fit
    {tokenTable width tokenCount stateBoundary tableWidth : Nat}
    {states : List CompactUnifiedParserState}
    {rows : List CompactParserSyntaxAdjacentStepRow}
    (hstateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hrowsValid : CompactParserSyntaxAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length rows)
    (hfit : CompactParserSyntaxAdjacentStepRowsFit tableWidth rows)
    (harea : (tokenCount + 1) * tokenCount <= tableWidth) :
    CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary states.length rows.length
        tableWidth (2 ^ tableWidth) := by
  refine ⟨rfl, ?_⟩
  intro rowIndex hrowIndex
  have hrowGraph := hrowsValid rowIndex hrowIndex
  have hrowMem : rows.getI rowIndex ∈ rows := by
    rw [List.getI_eq_getElem _ hrowIndex]
    exact List.getElem_mem hrowIndex
  have hcurrentStatusLayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (rows.getI rowIndex).currentCoordinates.tasksFinish
        (rows.getI rowIndex).currentCoordinates.finish
        (states.getI rowIndex).2.2 :=
    (CompactUnifiedParserStateAtRows.fixedLayout_of_rows
      rfl hstateRows hrowGraph.1).statusLayout
  have hnextStatusLayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (rows.getI rowIndex).nextCoordinates.tasksFinish
        (rows.getI rowIndex).nextCoordinates.finish
        (states.getI (rowIndex + 1)).2.2 :=
    (CompactUnifiedParserStateAtRows.fixedLayout_of_rows
      rfl hstateRows hrowGraph.2.1).statusLayout
  exact CompactParserSyntaxAdjacentStepRowGraph.toBounded
    hrowGraph (hfit (rows.getI rowIndex) hrowMem)
    (CompactBinaryNatStreamStatusDirectLayout.validBounded
      hcurrentStatusLayout harea)
    (CompactBinaryNatStreamStatusDirectLayout.validBounded
      hnextStatusLayout harea)

#print axioms compactParserSyntaxAdjacentRowsBoundedGraph_of_valid_fit

end FoundationCompactNumericListedDirectParserSyntaxBoundedRowsPublicInstallation
