import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds

/-!
# Fixed syntax bound for the syntax-term failure formula

The original twenty-one-coordinate formula is aligned with its three real
closed leaves.  Their already fixed code bounds and the two conjunction
overheads give the total syntax bound without reducing one large substitution.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds

def syntaxTermFailureClosedFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  binaryNatStatusDoubleClosedFormulaCodeEnvelope bitBound +
    sameRowsCompleteSyntaxFixedPolynomial numericBound bitBound +
    taskSameRowsCompleteSyntaxFixedPolynomial numericBound bitBound + 18

theorem syntaxTermFailureClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount numericBound bitBound : Nat)
    (hgraph : FoundationCompactNumericListedDirectParserSyntaxTermRows.CompactUnifiedParserSyntaxTermFailureRows
      tokenTable width tokenCount current next tailBoundary tailCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next tailBoundary tailCount)).length <=
      syntaxTermFailureClosedFormulaCodePolynomial numericBound bitBound := by
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable
    width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount
  let tasksFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
    next.tasksCount
  have hnextFinishSize : Nat.size next.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (1 : Fin 8)
  have hnextTasksFinishSize : Nat.size next.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (3 : Fin 8)
  have hcurrentTokensCount : current.tokensCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (5 : Fin 8)
  have hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (4 : Fin 8)
  have hnextTokensBoundarySize :
      Nat.size next.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (4 : Fin 8)
  have hnextTasksBoundarySize :
      Nat.size next.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (6 : Fin 8)
  have hfailedCode :
      (binaryFormulaCode failedFormula).length <=
        binaryNatStatusDoubleClosedFormulaCodeEnvelope bitBound := by
    dsimp only [failedFormula]
    exact compactBinaryNatFailedStatusSliceClosedFormula_code_length_le_uniform
      tokenTable width tokenCount next.tasksFinish next.finish bitBound
      htokenTableSize hwidthSize htokenCountSize hnextTasksFinishSize
      hnextFinishSize
  have htokensCode :
      (binaryFormulaCode tokensFormula).length <=
        sameRowsCompleteSyntaxFixedPolynomial numericBound bitBound := by
    dsimp only [tokensFormula]
    exact
      compactAdditiveNatListSameRowsClosedFormula_code_length_le_fullyFixed
        tokenTable width tokenCount current.tokensBoundary
        current.tokensCount next.tokensBoundary next.tokensCount numericBound
        bitBound hgraph.2.1.1 hwidth htokenCount hcurrentTokensCount
        htokenTableSize hcurrentTokensBoundarySize hnextTokensBoundarySize
        hnumericSize
  have htasksCode :
      (binaryFormulaCode tasksFormula).length <=
        taskSameRowsCompleteSyntaxFixedPolynomial numericBound bitBound := by
    dsimp only [tasksFormula]
    exact
      compactAdditiveSyntaxTaskListSameRowsClosedFormula_code_length_le_fullyFixed
        tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
        next.tasksCount numericBound bitBound hgraph.2.2.1 hwidth htokenCount
        htailCount htokenTableSize htailBoundarySize hnextTasksBoundarySize
        hnumericSize
  have hinner :=
    binaryFormulaCode_and_length_le tokensFormula tasksFormula
  have houter :=
    binaryFormulaCode_and_length_le failedFormula
      (tokensFormula ⋏ tasksFormula)
  rw [compactUnifiedParserSyntaxTermFailureClosedFormula_alignment]
  unfold compactUnifiedParserSyntaxTermFailureExplicitFormula
    syntaxTermFailureClosedFormulaCodePolynomial
  exact houter.trans (by
    have := hinner
    omega)

theorem syntaxTermFailureClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) :
    (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next tailBoundary tailCount).freeVariables = ∅ := by
  rw [compactUnifiedParserSyntaxTermFailureClosedFormula_alignment]
  unfold compactUnifiedParserSyntaxTermFailureExplicitFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_and,
    compactBinaryNatFailedStatusSliceClosedFormula_freeVariables_eq_empty,
    compactAdditiveNatListSameRowsClosedFormula_freeVariables_eq_empty_fullyFixed,
    compactAdditiveSyntaxTaskListSameRowsClosedFormula_freeVariables_eq_empty_fullyFixed]
  simp

#print axioms syntaxTermFailureClosedFormula_code_length_le_fixed
#print axioms syntaxTermFailureClosedFormula_freeVariables_eq_empty

end FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
