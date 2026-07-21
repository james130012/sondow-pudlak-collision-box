import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for syntax-term failure rows

The failed status and the two unchanged-list certificates are charged by their
public resources and assembled with the original right-associated formula tree.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds

private abbrev binaryStatusZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

private abbrev natListZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.zeroValuation

noncomputable def
    compactUnifiedParserSyntaxTermFailureFromGraphDataPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (_hfailed : CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (htasks : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      tailBoundary tailCount next.tasksBoundary next.tasksCount) : Nat :=
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable
    width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount
  let tasksFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
    next.tasksCount
  let tokensTasksResource := transparentHybridConjunctionPayloadEnvelope
    natListZeroValuation tokensFormula tasksFormula
    (compactAdditiveNatListSameRowsGraphPayloadEnvelope tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens)
    (compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope tokenTable width
      tokenCount tailBoundary tailCount next.tasksBoundary next.tasksCount
      htasks)
  transparentHybridConjunctionPayloadEnvelope binaryStatusZeroValuation
    failedFormula (tokensFormula ⋏ tasksFormula)
    (compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish next.finish)
    tokensTasksResource

noncomputable def compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next tailBoundary tailCount) : Nat :=
  compactUnifiedParserSyntaxTermFailureFromGraphDataPayloadEnvelope tokenTable
    width tokenCount current next tailBoundary tailCount hgraph.1 hgraph.2.1
    hgraph.2.2

theorem
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (hfailed : CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (htasks : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      tailBoundary tailCount next.tasksBoundary next.tasksCount) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateFromGraphData
          tokenTable width tokenCount current next tailBoundary tailCount
          hfailed htokens htasks) ≤
      compactUnifiedParserSyntaxTermFailureFromGraphDataPayloadEnvelope
        tokenTable width tokenCount current next tailBoundary tailCount
        hfailed htokens htasks := by
  let failedCertificate :=
    compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hfailed
  let tokensCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  let tasksCertificate :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount htasks
  have hfailedResource :=
    compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount next.tasksFinish next.finish hfailed
  have htokensResource :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokens
  have htasksResource :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount htasks
  let tokensTasks :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokensCertificate tasksCertificate
  have htokensTasks := transparentHybridConjunctionPayloadBound_le
    tokensCertificate tasksCertificate _ _ htokensResource htasksResource
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    failedCertificate tokensTasks
  have hparts := transparentHybridConjunctionPayloadBound_le
    failedCertificate tokensTasks _ _ hfailedResource htokensTasks
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxTermFailureClosedFormula_alignment
          tokenTable width tokenCount current next tailBoundary
          tailCount).symm parts) ≤ _
  unfold compactUnifiedParserSyntaxTermFailureFromGraphDataPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, failedCertificate,
    tokensCertificate, tasksCertificate, tokensTasks, parts] using hparts

theorem
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next tailBoundary tailCount) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          hgraph) ≤
      compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable width
        tokenCount current next tailBoundary tailCount hgraph := by
  simpa only [
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph,
    compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope] using
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
      tokenTable width tokenCount current next tailBoundary tailCount hgraph.1
      hgraph.2.1 hgraph.2.2

def compactUnifiedParserSyntaxTermFailurePublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) : Nat :=
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable
    width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount
  let tasksFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
    next.tasksCount
  let tokensTasksResource := transparentHybridConjunctionPayloadEnvelope
    natListZeroValuation tokensFormula tasksFormula
    (compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount)
    (compactAdditiveSyntaxTaskListSameRowsPublicFinitePayloadEnvelope tokenTable
      width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount)
  transparentHybridConjunctionPayloadEnvelope binaryStatusZeroValuation
    failedFormula (tokensFormula ⋏ tasksFormula)
    (compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish next.finish)
    tokensTasksResource

theorem
    compactUnifiedParserSyntaxTermFailureFromGraphDataPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (hfailed : CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (htasks : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      tailBoundary tailCount next.tasksBoundary next.tasksCount) :
    compactUnifiedParserSyntaxTermFailureFromGraphDataPayloadEnvelope tokenTable
        width tokenCount current next tailBoundary tailCount hfailed htokens
        htasks <=
      compactUnifiedParserSyntaxTermFailurePublicFinitePayloadEnvelope tokenTable
        width tokenCount current next tailBoundary tailCount := by
  unfold compactUnifiedParserSyntaxTermFailureFromGraphDataPayloadEnvelope
    compactUnifiedParserSyntaxTermFailurePublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      (compactAdditiveNatListSameRowsGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount htokens)
      (compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
        next.tasksCount htasks))

theorem
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next tailBoundary tailCount) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          hgraph) <=
      compactUnifiedParserSyntaxTermFailurePublicFinitePayloadEnvelope tokenTable
        width tokenCount current next tailBoundary tailCount := by
  exact
    (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next tailBoundary tailCount
      hgraph).trans
    (compactUnifiedParserSyntaxTermFailureFromGraphDataPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount current next tailBoundary tailCount hgraph.1
      hgraph.2.1 hgraph.2.2)

#print axioms
  compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds
