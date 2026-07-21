import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for continuing a syntax-term task

The running status, fixed token drop, and unchanged task tail are charged by
their public resources and assembled with the original formula tree.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermContinuePublicBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds

private abbrev binaryStatusZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

private abbrev natListDropZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

noncomputable def
    compactUnifiedParserSyntaxTermContinueFromGraphDataPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat)
    (_hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListDropRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount consumed)
    (htasks : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      tailBoundary tailCount next.tasksBoundary next.tasksCount) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount consumed
  let tasksFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
    next.tasksCount
  let tokensTasksResource := transparentHybridConjunctionPayloadEnvelope
    natListDropZeroValuation tokensFormula tasksFormula
    (compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount consumed htokens)
    (compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope tokenTable width
      tokenCount tailBoundary tailCount next.tasksBoundary next.tasksCount
      htasks)
  transparentHybridConjunctionPayloadEnvelope binaryStatusZeroValuation
    runningFormula (tokensFormula ⋏ tasksFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish next.finish)
    tokensTasksResource

noncomputable def compactUnifiedParserSyntaxTermContinueGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next tailBoundary tailCount consumed) : Nat :=
  compactUnifiedParserSyntaxTermContinueFromGraphDataPayloadEnvelope tokenTable
    width tokenCount current next tailBoundary tailCount consumed hgraph.1
    hgraph.2.1 hgraph.2.2

theorem
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat)
    (hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListDropRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount consumed)
    (htasks : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      tailBoundary tailCount next.tasksBoundary next.tasksCount) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateFromGraphData
          tokenTable width tokenCount current next tailBoundary tailCount consumed
          hrunning htokens htasks) ≤
      compactUnifiedParserSyntaxTermContinueFromGraphDataPayloadEnvelope
        tokenTable width tokenCount current next tailBoundary tailCount consumed
        hrunning htokens htasks := by
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  let tokensCertificate :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount consumed htokens
  let tasksCertificate :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount htasks
  have hrunningResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  have htokensResource :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount consumed htokens
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
    runningCertificate tokensTasks
  have hparts := transparentHybridConjunctionPayloadBound_le
    runningCertificate tokensTasks _ _ hrunningResource htokensTasks
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_alignment
          tokenTable width tokenCount current next tailBoundary tailCount
          consumed).symm parts) ≤ _
  unfold compactUnifiedParserSyntaxTermContinueFromGraphDataPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, runningCertificate,
    tokensCertificate, tasksCertificate, tokensTasks, parts] using hparts

theorem
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next tailBoundary tailCount consumed) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          consumed hgraph) ≤
      compactUnifiedParserSyntaxTermContinueGraphPayloadEnvelope tokenTable width
        tokenCount current next tailBoundary tailCount consumed hgraph := by
  simpa only [
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph,
    compactUnifiedParserSyntaxTermContinueGraphPayloadEnvelope] using
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
      tokenTable width tokenCount current next tailBoundary tailCount consumed
      hgraph.1 hgraph.2.1 hgraph.2.2

#print axioms
  compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectParserSyntaxTermContinuePublicBounds
