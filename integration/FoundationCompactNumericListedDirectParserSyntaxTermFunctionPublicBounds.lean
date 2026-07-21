import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for a syntax-term function task

The running status, three-token drop, and function-task insertion are charged
by their public resources and assembled with the original formula tree.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds

private abbrev binaryStatusZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

private abbrev natListDropZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

private theorem fixedNumeralTerm_freeVariables_eq_empty (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

noncomputable def
    compactUnifiedParserSyntaxTermFunctionFromGraphDataPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat)
    (_hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListDropRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount 3)
    (htasks : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount next.tasksBoundary next.tasksCount 2 binderArity
      functionArity) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount 3
  let tasksFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount tailBoundary tailCount next.tasksBoundary next.tasksCount
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
  let tokensTasksResource := transparentHybridConjunctionPayloadEnvelope
    natListDropZeroValuation tokensFormula tasksFormula
    (compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 3 htokens)
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount 2 binderArity functionArity (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity) htasks)
  transparentHybridConjunctionPayloadEnvelope binaryStatusZeroValuation
    runningFormula (tokensFormula ⋏ tasksFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish next.finish)
    tokensTasksResource

noncomputable def compactUnifiedParserSyntaxTermFunctionGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity
      functionArity) : Nat :=
  compactUnifiedParserSyntaxTermFunctionFromGraphDataPayloadEnvelope tokenTable
    width tokenCount current next tailBoundary tailCount binderArity
    functionArity hgraph.1 hgraph.2.1 hgraph.2.2

theorem
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat)
    (hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListDropRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount 3)
    (htasks : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount next.tasksBoundary next.tasksCount 2 binderArity
      functionArity) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateFromGraphData
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity functionArity hrunning htokens htasks) ≤
      compactUnifiedParserSyntaxTermFunctionFromGraphDataPayloadEnvelope
        tokenTable width tokenCount current next tailBoundary tailCount
        binderArity functionArity hrunning htokens htasks := by
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  let tokensCertificate :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 3 htokens
  let tasksCertificate :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount 2 binderArity functionArity (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
      (fun valuation => by simp)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) htasks
  have hrunningResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  have htokensResource :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 3 htokens
  have htasksResource :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount 2 binderArity functionArity (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
      (fixedNumeralTerm_freeVariables_eq_empty 2)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty functionArity)
      (fun valuation => by simp)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm]) htasks
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
        (compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_alignment
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity functionArity).symm parts) ≤ _
  unfold compactUnifiedParserSyntaxTermFunctionFromGraphDataPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, runningCertificate,
    tokensCertificate, tasksCertificate, tokensTasks, parts] using hparts

theorem
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity
      functionArity) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity functionArity hgraph) ≤
      compactUnifiedParserSyntaxTermFunctionGraphPayloadEnvelope tokenTable width
        tokenCount current next tailBoundary tailCount binderArity
        functionArity hgraph := by
  simpa only [
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph,
    compactUnifiedParserSyntaxTermFunctionGraphPayloadEnvelope] using
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
      tokenTable width tokenCount current next tailBoundary tailCount
      binderArity functionArity hgraph.1 hgraph.2.1 hgraph.2.2

#print axioms
  compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateFromGraphData_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionPublicBounds
