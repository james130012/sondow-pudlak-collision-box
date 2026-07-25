import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinuePublicBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListDropOneRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed syntax-term continue certificate

The original continue certificate is rebuilt from its real running-status,
drop-one token-list, and unchanged-task-list leaves.  All three resources and
both conjunctions use the shared numeric and bit coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermContinueFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermContinuePublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsFullyFixedBounds

private def continueZeroValuation : Nat -> Nat := fun _ => 0

def syntaxTermContinueRunningFormulaCodePolynomial (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactBinaryNatRunningStatusSliceDef.val)).length

def syntaxTermContinueClosedFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  syntaxTermContinueRunningFormulaCodePolynomial bitBound +
    dropOneRowsCompleteSyntaxFixedPolynomial numericBound bitBound +
    taskSameRowsCompleteSyntaxFixedPolynomial numericBound bitBound + 18

def syntaxTermContinueFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (syntaxTermContinueClosedFormulaCodePolynomial numericBound bitBound)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound)
    (dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)

@[simp] theorem
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) :
    (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next tailBoundary tailCount 1).freeVariables =
        ∅ := by
  have hrunning :
      (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
        tokenCount next.tasksFinish next.finish).freeVariables = ∅ := by
    unfold compactBinaryNatRunningStatusSliceClosedFormula
    exact fiveShortNumeralRewritingFormula_freeVariables_eq_empty
      compactBinaryNatRunningStatusSliceDef.val tokenTable width tokenCount
      next.tasksFinish next.finish
  have htokens :
      (compactAdditiveNatListDropFixedNumeralRowsClosedFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount 1).freeVariables = ∅ :=
    compactAdditiveNatListDropOneRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount
  have htasks :
      (compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width
        tokenCount tailBoundary tailCount next.tasksBoundary
        next.tasksCount).freeVariables = ∅ :=
    compactAdditiveSyntaxTaskListSameRowsClosedFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount
  rw [compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_alignment]
  unfold compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_and,
    hrunning, htokens, htasks]
  simp

theorem
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next tailBoundary tailCount 1)
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
      (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
        tokenTable width tokenCount current next tailBoundary tailCount 1)).length <=
      syntaxTermContinueClosedFormulaCodePolynomial numericBound bitBound := by
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount 1
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
  have hrunningCode :
      (binaryFormulaCode runningFormula).length <=
        syntaxTermContinueRunningFormulaCodePolynomial bitBound := by
    dsimp only [runningFormula]
    exact fiveShortNumeralRewritingFormula_code_length_le_uniform
      compactBinaryNatRunningStatusSliceDef.val tokenTable width tokenCount
      next.tasksFinish next.finish bitBound htokenTableSize hwidthSize
      htokenCountSize hnextTasksFinishSize hnextFinishSize
  have htokensCode :
      (binaryFormulaCode tokensFormula).length <=
        dropOneRowsCompleteSyntaxFixedPolynomial numericBound bitBound := by
    dsimp only [tokensFormula]
    exact
      compactAdditiveNatListDropOneRowsClosedFormula_code_length_le_fullyFixed
        tokenTable width tokenCount current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount numericBound bitBound hgraph.2.1
        hwidth htokenCount hcurrentTokensCount htokenTableSize
        hcurrentTokensBoundarySize hnextTokensBoundarySize hnumericSize
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
  have htailRaw := binaryFormulaCode_and_length_le tokensFormula tasksFormula
  have htotalRaw := binaryFormulaCode_and_length_le runningFormula
    (tokensFormula ⋏ tasksFormula)
  rw [compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_alignment]
  change
    (binaryFormulaCode
      (runningFormula ⋏ (tokensFormula ⋏ tasksFormula))).length <= _
  unfold syntaxTermContinueClosedFormulaCodePolynomial
  omega

theorem
    compactUnifiedParserSyntaxTermContinueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next tailBoundary tailCount 1)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount 1
          hgraph) <=
      syntaxTermContinueFullyFixedPayloadPolynomial numericBound bitBound := by
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount 1
  let tasksFormula := compactAdditiveSyntaxTaskListSameRowsClosedFormula
    tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
    next.tasksCount
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hgraph.1
  let tokensCertificate :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 hgraph.2.1
  let tasksCertificate :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount hgraph.2.2
  have hnextTasksFinish : next.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextValue (3 : Fin 8)
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
  have hrunningResource :
      hybridFormulaStructuralPayloadBound runningCertificate <=
        compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound := by
    dsimp only [runningCertificate]
    exact
      compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount next.tasksFinish next.finish numericBound
        bitBound hwidth hnextTasksFinish htokenTableSize hwidthSize
        htokenCountSize hnextTasksFinishSize hnextFinishSize hgraph.1
  have htokensPublic :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 hgraph.2.1
  have htokensEnvelope :=
    compactAdditiveNatListDropOneRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount numericBound bitBound hgraph.2.1
      hwidth htokenCount hcurrentTokensCount htokenTableSize
      hcurrentTokensBoundarySize hnextTokensBoundarySize hnumericSize
  have htokensResource :
      hybridFormulaStructuralPayloadBound tokensCertificate <=
        dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [tokensCertificate]
    exact htokensPublic.trans htokensEnvelope
  have htasksPublic :=
    compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount hgraph.2.2
  have htasksEnvelope :=
    compactAdditiveSyntaxTaskListSameRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount numericBound bitBound hgraph.2.2 hwidth htokenCount
      htailCount htokenTableSize htailBoundarySize hnextTasksBoundarySize
      hnumericSize
  have htasksResource :
      hybridFormulaStructuralPayloadBound tasksCertificate <=
        taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [tasksCertificate]
    exact htasksPublic.trans htasksEnvelope
  let tailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokensCertificate tasksCertificate
  have htail :=
    transparentHybridConjunctionPayloadBound_le tokensCertificate
      tasksCertificate _ _ htokensResource htasksResource
  let parts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      runningCertificate tailCertificate
  have hparts :=
    transparentHybridConjunctionPayloadBound_le runningCertificate
      tailCertificate _ _ hrunningResource htail
  have hrunningClosed : runningFormula.freeVariables = ∅ := by
    dsimp only [runningFormula]
    unfold compactBinaryNatRunningStatusSliceClosedFormula
    exact fiveShortNumeralRewritingFormula_freeVariables_eq_empty
      compactBinaryNatRunningStatusSliceDef.val tokenTable width tokenCount
      next.tasksFinish next.finish
  have htokensClosed : tokensFormula.freeVariables = ∅ := by
    dsimp only [tokensFormula]
    exact compactAdditiveNatListDropOneRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount
  have htasksClosed : tasksFormula.freeVariables = ∅ := by
    dsimp only [tasksFormula]
    exact
      compactAdditiveSyntaxTaskListSameRowsClosedFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
        next.tasksCount
  have hclosed :
      (runningFormula ⋏ (tokensFormula ⋏ tasksFormula)).freeVariables =
        ∅ := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_and, hrunningClosed,
      htokensClosed, htasksClosed]
    simp
  have hrunningCode :
      (binaryFormulaCode runningFormula).length <=
        syntaxTermContinueRunningFormulaCodePolynomial bitBound := by
    dsimp only [runningFormula]
    exact fiveShortNumeralRewritingFormula_code_length_le_uniform
      compactBinaryNatRunningStatusSliceDef.val tokenTable width tokenCount
      next.tasksFinish next.finish bitBound htokenTableSize hwidthSize
      htokenCountSize hnextTasksFinishSize hnextFinishSize
  have htokensCode :
      (binaryFormulaCode tokensFormula).length <=
        dropOneRowsCompleteSyntaxFixedPolynomial numericBound bitBound := by
    dsimp only [tokensFormula]
    exact
      compactAdditiveNatListDropOneRowsClosedFormula_code_length_le_fullyFixed
        tokenTable width tokenCount current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount numericBound bitBound hgraph.2.1
        hwidth htokenCount hcurrentTokensCount htokenTableSize
        hcurrentTokensBoundarySize hnextTokensBoundarySize hnumericSize
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
  have htailRaw := binaryFormulaCode_and_length_le tokensFormula tasksFormula
  have htailCode :
      (binaryFormulaCode (tokensFormula ⋏ tasksFormula)).length <=
        dropOneRowsCompleteSyntaxFixedPolynomial numericBound bitBound +
          taskSameRowsCompleteSyntaxFixedPolynomial numericBound bitBound +
          9 := by
    omega
  have htotalRaw := binaryFormulaCode_and_length_le runningFormula
    (tokensFormula ⋏ tasksFormula)
  have hcode :
      (binaryFormulaCode
        (runningFormula ⋏ (tokensFormula ⋏ tasksFormula))).length <=
          syntaxTermContinueClosedFormulaCodePolynomial numericBound
            bitBound := by
    unfold syntaxTermContinueClosedFormulaCodePolynomial
    omega
  have hassembly :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      continueZeroValuation runningFormula tokensFormula tasksFormula
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (taskSameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (syntaxTermContinueClosedFormulaCodePolynomial numericBound bitBound)
      (by
        unfold syntaxTermContinueClosedFormulaCodePolynomial
        omega)
      hclosed hcode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_alignment
          tokenTable width tokenCount current next tailBoundary tailCount
          1).symm parts) <= _
  unfold syntaxTermContinueFullyFixedPayloadPolynomial
  simpa only [hybridFormulaStructuralPayloadBound, runningFormula,
    tokensFormula, tasksFormula, runningCertificate, tokensCertificate,
    tasksCertificate, tailCertificate, parts, continueZeroValuation] using
      hparts.trans hassembly

#print axioms
  compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula_code_length_le_fullyFixed
#print axioms
  compactUnifiedParserSyntaxTermContinueExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermContinueFullyFixedBounds
