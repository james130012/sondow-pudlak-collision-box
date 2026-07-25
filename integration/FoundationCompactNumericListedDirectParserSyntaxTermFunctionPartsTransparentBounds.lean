import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionRunningTokensFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListDropThreeRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed function syntax-term transition

The genuine running-status, drop-three token-list, and function task-insertion
certificates are rebuilt and assembled in the original three-leaf formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionPartsTransparentBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionBranchCertificates
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionRunningTokensFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectNatListDropThreeRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds

private def functionFixedZeroValuation : Nat -> Nat := fun _ => 0

theorem
    syntaxTermFunctionPartsCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity numericBound bitBound :
      Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity
      functionArity)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hfunctionSize : Nat.size functionArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFunctionPartsCertificate tokenTable width tokenCount
          next.tasksFinish next.finish current.tokensBoundary
          current.tokensCount next.tokensBoundary next.tokensCount
          tailBoundary tailCount next.tasksBoundary next.tasksCount binderArity
          functionArity hgraph.1 hgraph.2.1 hgraph.2.2) <=
      syntaxTermFunctionPartsTransparentEnvelope tokenTable width tokenCount
        current next tailBoundary tailCount binderArity functionArity
        numericBound bitBound := by
  rcases hgraph with ⟨hrunning, htokens, htasks⟩
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount 3
  let tasksFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount (fixedNumeralTerm 2)
      (FoundationCompactPABinaryNumeralAddition.shortBinaryNumeralTerm
        binderArity)
      (FoundationCompactPABinaryNumeralAddition.shortBinaryNumeralTerm
        functionArity)
  let runningCertificate :=
    syntaxTermFunctionRunningCertificate tokenTable width tokenCount
      next.tasksFinish next.finish hrunning
  let tokensCertificate :=
    syntaxTermFunctionTokensCertificate tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount htokens
  let tasksCertificate :=
    syntaxTermFunctionTaskCertificate tokenTable width tokenCount tailBoundary
      tailCount next.tasksBoundary next.tasksCount binderArity functionArity
      htasks
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hnextTasksFinish : next.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextValue (3 : Fin 8)
  have hnextTasksCount : next.tasksCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextValue (7 : Fin 8)
  have hcurrentTokensCount : current.tokensCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (5 : Fin 8)
  have hnextFinishSize : Nat.size next.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (1 : Fin 8)
  have hnextTasksFinishSize : Nat.size next.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (3 : Fin 8)
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
  have hrunningPayload :
      hybridFormulaStructuralPayloadBound runningCertificate <=
        compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound := by
    simpa only [runningCertificate] using
      (syntaxTermFunctionRunningCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount next.tasksFinish next.finish numericBound
        bitBound hrunning hwidth hnextTasksFinish htokenTableSize hwidthSize
        htokenCountSize hnextTasksFinishSize hnextFinishSize)
  have htokensPayload :
      hybridFormulaStructuralPayloadBound tokensCertificate <=
        dropThreeRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [tokensCertificate] using
      (syntaxTermFunctionTokensCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount numericBound bitBound htokens
        hwidth htokenCount hcurrentTokensCount htokenTableSize
        hcurrentTokensBoundarySize hnextTokensBoundarySize hnumericSize)
  have htasksPayload :
      hybridFormulaStructuralPayloadBound tasksCertificate <=
        taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound := by
    simpa only [tasksCertificate] using
      (syntaxTermFunctionTaskCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
        next.tasksCount binderArity functionArity numericBound bitBound
        htasks hwidth htokenCount hnextTasksCount htokenTableSize
        htailBoundarySize hnextTasksBoundarySize hbinderSize hfunctionSize
        hnumericSize)
  let tailCertificate :=
    syntaxTermFunctionTailCertificate tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount binderArity functionArity htokens htasks
  have htail :
      hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            tokensCertificate tasksCertificate) <=
        transparentHybridConjunctionPayloadEnvelope
          FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation
          tokensFormula tasksFormula
          (dropThreeRowsCompleteFullyFixedPayloadPolynomial numericBound
            bitBound)
          (taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound
            bitBound) := by
    exact transparentHybridConjunctionPayloadBound_le tokensCertificate
      tasksCertificate _ _ htokensPayload htasksPayload
  have hparts :=
    transparentHybridConjunctionPayloadBound_le runningCertificate
      tailCertificate _ _ hrunningPayload htail
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        runningCertificate tailCertificate) <=
    syntaxTermFunctionPartsTransparentEnvelope tokenTable width tokenCount
      current next tailBoundary tailCount binderArity functionArity
      numericBound bitBound
  unfold syntaxTermFunctionPartsTransparentEnvelope
  simpa only [runningFormula, tokensFormula, tasksFormula, tailCertificate] using
    hparts

#print axioms
  syntaxTermFunctionPartsCertificate_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionPartsTransparentBounds
