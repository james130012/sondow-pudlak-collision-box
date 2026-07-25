import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierPublicBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListDropOneRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsQuantifierFullyFixedBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed quantified syntax-formula transition

The genuine running-status, drop-one token-list, and quantifier task-insertion
certificates are rebuilt and assembled in the original three-leaf formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierFullyFixedBounds

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
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsQuantifierFullyFixedBounds

private def quantifierFixedZeroValuation : Nat -> Nat := fun _ => 0

def syntaxFormulaQuantifierAssemblySyntaxEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound +
    dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound +
    taskConsQuantifierFullyFixedPayloadEnvelope tokenCount numericBound
      bitBound +
    2 * (binaryNatCode 4).length + 1

def syntaxFormulaQuantifierFullyFixedPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (syntaxFormulaQuantifierAssemblySyntaxEnvelope tokenCount numericBound
      bitBound)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound)
    (dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (taskConsQuantifierFullyFixedPayloadEnvelope tokenCount numericBound
      bitBound)

theorem
    compactUnifiedParserSyntaxFormulaQuantifierClosedFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) :
    (compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width
      tokenCount current next tailBoundary tailCount
      binderArity).freeVariables = ∅ := by
  rw [compactUnifiedParserSyntaxFormulaQuantifierClosedFormula_alignment]
  unfold compactUnifiedParserSyntaxFormulaQuantifierExplicitFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_and]
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  rw [fiveShortNumeralRewritingFormula_freeVariables_eq_empty]
  rw [compactAdditiveNatListDropOneRowsClosedFormula_freeVariables_eq_empty]
  rw [taskConsQuantifierFormula_freeVariables_eq_empty]
  simp

theorem
    compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity)
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
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity hgraph) <=
      syntaxFormulaQuantifierFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
  rcases hgraph with ⟨hrunning, htokens, htasks⟩
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokensFormula := compactAdditiveNatListDropFixedNumeralRowsClosedFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    next.tokensBoundary next.tokensCount 1
  let tasksFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  let tokensCertificate :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 htokens
  let tasksCertificate :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount 1 (binderArity + 1) 0 (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
      (termValue_nativeNumeralTerm · 1)
      (termValue_binderSuccessorTerm · binderArity)
      (termValue_nativeNumeralTerm · 0) htasks
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
    dsimp only [runningCertificate]
    exact
      compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount next.tasksFinish next.finish numericBound
        bitBound hwidth hnextTasksFinish htokenTableSize hwidthSize
        htokenCountSize hnextTasksFinishSize hnextFinishSize hrunning
  have htokensPublic :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 htokens
  have htokensFixed :=
    compactAdditiveNatListDropOneRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount numericBound bitBound htokens
      hwidth htokenCount hcurrentTokensCount htokenTableSize
      hcurrentTokensBoundarySize hnextTokensBoundarySize hnumericSize
  have htokensPayload :
      hybridFormulaStructuralPayloadBound tokensCertificate <=
        dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [tokensCertificate] using htokensPublic.trans htokensFixed
  let headData :=
    compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width
      tokenCount tailBoundary tailCount next.tasksBoundary next.tasksCount
      1 (binderArity + 1) 0 htasks
  let tailRows :=
    compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable width
      tokenCount tailBoundary tailCount next.tasksBoundary next.tasksCount
      1 (binderArity + 1) 0 htasks
  have htasksFromData :=
    taskConsQuantifierCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount tailBoundary tailCount next.tasksBoundary
      next.tasksCount binderArity numericBound bitBound hwidth htokenCount
      hnextTasksCount htokenTableSize htailBoundarySize
      hnextTasksBoundarySize hbinderSize hnumericSize htasks.1 headData
      tailRows
  have htasksPayload :
      hybridFormulaStructuralPayloadBound tasksCertificate <=
        taskConsQuantifierFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound := by
    simpa only [tasksCertificate,
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph,
      headData, tailRows] using htasksFromData
  let tailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokensCertificate tasksCertificate
  have htail :=
    transparentHybridConjunctionPayloadBound_le tokensCertificate
      tasksCertificate _ _ htokensPayload htasksPayload
  let parts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      runningCertificate tailCertificate
  have hparts :=
    transparentHybridConjunctionPayloadBound_le runningCertificate
      tailCertificate _ _ hrunningPayload htail
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
    exact taskConsQuantifierFormula_freeVariables_eq_empty tokenTable width
      tokenCount tailBoundary tailCount next.tasksBoundary next.tasksCount
      binderArity
  have hclosed :
      (runningFormula ⋏ (tokensFormula ⋏ tasksFormula)).freeVariables =
        ∅ := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_and, hrunningClosed,
      htokensClosed, htasksClosed, Finset.union_empty]
  have hrunningCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      runningCertificate
  have htokensCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      tokensCertificate
  have htasksCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      tasksCertificate
  have hrunningCode :
      (binaryFormulaCode runningFormula).length <=
        compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound := by
    simpa only [runningCertificate, runningFormula] using
      hrunningCodeRaw.trans hrunningPayload
  have htokensCode :
      (binaryFormulaCode tokensFormula).length <=
        dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [tokensCertificate, tokensFormula] using
      htokensCodeRaw.trans htokensPayload
  have htasksCode :
      (binaryFormulaCode tasksFormula).length <=
        taskConsQuantifierFullyFixedPayloadEnvelope tokenCount numericBound
          bitBound := by
    simpa only [tasksCertificate, tasksFormula] using
      htasksCodeRaw.trans htasksPayload
  have htailCodeRaw :=
    binaryFormulaCode_and_length_le_local tokensFormula tasksFormula
  have htotalCodeRaw :=
    binaryFormulaCode_and_length_le_local runningFormula
      (tokensFormula ⋏ tasksFormula)
  have hcode :
      (binaryFormulaCode
        (runningFormula ⋏ (tokensFormula ⋏ tasksFormula))).length <=
          syntaxFormulaQuantifierAssemblySyntaxEnvelope tokenCount
            numericBound bitBound := by
    unfold syntaxFormulaQuantifierAssemblySyntaxEnvelope
    omega
  have hassembly :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      quantifierFixedZeroValuation runningFormula tokensFormula tasksFormula
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (taskConsQuantifierFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound)
      (syntaxFormulaQuantifierAssemblySyntaxEnvelope tokenCount numericBound
        bitBound)
      (by
        unfold syntaxFormulaQuantifierAssemblySyntaxEnvelope
        omega)
      hclosed hcode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxFormulaQuantifierClosedFormula_alignment
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity).symm parts) <= _
  unfold syntaxFormulaQuantifierFullyFixedPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, runningFormula,
    tokensFormula, tasksFormula, runningCertificate, tokensCertificate,
    tasksCertificate, tailCertificate, parts,
    quantifierFixedZeroValuation] using hparts.trans hassembly

#print axioms
  compactUnifiedParserSyntaxFormulaQuantifierClosedFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierFullyFixedBounds
