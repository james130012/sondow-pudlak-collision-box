import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryPublicBounds
import integration.FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListDropOneRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryModularCertificateFullyFixedBounds
import integration.FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds

/-!
# Fully fixed modular binary syntax-formula transition

The genuine running, token drop-one, task drop-two, and two task-row
certificates are assembled at the original five-leaf binary formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryModularFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryBodyFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryModularCertificateFullyFixedBounds

private def binaryModularZeroValuation : Nat -> Nat := fun _ => 0

def syntaxFormulaBinaryAssemblySyntaxEnvelope
    (numericBound bitBound : Nat) : Nat :=
  compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound +
    dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound +
    taskDropTwoCompleteFullyFixedPayloadPolynomial numericBound bitBound +
    2 * syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound +
    4 * (binaryNatCode 4).length + 1

def syntaxFormulaBinaryModularFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridFiveConjunctionGeneralPayloadEnvelope
    (syntaxFormulaBinaryAssemblySyntaxEnvelope numericBound bitBound)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound)
    (dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (taskDropTwoCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound)
    (syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound)

noncomputable def
    compactUnifiedParserSyntaxFormulaBinaryModularCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity) :
    CheckedHybridValuationBoundedFormulaCertificate binaryModularZeroValuation
      (compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width
        tokenCount current next tailBoundary tailCount binderArity) := by
  rcases hgraph with ⟨hrunning, htokens, hdrop, htaskZero, htaskOne⟩
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  let tokenDropCertificate :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 htokens
  let taskDropCertificate :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      tailBoundary tailCount 2 hdrop
  let taskZeroCertificate :=
    syntaxTaskAtRowsBinaryModularCertificateOfGraph tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 0 binderArity htaskZero
  let taskOneCertificate :=
    syntaxTaskAtRowsBinaryModularCertificateOfGraph tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 1 binderArity htaskOne
  let parts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      runningCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        tokenDropCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          taskDropCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            taskZeroCertificate taskOneCertificate)))
  exact .cast
    (compactUnifiedParserSyntaxFormulaBinaryClosedFormula_alignment tokenTable
      width tokenCount current next tailBoundary tailCount binderArity).symm
    parts

theorem
    compactUnifiedParserSyntaxFormulaBinaryClosedFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) :
    (compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width
      tokenCount current next tailBoundary tailCount
      binderArity).freeVariables = ∅ := by
  rw [compactUnifiedParserSyntaxFormulaBinaryClosedFormula_alignment]
  unfold compactUnifiedParserSyntaxFormulaBinaryExplicitFormula
  unfold compactBinaryNatRunningStatusSliceClosedFormula
  simp only [LO.FirstOrder.Semiformula.freeVariables_and]
  rw [fiveShortNumeralRewritingFormula_freeVariables_eq_empty]
  rw [compactAdditiveNatListDropOneRowsClosedFormula_freeVariables_eq_empty]
  rw [
    compactAdditiveSyntaxTaskListDropTwoRowsClosedFormula_freeVariables_eq_empty]
  rw [syntaxTaskAtRowsBinaryFullFormula_freeVariables_eq_empty,
    syntaxTaskAtRowsBinaryFullFormula_freeVariables_eq_empty]
  simp

theorem
    compactUnifiedParserSyntaxFormulaBinaryModularCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
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
        (compactUnifiedParserSyntaxFormulaBinaryModularCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity hgraph) <=
      syntaxFormulaBinaryModularFullyFixedPayloadEnvelope numericBound
        bitBound := by
  rcases hgraph with ⟨hrunning, htokens, hdrop, htaskZero, htaskOne⟩
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokenDropFormula :=
    compactAdditiveNatListDropFixedNumeralRowsClosedFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1
  let taskDropFormula :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
      width tokenCount next.tasksBoundary next.tasksCount tailBoundary
      tailCount 2
  let taskZeroFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (nativeNumeralTerm 0)
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0)
  let taskOneFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount (nativeNumeralTerm 1)
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0)
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  let tokenDropCertificate :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 htokens
  let taskDropCertificate :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      tailBoundary tailCount 2 hdrop
  let taskZeroCertificate :=
    syntaxTaskAtRowsBinaryModularCertificateOfGraph tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 0 binderArity htaskZero
  let taskOneCertificate :=
    syntaxTaskAtRowsBinaryModularCertificateOfGraph tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 1 binderArity htaskOne
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
  have hnextTasksCountSize :
      Nat.size next.tasksCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextSize (7 : Fin 8)
  have hrunning :
      hybridFormulaStructuralPayloadBound runningCertificate <=
        compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound := by
    dsimp only [runningCertificate]
    exact
      compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount next.tasksFinish next.finish numericBound
        bitBound hwidth hnextTasksFinish htokenTableSize hwidthSize
        htokenCountSize hnextTasksFinishSize hnextFinishSize hrunning
  have htokenPublic :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 htokens
  have htokenFixed :=
    compactAdditiveNatListDropOneRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount numericBound bitBound htokens
      hwidth htokenCount hcurrentTokensCount htokenTableSize
      hcurrentTokensBoundarySize hnextTokensBoundarySize hnumericSize
  have htoken :
      hybridFormulaStructuralPayloadBound tokenDropCertificate <=
        dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [tokenDropCertificate] using htokenPublic.trans htokenFixed
  have htaskPublic :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      tailBoundary tailCount 2 hdrop
  have htaskFixed :=
    compactAdditiveSyntaxTaskListDropTwoRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      tailBoundary tailCount numericBound bitBound hdrop hwidth htokenCount
      hnextTasksCount htokenTableSize hnextTasksBoundarySize
      htailBoundarySize hnumericSize
  have htask :
      hybridFormulaStructuralPayloadBound taskDropCertificate <=
        taskDropTwoCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [taskDropCertificate] using htaskPublic.trans htaskFixed
  have hzero :
      hybridFormulaStructuralPayloadBound taskZeroCertificate <=
        syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound := by
    dsimp only [taskZeroCertificate]
    exact
      syntaxTaskAtRowsBinaryModularCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount next.tasksBoundary next.tasksCount 0
        binderArity numericBound bitBound (by omega) htaskZero hwidth
        htokenCount hnextTasksCount htokenTableSize hwidthSize htokenCountSize
        hnextTasksBoundarySize hnextTasksCountSize hbinderSize
  have hone :
      hybridFormulaStructuralPayloadBound taskOneCertificate <=
        syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound := by
    dsimp only [taskOneCertificate]
    exact
      syntaxTaskAtRowsBinaryModularCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount next.tasksBoundary next.tasksCount 1
        binderArity numericBound bitBound (by omega) htaskOne hwidth
        htokenCount hnextTasksCount htokenTableSize hwidthSize htokenCountSize
        hnextTasksBoundarySize hnextTasksCountSize hbinderSize
  let pair :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      taskZeroCertificate taskOneCertificate
  have hpair := transparentHybridConjunctionPayloadBound_le
    taskZeroCertificate taskOneCertificate _ _ hzero hone
  let taskTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      taskDropCertificate pair
  have htaskTail := transparentHybridConjunctionPayloadBound_le
    taskDropCertificate pair _ _ htask hpair
  let tokenTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokenDropCertificate taskTail
  have htokenTail := transparentHybridConjunctionPayloadBound_le
    tokenDropCertificate taskTail _ _ htoken htaskTail
  let parts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      runningCertificate tokenTail
  have hparts := transparentHybridConjunctionPayloadBound_le
    runningCertificate tokenTail _ _ hrunning htokenTail
  have hrunningClosed : runningFormula.freeVariables = ∅ := by
    dsimp only [runningFormula]
    unfold compactBinaryNatRunningStatusSliceClosedFormula
    exact fiveShortNumeralRewritingFormula_freeVariables_eq_empty
      _ tokenTable width tokenCount next.tasksFinish next.finish
  have htokenClosed : tokenDropFormula.freeVariables = ∅ := by
    dsimp only [tokenDropFormula]
    exact compactAdditiveNatListDropOneRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount
  have htaskClosed : taskDropFormula.freeVariables = ∅ := by
    dsimp only [taskDropFormula]
    exact
      compactAdditiveSyntaxTaskListDropTwoRowsClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount next.tasksBoundary next.tasksCount
        tailBoundary tailCount
  have hzeroClosed : taskZeroFormula.freeVariables = ∅ := by
    dsimp only [taskZeroFormula]
    exact syntaxTaskAtRowsBinaryFullFormula_freeVariables_eq_empty tokenTable
      width tokenCount next.tasksBoundary next.tasksCount 0 binderArity
  have honeClosed : taskOneFormula.freeVariables = ∅ := by
    dsimp only [taskOneFormula]
    exact syntaxTaskAtRowsBinaryFullFormula_freeVariables_eq_empty tokenTable
      width tokenCount next.tasksBoundary next.tasksCount 1 binderArity
  have hclosed :
      (runningFormula ⋏
        (tokenDropFormula ⋏
          (taskDropFormula ⋏ (taskZeroFormula ⋏ taskOneFormula)))).freeVariables =
        ∅ := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_and, hrunningClosed,
      htokenClosed, htaskClosed, hzeroClosed, honeClosed]
    simp
  have hrunningCode :
      (binaryFormulaCode runningFormula).length <=
        compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound := by
    simpa only [runningFormula] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        runningCertificate).trans hrunning
  have htokenCode :
      (binaryFormulaCode tokenDropFormula).length <=
        dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [tokenDropFormula] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        tokenDropCertificate).trans htoken
  have htaskCode :
      (binaryFormulaCode taskDropFormula).length <=
        taskDropTwoCompleteFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [taskDropFormula] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        taskDropCertificate).trans htask
  have hzeroCode :
      (binaryFormulaCode taskZeroFormula).length <=
        syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound := by
    simpa only [taskZeroFormula] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        taskZeroCertificate).trans hzero
  have honeCode :
      (binaryFormulaCode taskOneFormula).length <=
        syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound := by
    simpa only [taskOneFormula] using
      (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
        taskOneCertificate).trans hone
  have hpairCode := binaryFormulaCode_and_length_le_local taskZeroFormula
    taskOneFormula
  have htaskTailCode := binaryFormulaCode_and_length_le_local taskDropFormula
    (taskZeroFormula ⋏ taskOneFormula)
  have htokenTailCode := binaryFormulaCode_and_length_le_local
    tokenDropFormula (taskDropFormula ⋏ taskZeroFormula ⋏ taskOneFormula)
  have htotalCode := binaryFormulaCode_and_length_le_local runningFormula
    (tokenDropFormula ⋏ taskDropFormula ⋏ taskZeroFormula ⋏ taskOneFormula)
  have hcode :
      (binaryFormulaCode
        (runningFormula ⋏
          (tokenDropFormula ⋏
            (taskDropFormula ⋏
              (taskZeroFormula ⋏ taskOneFormula))))).length <=
        syntaxFormulaBinaryAssemblySyntaxEnvelope numericBound bitBound := by
    unfold syntaxFormulaBinaryAssemblySyntaxEnvelope
    omega
  have hassembly :=
    transparentHybridFiveConjunctionPayloadEnvelope_le_closedGeneral
      binaryModularZeroValuation runningFormula tokenDropFormula
      taskDropFormula taskZeroFormula taskOneFormula
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (dropOneRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (taskDropTwoCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound)
      (syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound)
      (syntaxFormulaBinaryAssemblySyntaxEnvelope numericBound bitBound)
      (by
        unfold syntaxFormulaBinaryAssemblySyntaxEnvelope
        omega)
      hclosed hcode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxFormulaBinaryClosedFormula_alignment
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity).symm parts) <= _
  unfold syntaxFormulaBinaryModularFullyFixedPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, runningFormula,
    tokenDropFormula, taskDropFormula, taskZeroFormula, taskOneFormula,
    runningCertificate, tokenDropCertificate, taskDropCertificate,
    taskZeroCertificate, taskOneCertificate, pair, taskTail, tokenTail, parts,
    binaryModularZeroValuation] using hparts.trans hassembly

#print axioms
  compactUnifiedParserSyntaxFormulaBinaryModularCertificateOfGraph
#print axioms
  compactUnifiedParserSyntaxFormulaBinaryClosedFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  compactUnifiedParserSyntaxFormulaBinaryModularCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryModularFullyFixedBounds
