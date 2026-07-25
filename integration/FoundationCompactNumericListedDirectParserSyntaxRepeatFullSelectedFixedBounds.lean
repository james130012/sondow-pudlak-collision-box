import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatFullGraphFixedBounds

/-! # Exact selected full Repeat certificates -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatFullSelectedFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaEnvironmentAlignment
open FoundationCompactNumericListedDirectParserSyntaxRepeatBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatZeroBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatPositiveBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFullGraphFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows

private abbrev repeatZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate.zeroValuation

noncomputable def repeatZeroOriginalBranchCertificate
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hrepeatZero : repeatCount = 0)
    (hsame : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      witness.tailBoundary witness.tailCount next.tasksBoundary
      next.tasksCount) :
    CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
      (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
        tokenCount next binderArity repeatCount witness) :=
  CheckedHybridValuationBoundedFormulaCertificate.cast
    (repeatBranchExplicitFormula_alignment tokenTable width tokenCount next
      binderArity repeatCount witness).symm
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := repeatPositiveBranchFormula tokenTable width tokenCount next
        binderArity repeatCount witness)
      (repeatZeroBranchCertificate tokenTable width tokenCount next repeatCount
        witness hrepeatZero hsame))

noncomputable def repeatPositiveOriginalBranchCertificate
    (tokenTable width tokenCount : Nat)
    (next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hrepeatSuccessor : repeatCount = witness.decrementedCount + 1)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount witness.tailBoundary witness.tailCount 2)
    (htaskZero : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 0 0 binderArity 0)
    (htaskOne : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 1 2 binderArity
        witness.decrementedCount) :
    CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
      (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
        tokenCount next binderArity repeatCount witness) :=
  CheckedHybridValuationBoundedFormulaCertificate.cast
    (repeatBranchExplicitFormula_alignment tokenTable width tokenCount next
      binderArity repeatCount witness).symm
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := repeatZeroBranchFormula tokenTable width tokenCount next
        repeatCount witness)
      (repeatPositiveBranchCertificate tokenTable width tokenCount next
        binderArity repeatCount witness hrepeatSuccessor hdrop htaskZero
        htaskOne))

noncomputable def repeatFullGraphCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (hcurrent : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (hnext : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize 2 binderArity repeatCount)
    (branchCertificate :
      CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
        (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
          tokenCount next binderArity repeatCount witness)) :
    CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
        current next binderArity repeatCount witness) :=
  CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactUnifiedParserSyntaxRepeatClosedFormula_alignment tokenTable width
      tokenCount current next binderArity repeatCount witness).symm
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksFinish current.finish hcurrent)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount next.tasksFinish next.finish hnext)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount next.tokensBoundary next.tokensCount htokens)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (parserSyntaxRepeatUnconsGraphCertificate tokenTable width tokenCount
              current.tasksBoundary current.tasksCount witness.tailBoundary
              witness.tailCount witness.tailBoundarySize binderArity repeatCount
              huncons)
            branchCertificate))))

theorem repeatFullGraphCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (branchCertificate :
      CheckedHybridValuationBoundedFormulaCertificate repeatZeroValuation
        (compactUnifiedParserSyntaxRepeatBranchExplicitFormula tokenTable width
          tokenCount next binderArity repeatCount witness))
    (branchResource numericBound bitBound : Nat)
    (hcurrent : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (hnext : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize 2 binderArity repeatCount)
    (hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <= branchResource)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcurrentTasksFinishValue : current.tasksFinish <= numericBound)
    (hnextTasksFinishValue : next.tasksFinish <= numericBound)
    (hcurrentTokensCountValue : current.tokensCount <= numericBound)
    (hcurrentTasksCountValue : current.tasksCount <= numericBound)
    (htailCountValue : witness.tailCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentTasksFinishSize : Nat.size current.tasksFinish <= bitBound)
    (hcurrentFinishSize : Nat.size current.finish <= bitBound)
    (hnextTasksFinishSize : Nat.size next.tasksFinish <= bitBound)
    (hnextFinishSize : Nat.size next.finish <= bitBound)
    (hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound)
    (hnextTokensBoundarySize : Nat.size next.tokensBoundary <= bitBound)
    (hcurrentTasksBoundarySize :
      Nat.size current.tasksBoundary <= bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatFullGraphCertificate tokenTable width tokenCount current next
          binderArity repeatCount witness hcurrent hnext htokens huncons
          branchCertificate) <=
      repeatFullGraphPayloadEnvelope tokenCount numericBound bitBound
        branchResource := by
  unfold repeatFullGraphCertificate
  exact repeatGraphComponentsCertificate_structuralPayloadBound_le_fixed
    tokenTable width tokenCount current next binderArity repeatCount witness
    branchCertificate branchResource numericBound bitBound hcurrent hnext
    htokens huncons hbranch hsize hwidthValue htokenCountValue
    hcurrentTasksFinishValue hnextTasksFinishValue hcurrentTokensCountValue
    hcurrentTasksCountValue htailCountValue htableSize hwidthSize
    htokenCountSize hcurrentTasksFinishSize hcurrentFinishSize
    hnextTasksFinishSize hnextFinishSize hcurrentTokensBoundarySize
    hnextTokensBoundarySize hcurrentTasksBoundarySize htailBoundarySize
    hbinderSize hrepeatSize hnumericSize

theorem repeatZeroOriginalBranchCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hrepeatZero : repeatCount = 0)
    (hsame : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      witness.tailBoundary witness.tailCount next.tasksBoundary
      next.tasksCount)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htailCountValue : witness.tailCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htasksBoundarySize : Nat.size next.tasksBoundary <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatZeroOriginalBranchCertificate tokenTable width tokenCount next
          binderArity repeatCount witness hrepeatZero hsame) <=
      repeatSelectedBranchPayloadEnvelope bitBound
        (repeatZeroBranchPayloadEnvelope numericBound bitBound) := by
  unfold repeatZeroOriginalBranchCertificate
  exact
    repeatZeroSelectedBranchCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next binderArity repeatCount witness
      numericBound bitBound hrepeatZero hsame hsize hwidthValue
      htokenCountValue htailCountValue htableSize htailBoundarySize
      htasksBoundarySize hrepeatSize hnumericSize

theorem repeatPositiveOriginalBranchCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hrepeatSuccessor : repeatCount = witness.decrementedCount + 1)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount witness.tailBoundary witness.tailCount 2)
    (htaskZero : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 0 0 binderArity 0)
    (htaskOne : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 1 2 binderArity
        witness.decrementedCount)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htasksCountValue : next.tasksCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htasksBoundarySize : Nat.size next.tasksBoundary <= bitBound)
    (htasksCountSize : Nat.size next.tasksCount <= bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hdecrementedSize : Nat.size witness.decrementedCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatPositiveOriginalBranchCertificate tokenTable width tokenCount next
          binderArity repeatCount witness hrepeatSuccessor hdrop htaskZero
          htaskOne) <=
      repeatSelectedBranchPayloadEnvelope bitBound
        (repeatPositiveBranchPayloadEnvelope numericBound bitBound) := by
  unfold repeatPositiveOriginalBranchCertificate
  exact
    repeatPositiveSelectedBranchCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next binderArity repeatCount witness
      numericBound bitBound hrepeatSuccessor hdrop htaskZero htaskOne hsize
      hwidthValue htokenCountValue htasksCountValue htableSize hwidthSize
      htokenCountSize htasksBoundarySize htasksCountSize htailBoundarySize
      hbinderSize hrepeatSize hdecrementedSize hnumericSize

theorem repeatZeroFullGraphCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hcurrent : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (hnext : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize 2 binderArity repeatCount)
    (hrepeatZero : repeatCount = 0)
    (hsame : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      witness.tailBoundary witness.tailCount next.tasksBoundary
      next.tasksCount)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcurrentTasksFinishValue : current.tasksFinish <= numericBound)
    (hnextTasksFinishValue : next.tasksFinish <= numericBound)
    (hcurrentTokensCountValue : current.tokensCount <= numericBound)
    (hcurrentTasksCountValue : current.tasksCount <= numericBound)
    (htailCountValue : witness.tailCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentTasksFinishSize : Nat.size current.tasksFinish <= bitBound)
    (hcurrentFinishSize : Nat.size current.finish <= bitBound)
    (hnextTasksFinishSize : Nat.size next.tasksFinish <= bitBound)
    (hnextFinishSize : Nat.size next.finish <= bitBound)
    (hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound)
    (hnextTokensBoundarySize : Nat.size next.tokensBoundary <= bitBound)
    (hcurrentTasksBoundarySize :
      Nat.size current.tasksBoundary <= bitBound)
    (hnextTasksBoundarySize : Nat.size next.tasksBoundary <= bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    let branchCertificate :=
      repeatZeroOriginalBranchCertificate tokenTable width tokenCount next
        binderArity repeatCount witness hrepeatZero hsame
    hybridFormulaStructuralPayloadBound
        (repeatFullGraphCertificate tokenTable width tokenCount current next
          binderArity repeatCount witness hcurrent hnext htokens huncons
          branchCertificate) <=
      repeatFullGraphPayloadEnvelope tokenCount numericBound bitBound
        (repeatSelectedBranchPayloadEnvelope bitBound
          (repeatZeroBranchPayloadEnvelope numericBound bitBound)) := by
  dsimp only
  let branchCertificate :=
    repeatZeroOriginalBranchCertificate tokenTable width tokenCount next
      binderArity repeatCount witness hrepeatZero hsame
  have hbranch :=
    repeatZeroOriginalBranchCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next binderArity repeatCount witness
      numericBound bitBound hrepeatZero hsame hsize hwidthValue
      htokenCountValue htailCountValue htableSize htailBoundarySize
      hnextTasksBoundarySize hrepeatSize hnumericSize
  exact repeatFullGraphCertificate_structuralPayloadBound_le_fixed tokenTable
    width tokenCount current next binderArity repeatCount witness
    branchCertificate
    (repeatSelectedBranchPayloadEnvelope bitBound
      (repeatZeroBranchPayloadEnvelope numericBound bitBound))
    numericBound bitBound hcurrent hnext htokens huncons hbranch hsize
    hwidthValue htokenCountValue hcurrentTasksFinishValue
    hnextTasksFinishValue hcurrentTokensCountValue hcurrentTasksCountValue
    htailCountValue htableSize hwidthSize htokenCountSize
    hcurrentTasksFinishSize hcurrentFinishSize hnextTasksFinishSize
    hnextFinishSize hcurrentTokensBoundarySize hnextTokensBoundarySize
    hcurrentTasksBoundarySize htailBoundarySize hbinderSize hrepeatSize
    hnumericSize

theorem repeatPositiveFullGraphCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hcurrent : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      current.tasksFinish current.finish)
    (hnext : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      next.tasksFinish next.finish)
    (htokens : CompactAdditiveNatListSameRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount next.tokensBoundary
      next.tokensCount)
    (huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize 2 binderArity repeatCount)
    (hrepeatSuccessor : repeatCount = witness.decrementedCount + 1)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount witness.tailBoundary witness.tailCount 2)
    (htaskZero : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 0 0 binderArity 0)
    (htaskOne : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      next.tasksBoundary next.tasksCount 1 2 binderArity
        witness.decrementedCount)
    (hsize : forall coordinate : Fin 25,
      Nat.size
        (compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf tokenTable width
          tokenCount current next binderArity repeatCount witness coordinate) <=
        bitBound)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcurrentTasksFinishValue : current.tasksFinish <= numericBound)
    (hnextTasksFinishValue : next.tasksFinish <= numericBound)
    (hcurrentTokensCountValue : current.tokensCount <= numericBound)
    (hcurrentTasksCountValue : current.tasksCount <= numericBound)
    (hnextTasksCountValue : next.tasksCount <= numericBound)
    (htailCountValue : witness.tailCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentTasksFinishSize : Nat.size current.tasksFinish <= bitBound)
    (hcurrentFinishSize : Nat.size current.finish <= bitBound)
    (hnextTasksFinishSize : Nat.size next.tasksFinish <= bitBound)
    (hnextFinishSize : Nat.size next.finish <= bitBound)
    (hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound)
    (hnextTokensBoundarySize : Nat.size next.tokensBoundary <= bitBound)
    (hcurrentTasksBoundarySize :
      Nat.size current.tasksBoundary <= bitBound)
    (hnextTasksBoundarySize : Nat.size next.tasksBoundary <= bitBound)
    (hnextTasksCountSize : Nat.size next.tasksCount <= bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hdecrementedSize : Nat.size witness.decrementedCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    let branchCertificate :=
      repeatPositiveOriginalBranchCertificate tokenTable width tokenCount next
        binderArity repeatCount witness hrepeatSuccessor hdrop htaskZero
        htaskOne
    hybridFormulaStructuralPayloadBound
        (repeatFullGraphCertificate tokenTable width tokenCount current next
          binderArity repeatCount witness hcurrent hnext htokens huncons
          branchCertificate) <=
      repeatFullGraphPayloadEnvelope tokenCount numericBound bitBound
        (repeatSelectedBranchPayloadEnvelope bitBound
          (repeatPositiveBranchPayloadEnvelope numericBound bitBound)) := by
  dsimp only
  let branchCertificate :=
    repeatPositiveOriginalBranchCertificate tokenTable width tokenCount next
      binderArity repeatCount witness hrepeatSuccessor hdrop htaskZero htaskOne
  have hbranch :=
    repeatPositiveOriginalBranchCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next binderArity repeatCount witness
      numericBound bitBound hrepeatSuccessor hdrop htaskZero htaskOne hsize
      hwidthValue htokenCountValue hnextTasksCountValue htableSize hwidthSize
      htokenCountSize hnextTasksBoundarySize hnextTasksCountSize
      htailBoundarySize hbinderSize hrepeatSize hdecrementedSize hnumericSize
  exact repeatFullGraphCertificate_structuralPayloadBound_le_fixed tokenTable
    width tokenCount current next binderArity repeatCount witness
    branchCertificate
    (repeatSelectedBranchPayloadEnvelope bitBound
      (repeatPositiveBranchPayloadEnvelope numericBound bitBound))
    numericBound bitBound hcurrent hnext htokens huncons hbranch hsize
    hwidthValue htokenCountValue hcurrentTasksFinishValue
    hnextTasksFinishValue hcurrentTokensCountValue hcurrentTasksCountValue
    htailCountValue htableSize hwidthSize htokenCountSize
    hcurrentTasksFinishSize hcurrentFinishSize hnextTasksFinishSize
    hnextFinishSize hcurrentTokensBoundarySize hnextTokensBoundarySize
    hcurrentTasksBoundarySize htailBoundarySize hbinderSize hrepeatSize
    hnumericSize

#print axioms repeatFullGraphCertificate_structuralPayloadBound_le_fixed
#print axioms
  repeatZeroOriginalBranchCertificate_structuralPayloadBound_le_fixed
#print axioms
  repeatPositiveOriginalBranchCertificate_structuralPayloadBound_le_fixed
#print axioms
  repeatZeroFullGraphCertificate_structuralPayloadBound_le_fixed
#print axioms
  repeatPositiveFullGraphCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatFullSelectedFixedBounds
