import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraph
import integration.FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineBranchRowsCompleteness
import integration.FoundationCompactNumericListedDirectSimpleCombineTransitionRowsCompleteness
import integration.FoundationCompactNumericListedDirectAllShiftCombineRuleRowsCompleteness
import integration.FoundationCompactNumericListedDirectExsCutCombineRuleRowsCompleteness

/-!
# Converse constructors for the 93-column verifier-combine graph

The common canonical frame and one exact branch row contain precisely the five
conjuncts of the public fixed-column combine graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectSimpleCombineTransitionRows
open FoundationCompactNumericListedDirectAllShiftCombineRuleRows
open FoundationCompactNumericListedDirectExsCutCombineRuleRows
open FoundationCompactNumericListedDirectVerifierCombineFailureRows
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineBranchRowsCompleteness

theorem CompactAdditiveStructuredListElementRowLayouts.childResult_components_at
    {tokenTable width tokenCount boundaryTable : Nat}
    {values : List CompactNumericChildResult}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        boundaryTable values)
    (index : Nat) (hindex : index < values.length) :
    ∃ gammaBoundary boolValue,
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary (values.getI index).1 ∧
      boolValue = compactAdditiveBoolTag (values.getI index).2 := by
  rcases hrows index hindex with
    ⟨_start, _hstart, _finish, _hfinish,
      _hstartEntry, _hfinishEntry, hvalue⟩
  rcases hvalue with
    ⟨_gammaFinish, gammaBoundary, boolValue,
      _hproduct, _hgammaLayout, hgammaRows, hboolValue,
      _hboolLayout, _hgammaSize⟩
  exact ⟨gammaBoundary, boolValue, hgammaRows, hboolValue⟩

theorem CompactNumericVerifierCombineStateGraph.of_canonical_frame_branch
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {nextStatus : Option Bool}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {ruleWitness : CompactNumericVerifierCombineRuleWitness}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens task tasks
      source target nextStatus currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hbranch : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      taskCoordinates.witnessFinish taskCoordinates.witnessCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool ruleWitness) :
    CompactNumericVerifierCombineStateGraph
      tokenTable width tokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      ruleWitness := by
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, hhead, hframe, _hfields⟩
  rcases hcurrentPackage with
    ⟨_hcurrentStart, _hcurrentFinish,
      _hcurrentProof, _hcurrentCertificate,
      _hcurrentTaskLayout, _hcurrentTaskRows,
      _hcurrentValueLayout, _hcurrentValueRows,
      _hcurrentTaskCount, _hcurrentValueCount,
      _hcurrentTaskTableWidth, _hcurrentTaskValueBound,
      _hcurrentValueTableWidth, _hcurrentValueValueBound,
      _hcurrentStatus, hcurrentCore⟩
  rcases hnextPackage with
    ⟨_hnextStart, _hnextFinish,
      _hnextProof, _hnextCertificate,
      _hnextTaskLayout, _hnextTaskRows,
      _hnextValueLayout, _hnextValueRows,
      _hnextTaskCount, _hnextValueCount,
      _hnextTaskTableWidth, _hnextTaskValueBound,
      _hnextValueTableWidth, _hnextValueValueBound,
      _hnextStatus, hnextCore⟩
  exact ⟨hcurrentCore, hnextCore, hhead, hframe, hbranch⟩

theorem CompactNumericVerifierCombineStateGraph.of_simple_rows
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue resultBoolValue : Nat}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens task tasks
      source target none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hrows : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue) :
    CompactNumericVerifierCombineStateGraph
      tokenTable width tokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      (compactNumericVerifierSimpleCombineRuleWitness
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue resultBoolValue) := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨_hcurrentPackage, hnextPackage, _hhead, _hframe, _hfields⟩
  have hnextStatusTag : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hnextPackage rfl
  have hbranchZero := CompactNumericVerifierCombineBranchRows.of_simple_rows
    (witnessFinish := taskCoordinates.witnessFinish)
    (witnessCount := taskCoordinates.witnessCount)
    (nextStatusBool := nextCoordinates.statusBool) hrows
  have hbranch : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      taskCoordinates.witnessFinish taskCoordinates.witnessCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool
      (compactNumericVerifierSimpleCombineRuleWitness
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue resultBoolValue) := by
    simpa only [hnextStatusTag] using hbranchZero
  exact CompactNumericVerifierCombineStateGraph.of_canonical_frame_branch
    hframeSaved hbranch

theorem CompactNumericVerifierCombineStateGraph.exists_of_simple_rows
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue resultBoolValue : Nat}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens task tasks
      source target none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hrows : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness := by
  exact ⟨compactNumericVerifierSimpleCombineRuleWitness
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue resultBoolValue,
    CompactNumericVerifierCombineStateGraph.of_simple_rows
      hframePackage hrows⟩

theorem CompactNumericVerifierCombineStateGraph.of_all_shift_rows
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue : Nat}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens task tasks
      source target none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hrows : CompactNumericAllShiftCombineRuleRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue) :
    CompactNumericVerifierCombineStateGraph
      tokenTable width tokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      (compactNumericVerifierAllShiftCombineRuleWitness
        premiseGammaCount premiseGammaBoundary premiseBoolValue
        formulaBoundary formulaBoundarySize
        freedStart freedFinish freedBoundary freedCount freedBoundarySize
        freeStateBoundary freeStateCount
        shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound freeTableWidth freeValueBound resultBoolValue) := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨_hcurrentPackage, hnextPackage, _hhead, _hframe, _hfields⟩
  have hnextStatusTag : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hnextPackage rfl
  let ruleWitness := compactNumericVerifierAllShiftCombineRuleWitness
    premiseGammaCount premiseGammaBoundary premiseBoolValue
    formulaBoundary formulaBoundarySize
    freedStart freedFinish freedBoundary freedCount freedBoundarySize
    freeStateBoundary freeStateCount
    shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
    emptyStart emptyFinish emptyBoundary emptyBoundarySize
    shiftWitnessBound freeTableWidth freeValueBound resultBoolValue
  have hbranchZero : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      taskCoordinates.witnessFinish taskCoordinates.witnessCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound 0 nextCoordinates.statusBool
      ruleWitness := by
    exact Or.inr <| Or.inl ⟨hrows, rfl⟩
  have hbranch : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      taskCoordinates.witnessFinish taskCoordinates.witnessCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool ruleWitness := by
    simpa only [hnextStatusTag] using hbranchZero
  simpa only [ruleWitness] using
    (CompactNumericVerifierCombineStateGraph.of_canonical_frame_branch
      hframeSaved hbranch)

theorem CompactNumericVerifierCombineStateGraph.exists_of_all_shift_rows
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue : Nat}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens task tasks
      source target none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hrows : CompactNumericAllShiftCombineRuleRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨_hcurrentPackage, hnextPackage, _hhead, _hframe, _hfields⟩
  have hnextStatusTag : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hnextPackage rfl
  rcases CompactNumericVerifierCombineBranchRows.exists_of_all_shift_rows
      (secondFinish := taskCoordinates.secondFinish)
      (secondCount := taskCoordinates.secondCount)
      (witnessFinish := taskCoordinates.witnessFinish)
      (witnessCount := taskCoordinates.witnessCount)
      (nextStatusBool := nextCoordinates.statusBool) hrows with
    ⟨ruleWitness, hbranchZero⟩
  have hbranch : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      taskCoordinates.witnessFinish taskCoordinates.witnessCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool ruleWitness := by
    simpa only [hnextStatusTag] using hbranchZero
  exact ⟨ruleWitness,
    CompactNumericVerifierCombineStateGraph.of_canonical_frame_branch
      hframeSaved hbranch⟩

theorem CompactNumericVerifierCombineStateGraph.of_exs_cut_rows
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound resultBoolValue : Nat}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens task tasks
      source target none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hrows : CompactNumericExsCutCombineRuleRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.witnessFinish
        taskCoordinates.witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
        transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue) :
    CompactNumericVerifierCombineStateGraph
      tokenTable width tokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      (compactNumericVerifierExsCutCombineRuleWitness
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue
        formulaBoundary formulaBoundarySize
        transformedStart transformedFinish transformedBoundary
        transformedCount transformedBoundarySize
        transformStateBoundary transformStateCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        transformTableWidth transformValueBound resultBoolValue) := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨_hcurrentPackage, hnextPackage, _hhead, _hframe, _hfields⟩
  have hnextStatusTag : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hnextPackage rfl
  let ruleWitness := compactNumericVerifierExsCutCombineRuleWitness
    rightGammaCount rightGammaBoundary rightBoolValue
    leftGammaCount leftGammaBoundary leftBoolValue
    formulaBoundary formulaBoundarySize
    transformedStart transformedFinish transformedBoundary
    transformedCount transformedBoundarySize
    transformStateBoundary transformStateCount
    emptyStart emptyFinish emptyBoundary emptyBoundarySize
    transformTableWidth transformValueBound resultBoolValue
  have hbranchZero : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      taskCoordinates.witnessFinish taskCoordinates.witnessCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound 0 nextCoordinates.statusBool
      ruleWitness := by
    exact Or.inr <| Or.inr <| Or.inl ⟨hrows, rfl⟩
  have hbranch : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      taskCoordinates.witnessFinish taskCoordinates.witnessCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool ruleWitness := by
    simpa only [hnextStatusTag] using hbranchZero
  simpa only [ruleWitness] using
    (CompactNumericVerifierCombineStateGraph.of_canonical_frame_branch
      hframeSaved hbranch)

theorem CompactNumericVerifierCombineStateGraph.exists_of_exs_cut_rows
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound resultBoolValue : Nat}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens task tasks
      source target none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hrows : CompactNumericExsCutCombineRuleRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.witnessFinish
        taskCoordinates.witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
        transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨_hcurrentPackage, hnextPackage, _hhead, _hframe, _hfields⟩
  have hnextStatusTag : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hnextPackage rfl
  rcases CompactNumericVerifierCombineBranchRows.exists_of_exs_cut_rows
      (secondCount := taskCoordinates.secondCount)
      (nextStatusBool := nextCoordinates.statusBool) hrows with
    ⟨ruleWitness, hbranchZero⟩
  have hbranch : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      taskCoordinates.witnessFinish taskCoordinates.witnessCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool ruleWitness := by
    simpa only [hnextStatusTag] using hbranchZero
  exact ⟨ruleWitness,
    CompactNumericVerifierCombineStateGraph.of_canonical_frame_branch
      hframeSaved hbranch⟩

theorem CompactNumericVerifierCombineStateGraph.of_failure_rows
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens task tasks
      source target (some false) currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hrows : CompactNumericVerifierCombineFailureRows
      tokenTable width tokenCount taskCoordinates.tag
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound 1 0) :
    CompactNumericVerifierCombineStateGraph
      tokenTable width tokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      compactNumericVerifierFailureCombineRuleWitness := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨_hcurrentPackage, hnextPackage, _hhead, _hframe, _hfields⟩
  have hnextStatus :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTagBool_eq_some
      hnextPackage (result := false) rfl
  have hnextStatusTag : nextCoordinates.statusTag = 1 := hnextStatus.1
  have hnextStatusBool : nextCoordinates.statusBool = 0 := by
    simpa [FoundationCompactNumericListedDirectAdditiveTypeCanonical.compactAdditiveBoolTag]
      using hnextStatus.2
  have hbranchFixed :=
    CompactNumericVerifierCombineBranchRows.of_failure_rows
      (gammaFinish := taskCoordinates.gammaFinish)
      (gammaCount := taskCoordinates.gammaCount)
      (gammaBoundary := taskCoordinates.gammaBoundary)
      (firstFinish := taskCoordinates.firstFinish)
      (firstCount := taskCoordinates.firstCount)
      (secondFinish := taskCoordinates.secondFinish)
      (secondCount := taskCoordinates.secondCount)
      (witnessFinish := taskCoordinates.witnessFinish)
      (witnessCount := taskCoordinates.witnessCount) hrows
  have hbranch : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      taskCoordinates.witnessFinish taskCoordinates.witnessCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool
      compactNumericVerifierFailureCombineRuleWitness := by
    simpa only [hnextStatusTag, hnextStatusBool] using hbranchFixed
  exact CompactNumericVerifierCombineStateGraph.of_canonical_frame_branch
    hframeSaved hbranch

theorem CompactNumericVerifierCombineStateGraph.exists_of_failure_rows
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens task tasks
      source target (some false) currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hrows : CompactNumericVerifierCombineFailureRows
      tokenTable width tokenCount taskCoordinates.tag
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound 1 0) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness := by
  exact ⟨compactNumericVerifierFailureCombineRuleWitness,
    CompactNumericVerifierCombineStateGraph.of_failure_rows
      hframePackage hrows⟩

#print axioms
  CompactNumericVerifierCombineStateGraph.of_canonical_frame_branch
#print axioms
  CompactAdditiveStructuredListElementRowLayouts.childResult_components_at
#print axioms CompactNumericVerifierCombineStateGraph.of_simple_rows
#print axioms CompactNumericVerifierCombineStateGraph.exists_of_simple_rows
#print axioms
  CompactNumericVerifierCombineStateGraph.exists_of_all_shift_rows
#print axioms
  CompactNumericVerifierCombineStateGraph.exists_of_exs_cut_rows
#print axioms CompactNumericVerifierCombineStateGraph.of_failure_rows
#print axioms CompactNumericVerifierCombineStateGraph.exists_of_failure_rows

end FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness
