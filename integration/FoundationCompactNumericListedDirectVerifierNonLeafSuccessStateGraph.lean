import integration.FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineStateExactness
import integration.FoundationCompactNumericListedDirectVerifierCombineSimpleStateGraphCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineExsCutStateGraphCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineAllShiftStateGraphCompleteness
import integration.FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
import integration.FoundationCompactNumericListedDirectVerifierStepCases

/-!
# Direct bounded graph for a successful non-leaf verifier step

The existing 93-column combine graph already contains every tag `3` through
`9` rule branch.  This module only selects its public-success endpoint: the
next status is `none`, represented by status tag zero.  It deliberately does
not duplicate any rule-row construction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierNonLeafSuccessStateGraph

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTraceListLayout
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRows
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierCombineSimpleStateGraphCompleteness
open FoundationCompactNumericListedDirectVerifierCombineExsCutStateGraphCompleteness
open FoundationCompactNumericListedDirectVerifierCombineAllShiftStateGraphCompleteness
open FoundationCompactNumericListedDirectSimpleCombineTransitionRows
open FoundationCompactNumericListedDirectAllShiftCombineRuleRows
open FoundationCompactNumericListedDirectExsCutCombineRuleRows
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineCanonicalFrameCompleteness
open FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

def CompactNumericVerifierNonLeafSuccessStateGraph
    (tokenTable width tokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness : CompactNumericVerifierTaskSizeWitness)
    (ruleWitness : CompactNumericVerifierCombineRuleWitness) : Prop :=
  CompactNumericVerifierCombineStateGraph
      tokenTable width tokenCount
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness ruleWitness ∧
    nextCoordinates.statusTag = 0

def compactNumericVerifierNonLeafSuccessStateGraphDef :
    𝚺₀.Semisentence 93 := .mkSigma
  (compactNumericVerifierCombineStateGraphDef.val ⋏ “(#36 = 0)”)
  (by simp)

def CompactNumericVerifierNonLeafSuccessStateGraphAt
    (environment : Fin 93 → Nat) : Prop :=
  CompactNumericVerifierNonLeafSuccessStateGraph
      (environment 0) (environment 1) (environment 2)
      (compactNumericVerifierStateRowCoordinatesOf
        (environment 3) (environment 4)
        (environment 5) (environment 6)
        (environment 7) (environment 8)
        (environment 9) (environment 10) (environment 11)
        (environment 12) (environment 13) (environment 14)
        (environment 15) (environment 16) (environment 17))
      (compactNumericVerifierStateRowCoordinatesOf
        (environment 24) (environment 25)
        (environment 26) (environment 27)
        (environment 28) (environment 29)
        (environment 30) (environment 31) (environment 32)
        (environment 33) (environment 34) (environment 35)
        (environment 36) (environment 37) (environment 38))
      { taskBoundarySize := environment 18
        valueBoundarySize := environment 19
        taskTableWidth := environment 20
        taskValueBound := environment 21
        valueTableWidth := environment 22
        valueValueBound := environment 23 }
      { taskBoundarySize := environment 39
        valueBoundarySize := environment 40
        taskTableWidth := environment 41
        taskValueBound := environment 42
        valueTableWidth := environment 43
        valueValueBound := environment 44 }
      (compactNumericVerifierTaskRowCoordinatesOf
        (environment 45) (environment 46) (environment 47)
        (environment 48) (environment 49) (environment 50)
        (environment 51) (environment 52)
        (environment 53) (environment 54)
        (environment 55) (environment 56) (environment 57))
      { gammaBoundarySize := environment 58 }
      (compactNumericVerifierCombineRuleWitnessOf
        (environment 59) (environment 60) (environment 61)
        (environment 62) (environment 63) (environment 64)
        (environment 65) (environment 66)
        (environment 67) (environment 68) (environment 69)
        (environment 70) (environment 71) (environment 72)
        (environment 73) (environment 74)
        (environment 75) (environment 76) (environment 77)
        (environment 78) (environment 79)
        (environment 80) (environment 81) (environment 82)
        (environment 83) (environment 84)
        (environment 85) (environment 86)
        (environment 87) (environment 88) (environment 89) (environment 90)
        (environment 91) (environment 92))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
@[simp] theorem compactNumericVerifierNonLeafSuccessStateGraphDef_spec
    (environment : Fin 93 → Nat) :
    compactNumericVerifierNonLeafSuccessStateGraphDef.val.Evalb environment ↔
      CompactNumericVerifierNonLeafSuccessStateGraphAt environment := by
  have hcombineEnvironment :
      compactNumericVerifierCombineStateGraphEnvironment
        (environment 0) (environment 1) (environment 2)
        (environment 3) (environment 4)
        (environment 5) (environment 6)
        (environment 7) (environment 8)
        (environment 9) (environment 10) (environment 11)
        (environment 12) (environment 13) (environment 14)
        (environment 15) (environment 16) (environment 17)
        (environment 18) (environment 19)
        (environment 20) (environment 21)
        (environment 22) (environment 23)
        (environment 24) (environment 25)
        (environment 26) (environment 27)
        (environment 28) (environment 29)
        (environment 30) (environment 31) (environment 32)
        (environment 33) (environment 34) (environment 35)
        (environment 36) (environment 37) (environment 38)
        (environment 39) (environment 40)
        (environment 41) (environment 42)
        (environment 43) (environment 44)
        (environment 45) (environment 46) (environment 47)
        (environment 48) (environment 49) (environment 50)
        (environment 51) (environment 52)
        (environment 53) (environment 54)
        (environment 55) (environment 56) (environment 57)
        (environment 58)
        (environment 59) (environment 60) (environment 61)
        (environment 62) (environment 63) (environment 64)
        (environment 65) (environment 66)
        (environment 67) (environment 68) (environment 69)
        (environment 70) (environment 71) (environment 72)
        (environment 73) (environment 74)
        (environment 75) (environment 76) (environment 77)
        (environment 78) (environment 79)
        (environment 80) (environment 81)
        (environment 82) (environment 83) (environment 84) (environment 85)
        (environment 86) (environment 87)
        (environment 88) (environment 89) (environment 90) (environment 91)
        (environment 92) = environment := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcombine := compactNumericVerifierCombineStateGraphDef_spec
    (environment 0) (environment 1) (environment 2)
    (environment 3) (environment 4)
    (environment 5) (environment 6)
    (environment 7) (environment 8)
    (environment 9) (environment 10) (environment 11)
    (environment 12) (environment 13) (environment 14)
    (environment 15) (environment 16) (environment 17)
    (environment 18) (environment 19)
    (environment 20) (environment 21)
    (environment 22) (environment 23)
    (environment 24) (environment 25)
    (environment 26) (environment 27)
    (environment 28) (environment 29)
    (environment 30) (environment 31) (environment 32)
    (environment 33) (environment 34) (environment 35)
    (environment 36) (environment 37) (environment 38)
    (environment 39) (environment 40)
    (environment 41) (environment 42)
    (environment 43) (environment 44)
    (environment 45) (environment 46) (environment 47)
    (environment 48) (environment 49) (environment 50)
    (environment 51) (environment 52)
    (environment 53) (environment 54)
    (environment 55) (environment 56) (environment 57)
    (environment 58)
    (environment 59) (environment 60) (environment 61)
    (environment 62) (environment 63) (environment 64)
    (environment 65) (environment 66)
    (environment 67) (environment 68) (environment 69)
    (environment 70) (environment 71) (environment 72)
    (environment 73) (environment 74)
    (environment 75) (environment 76) (environment 77)
    (environment 78) (environment 79)
    (environment 80) (environment 81)
    (environment 82) (environment 83) (environment 84) (environment 85)
    (environment 86) (environment 87)
    (environment 88) (environment 89) (environment 90) (environment 91)
    (environment 92)
  rw [hcombineEnvironment] at hcombine
  change
    (compactNumericVerifierCombineStateGraphDef.val.Evalb environment ∧
      environment 36 = 0) ↔ (_ ∧ environment 36 = 0)
  exact and_congr hcombine Iff.rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
theorem compactNumericVerifierNonLeafSuccessStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierNonLeafSuccessStateGraphDef.val := by
  simp [compactNumericVerifierNonLeafSuccessStateGraphDef]

def CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (backTokens : List Nat) : Prop :=
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), none)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  ∃ currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      ruleWitness,
    CompactNumericVerifierNonLeafSuccessStateGraph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness ruleWitness

theorem CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_and
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion leftConclusion : List (List Nat))
    (rightValid leftValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
      proofTokens certificateTokens
      (3, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks
      ((rightConclusion, rightValid) :: (leftConclusion, leftValid) :: tail)
      ((Gamma, compactAndRuleCheck
        (Gamma, firstFormula, secondFormula,
          (leftConclusion, leftValid), rightConclusion, rightValid)) :: tail)
      [] := by
  dsimp only [CompactNumericVerifierCanonicalNonLeafSuccessStateGraph]
  have hframeExists :=
    CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back
      proofTokens certificateTokens
      (3, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks
      ((rightConclusion, rightValid) :: (leftConclusion, leftValid) :: tail)
      ((Gamma, compactAndRuleCheck
        (Gamma, firstFormula, secondFormula,
          (leftConclusion, leftValid), rightConclusion, rightValid)) :: tail)
      none [] (by simp)
  dsimp only at hframeExists
  rcases hframeExists with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframe⟩
  have hstatus : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hframe.2.1 rfl
  rcases CompactNumericVerifierCombineStateGraph.exists_of_and_frame hframe with
    ⟨ruleWitness, hgraph, _hruleSize⟩
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness,
    ruleWitness, hgraph, hstatus⟩

theorem CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_or
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion : List (List Nat)) (rightValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
      proofTokens certificateTokens
      (4, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactOrRuleCheck
        (Gamma, firstFormula, secondFormula,
          rightConclusion, rightValid)) :: tail)
      [] := by
  dsimp only [CompactNumericVerifierCanonicalNonLeafSuccessStateGraph]
  have hframeExists :=
    CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back
      proofTokens certificateTokens
      (4, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactOrRuleCheck
        (Gamma, firstFormula, secondFormula,
          rightConclusion, rightValid)) :: tail)
      none [] (by simp)
  dsimp only at hframeExists
  rcases hframeExists with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframe⟩
  have hstatus : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hframe.2.1 rfl
  rcases CompactNumericVerifierCombineStateGraph.exists_of_or_frame hframe with
    ⟨ruleWitness, hgraph, _hruleSize⟩
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness,
    ruleWitness, hgraph, hstatus⟩

theorem CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_wk
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion : List (List Nat)) (rightValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
      proofTokens certificateTokens
      (7, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactWkRuleCheck
        (Gamma, rightConclusion, rightValid)) :: tail)
      [] := by
  dsimp only [CompactNumericVerifierCanonicalNonLeafSuccessStateGraph]
  have hframeExists :=
    CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back
      proofTokens certificateTokens
      (7, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactWkRuleCheck
        (Gamma, rightConclusion, rightValid)) :: tail)
      none [] (by simp)
  dsimp only at hframeExists
  rcases hframeExists with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframe⟩
  have hstatus : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hframe.2.1 rfl
  rcases CompactNumericVerifierCombineStateGraph.exists_of_wk_frame hframe with
    ⟨ruleWitness, hgraph, _hruleSize⟩
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness,
    ruleWitness, hgraph, hstatus⟩

theorem CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_exs
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (formula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion : List (List Nat)) (rightValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
      proofTokens certificateTokens
      (6, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactExsRuleCheck
        (Gamma, formula, witness, rightConclusion, rightValid)) :: tail)
      (compactNumericExsCombineAuxiliaryTokens formula witness) := by
  let task : CompactNumericVerifierTask :=
    (6, (Gamma, (formula, (secondFormula, (witness, suffix)))))
  let source : List CompactNumericChildResult :=
    (rightConclusion, rightValid) :: tail
  let target : List CompactNumericChildResult :=
    (Gamma, compactExsRuleCheck
      (Gamma, formula, witness, rightConclusion, rightValid)) :: tail
  let transformed :=
    (compactFormulaSubstitutionExact 1 (witness, formula)).getD []
  let empty : List Nat := []
  let trace := compactFormulaTransformStateTrace (2, witness)
    (compactSyntaxRunFuelBound formula)
    (compactFormulaTransformInitialState 1 formula)
  let transformedTokens := compactAdditiveEncode transformed
  let emptyTokens := compactAdditiveEncode empty
  let traceTokens := compactAdditiveEncode trace
  let backTokens := transformedTokens ++ emptyTokens ++ traceTokens
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), none)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let statePrefix := currentTokens ++ nextTokens
  let tokens := statePrefix ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let transformedStart := statePrefix.length
  let transformedFinish := transformedStart + transformedTokens.length
  let afterTransformed := statePrefix ++ transformedTokens
  let emptyStart := afterTransformed.length
  let emptyFinish := emptyStart + emptyTokens.length
  let afterEmpty := afterTransformed ++ emptyTokens
  let traceStart := afterEmpty.length
  let traceFinish := traceStart + traceTokens.length
  let transformStateBoundary :=
    compactFormulaTransformStateBoundaryTable
      tokens.length (traceStart + 1) trace
  change CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
    proofTokens certificateTokens task tasks source target backTokens
  have htransformedRaw := compactAdditiveNatListDirectLayout_canonical
    statePrefix transformed (emptyTokens ++ traceTokens)
  have htransformed : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      transformedStart transformedFinish transformed := by
    simpa only [tokens, width, statePrefix, backTokens, transformedTokens,
      transformedStart, transformedFinish, List.append_assoc] using
      htransformedRaw
  have hemptyRaw := compactAdditiveNatListDirectLayout_canonical
    afterTransformed empty traceTokens
  have hempty : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      emptyStart emptyFinish empty := by
    simpa only [tokens, width, statePrefix, backTokens, transformedTokens,
      emptyTokens, afterTransformed, emptyStart, emptyFinish,
      List.append_assoc] using hemptyRaw
  have htraceRaw := compactFormulaTransformStateListDirectLayout_canonical
    afterEmpty trace []
  have htrace :
      CompactAdditiveStructuredListLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          traceStart trace.length traceFinish transformStateBoundary ∧
        CompactFormulaTransformStateListRowLayouts
          (compactFixedWidthTableCode width tokens) width tokens.length
          transformStateBoundary trace ∧
        Nat.size transformStateBoundary ≤ (trace.length + 1) * tokens.length := by
    simpa only [tokens, width, statePrefix, backTokens, transformedTokens,
      emptyTokens, traceTokens, afterTransformed, afterEmpty,
      traceStart, traceFinish, transformStateBoundary,
      compactFormulaTransformStateBoundaryTable, List.append_nil,
      List.append_assoc] using htraceRaw
  have hframeExists :=
    CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back
      proofTokens certificateTokens task tasks source target none backTokens
      (by simp [task])
  dsimp only at hframeExists
  rcases hframeExists with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframeRaw⟩
  have hframe : CompactNumericVerifierCombineCanonicalFramePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      0 currentTokens.length currentTokens.length
      (currentTokens.length + nextTokens.length)
      proofTokens certificateTokens task tasks source target none
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness := by
    simpa only [currentState, nextState, currentTokens, nextTokens,
      statePrefix, tokens, width] using hframeRaw
  have hstatus : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hframe.2.1 rfl
  rcases CompactNumericVerifierCombineStateGraph.exists_of_exs_frame
      (transformedStart := transformedStart)
      (transformedFinish := transformedFinish)
      (transformStateBoundary := transformStateBoundary)
      (emptyStart := emptyStart) (emptyFinish := emptyFinish)
      hframe htransformed hempty ⟨htrace.2.1, htrace.2.2⟩ with
    ⟨ruleWitness, hgraph, _hruleBounds⟩
  dsimp only [CompactNumericVerifierCanonicalNonLeafSuccessStateGraph]
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness,
    ruleWitness, hgraph, hstatus⟩

theorem CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_cut
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (formula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion leftConclusion : List (List Nat))
    (rightValid leftValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
      proofTokens certificateTokens
      (9, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks
      ((rightConclusion, rightValid) :: (leftConclusion, leftValid) :: tail)
      ((Gamma, compactCutRuleCheck
        (Gamma, formula, (leftConclusion, leftValid),
          rightConclusion, rightValid)) :: tail)
      (compactNumericCutCombineAuxiliaryTokens formula) := by
  let task : CompactNumericVerifierTask :=
    (9, (Gamma, (formula, (secondFormula, (witness, suffix)))))
  let source : List CompactNumericChildResult :=
    (rightConclusion, rightValid) :: (leftConclusion, leftValid) :: tail
  let target : List CompactNumericChildResult :=
    (Gamma, compactCutRuleCheck
      (Gamma, formula, (leftConclusion, leftValid),
        rightConclusion, rightValid)) :: tail
  let transformed := (compactFormulaNegationExact 0 formula).getD []
  let empty : List Nat := []
  let trace := compactFormulaTransformStateTrace (3, [])
    (compactSyntaxRunFuelBound formula)
    (compactFormulaTransformInitialState 0 formula)
  let transformedTokens := compactAdditiveEncode transformed
  let emptyTokens := compactAdditiveEncode empty
  let traceTokens := compactAdditiveEncode trace
  let backTokens := transformedTokens ++ emptyTokens ++ traceTokens
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), none)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let statePrefix := currentTokens ++ nextTokens
  let tokens := statePrefix ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let transformedStart := statePrefix.length
  let transformedFinish := transformedStart + transformedTokens.length
  let afterTransformed := statePrefix ++ transformedTokens
  let emptyStart := afterTransformed.length
  let emptyFinish := emptyStart + emptyTokens.length
  let afterEmpty := afterTransformed ++ emptyTokens
  let traceStart := afterEmpty.length
  let traceFinish := traceStart + traceTokens.length
  let transformStateBoundary :=
    compactFormulaTransformStateBoundaryTable
      tokens.length (traceStart + 1) trace
  change CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
    proofTokens certificateTokens task tasks source target backTokens
  have htransformedRaw := compactAdditiveNatListDirectLayout_canonical
    statePrefix transformed (emptyTokens ++ traceTokens)
  have htransformed : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      transformedStart transformedFinish transformed := by
    simpa only [tokens, width, statePrefix, backTokens, transformedTokens,
      transformedStart, transformedFinish, List.append_assoc] using
      htransformedRaw
  have hemptyRaw := compactAdditiveNatListDirectLayout_canonical
    afterTransformed empty traceTokens
  have hempty : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      emptyStart emptyFinish empty := by
    simpa only [tokens, width, statePrefix, backTokens, transformedTokens,
      emptyTokens, afterTransformed, emptyStart, emptyFinish,
      List.append_assoc] using hemptyRaw
  have htraceRaw := compactFormulaTransformStateListDirectLayout_canonical
    afterEmpty trace []
  have htrace :
      CompactAdditiveStructuredListLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          traceStart trace.length traceFinish transformStateBoundary ∧
        CompactFormulaTransformStateListRowLayouts
          (compactFixedWidthTableCode width tokens) width tokens.length
          transformStateBoundary trace ∧
        Nat.size transformStateBoundary ≤ (trace.length + 1) * tokens.length := by
    simpa only [tokens, width, statePrefix, backTokens, transformedTokens,
      emptyTokens, traceTokens, afterTransformed, afterEmpty,
      traceStart, traceFinish, transformStateBoundary,
      compactFormulaTransformStateBoundaryTable, List.append_nil,
      List.append_assoc] using htraceRaw
  have hframeExists :=
    CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back
      proofTokens certificateTokens task tasks source target none backTokens
      (by simp [task])
  dsimp only at hframeExists
  rcases hframeExists with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframeRaw⟩
  have hframe : CompactNumericVerifierCombineCanonicalFramePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      0 currentTokens.length currentTokens.length
      (currentTokens.length + nextTokens.length)
      proofTokens certificateTokens task tasks source target none
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness := by
    simpa only [currentState, nextState, currentTokens, nextTokens,
      statePrefix, tokens, width] using hframeRaw
  have hstatus : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hframe.2.1 rfl
  rcases CompactNumericVerifierCombineStateGraph.exists_of_cut_frame
      (transformedStart := transformedStart)
      (transformedFinish := transformedFinish)
      (transformStateBoundary := transformStateBoundary)
      (emptyStart := emptyStart) (emptyFinish := emptyFinish)
      hframe htransformed hempty ⟨htrace.2.1, htrace.2.2⟩ with
    ⟨ruleWitness, hgraph, _hruleBounds⟩
  dsimp only [CompactNumericVerifierCanonicalNonLeafSuccessStateGraph]
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness,
    ruleWitness, hgraph, hstatus⟩

theorem CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_shift
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (premise : List (List Nat)) (premiseValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
      proofTokens certificateTokens
      (8, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((premise, premiseValid) :: tail)
      ((Gamma, compactShiftRuleCheck (Gamma, premise, premiseValid)) :: tail)
      (compactNumericShiftCombineAuxiliaryTokens premise) := by
  let task : CompactNumericVerifierTask :=
    (8, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
  let source : List CompactNumericChildResult :=
    (premise, premiseValid) :: tail
  let target : List CompactNumericChildResult :=
    (Gamma, compactShiftRuleCheck (Gamma, premise, premiseValid)) :: tail
  let empty : List Nat := []
  let candidates := premise.map fun formula =>
    (compactFormulaShiftExact 0 formula).getD []
  let shifted := (compactFormulaShiftExactList premise).getD []
  let traces := compactFormulaShiftTraceList premise
  let emptyTokens := compactAdditiveEncode empty
  let candidateTokens := compactAdditiveEncode candidates
  let shiftedTokens := compactAdditiveEncode shifted
  let traceTokens := compactAdditiveEncode traces
  let backTokens := emptyTokens ++ candidateTokens ++ shiftedTokens ++ traceTokens
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), none)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let statePrefix := currentTokens ++ nextTokens
  let tokens := statePrefix ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let emptyStart := statePrefix.length
  let emptyFinish := emptyStart + emptyTokens.length
  let afterEmpty := statePrefix ++ emptyTokens
  let candidateStart := afterEmpty.length
  let candidateFinish := candidateStart + candidateTokens.length
  let afterCandidate := afterEmpty ++ candidateTokens
  let shiftedStart := afterCandidate.length
  let shiftedFinish := shiftedStart + shiftedTokens.length
  let afterShifted := afterCandidate ++ shiftedTokens
  let traceStart := afterShifted.length
  let traceFinish := traceStart + traceTokens.length
  change CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
    proofTokens certificateTokens task tasks source target backTokens
  have hemptyRaw := compactAdditiveNatListDirectLayout_canonical
    statePrefix empty (candidateTokens ++ shiftedTokens ++ traceTokens)
  have hempty : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      emptyStart emptyFinish empty := by
    simpa only [tokens, width, statePrefix, backTokens, emptyTokens,
      emptyStart, emptyFinish, List.append_assoc] using hemptyRaw
  have hcandidateRaw := compactAdditiveNatListListDirectLayout_canonical
    afterEmpty candidates (shiftedTokens ++ traceTokens)
  have hcandidate : CompactAdditiveNatListListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      candidateStart candidateFinish candidates := by
    simpa only [tokens, width, statePrefix, backTokens, emptyTokens,
      candidateTokens, afterEmpty, candidateStart, candidateFinish,
      List.append_assoc] using hcandidateRaw
  rcases hcandidate with
    ⟨candidateBoundary, hcandidateStructure,
      hcandidateRows, hcandidateSize⟩
  have hshiftedRaw := compactAdditiveNatListListDirectLayout_canonical
    afterCandidate shifted traceTokens
  have hshifted : CompactAdditiveNatListListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      shiftedStart shiftedFinish shifted := by
    simpa only [tokens, width, statePrefix, backTokens, emptyTokens,
      candidateTokens, shiftedTokens, afterEmpty, afterCandidate,
      shiftedStart, shiftedFinish, List.append_assoc] using hshiftedRaw
  rcases hshifted with
    ⟨shiftedBoundary, hshiftedStructure, hshiftedRows, hshiftedSize⟩
  have htracesRaw := compactFormulaTransformTraceListDirectLayout_canonical
    afterShifted traces []
  have htraces : CompactFormulaTransformTraceListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      traceStart traceFinish traces := by
    simpa only [tokens, width, statePrefix, backTokens, emptyTokens,
      candidateTokens, shiftedTokens, traceTokens, afterEmpty,
      afterCandidate, afterShifted, traceStart, traceFinish,
      List.append_nil, List.append_assoc] using htracesRaw
  rcases htraces with
    ⟨traceBoundary, _htraceStructure, htraceRows, _htraceSize⟩
  have hshiftTraces : ∀ index (_hindex : index < premise.length),
      ∃ stateBoundary,
        CompactFormulaTransformStateListRowLayouts
          (compactFixedWidthTableCode width tokens) width tokens.length
          stateBoundary
          (compactFormulaTransformStateTrace (1, [])
            (compactSyntaxRunFuelBound (premise.getI index))
            (compactFormulaTransformInitialState 0 (premise.getI index))) ∧
        Nat.size stateBoundary ≤
          ((compactFormulaTransformStateTrace (1, [])
              (compactSyntaxRunFuelBound (premise.getI index))
              (compactFormulaTransformInitialState 0
                (premise.getI index))).length + 1) * tokens.length := by
    intro index hindex
    have htraceIndex : index < traces.length := by
      simpa [traces, compactFormulaShiftTraceList] using hindex
    rcases CompactFormulaTransformTraceListRowLayouts.trace_rows_with_size
        htraceRows index htraceIndex with
      ⟨stateBoundary, hstateRows, hstateSize⟩
    refine ⟨stateBoundary, ?_, ?_⟩
    · simpa only [traces, compactFormulaShiftTraceList_getI
        premise index hindex] using hstateRows
    · simpa only [traces, compactFormulaShiftTraceList_getI
        premise index hindex] using hstateSize
  have htokenCount : 1 ≤ tokens.length := by
    simpa only [tokens, statePrefix, currentTokens, nextTokens] using
      compactNumericVerifierStatePairPrefix_tokenCount_pos
        currentState nextState backTokens
  have hframeExists :=
    CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back
      proofTokens certificateTokens task tasks source target none backTokens
      (by simp [task])
  dsimp only at hframeExists
  rcases hframeExists with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframeRaw⟩
  have hframe : CompactNumericVerifierCombineCanonicalFramePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      0 currentTokens.length currentTokens.length
      (currentTokens.length + nextTokens.length)
      proofTokens certificateTokens task tasks source target none
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness := by
    simpa only [currentState, nextState, currentTokens, nextTokens,
      statePrefix, tokens, width] using hframeRaw
  have hstatus : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hframe.2.1 rfl
  rcases CompactNumericVerifierCombineStateGraph.exists_of_shift_frame
      (shiftCandidateBoundary := candidateBoundary)
      (shiftedBoundary := shiftedBoundary)
      (emptyStart := emptyStart) (emptyFinish := emptyFinish)
      hframe hempty
        ⟨hcandidateStructure, hcandidateRows, hcandidateSize⟩
        ⟨hshiftedStructure, hshiftedRows, hshiftedSize⟩
        hshiftTraces htokenCount with
    ⟨ruleWitness, hgraph, _hcritical⟩
  dsimp only [CompactNumericVerifierCanonicalNonLeafSuccessStateGraph]
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness,
    ruleWitness, hgraph, hstatus⟩

theorem CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_all
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (formula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (premise : List (List Nat)) (premiseValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
      proofTokens certificateTokens
      (5, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks ((premise, premiseValid) :: tail)
      ((Gamma, compactAllRuleCheck
        (Gamma, formula, premise, premiseValid)) :: tail)
      (compactNumericAllCombineAuxiliaryTokens Gamma formula) := by
  let task : CompactNumericVerifierTask :=
    (5, (Gamma, (formula, (secondFormula, (witness, suffix)))))
  let source : List CompactNumericChildResult :=
    (premise, premiseValid) :: tail
  let target : List CompactNumericChildResult :=
    (Gamma, compactAllRuleCheck
      (Gamma, formula, premise, premiseValid)) :: tail
  let freed := (compactFormulaFreeExact formula).getD []
  let empty : List Nat := []
  let freeTrace := compactFormulaTransformStateTrace (0, [])
    (compactSyntaxRunFuelBound formula)
    (compactFormulaTransformInitialState 1 formula)
  let candidates := Gamma.map fun candidateFormula =>
    (compactFormulaShiftExact 0 candidateFormula).getD []
  let shifted := (compactFormulaShiftExactList Gamma).getD []
  let shiftTraces := compactFormulaShiftTraceList Gamma
  let freedTokens := compactAdditiveEncode freed
  let emptyTokens := compactAdditiveEncode empty
  let freeTraceTokens := compactAdditiveEncode freeTrace
  let candidateTokens := compactAdditiveEncode candidates
  let shiftedTokens := compactAdditiveEncode shifted
  let shiftTraceTokens := compactAdditiveEncode shiftTraces
  let backTokens := freedTokens ++ emptyTokens ++ freeTraceTokens ++
    candidateTokens ++ shiftedTokens ++ shiftTraceTokens
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), none)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let statePrefix := currentTokens ++ nextTokens
  let tokens := statePrefix ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let freedStart := statePrefix.length
  let freedFinish := freedStart + freedTokens.length
  let afterFreed := statePrefix ++ freedTokens
  let emptyStart := afterFreed.length
  let emptyFinish := emptyStart + emptyTokens.length
  let afterEmpty := afterFreed ++ emptyTokens
  let freeTraceStart := afterEmpty.length
  let freeTraceFinish := freeTraceStart + freeTraceTokens.length
  let afterFreeTrace := afterEmpty ++ freeTraceTokens
  let candidateStart := afterFreeTrace.length
  let candidateFinish := candidateStart + candidateTokens.length
  let afterCandidate := afterFreeTrace ++ candidateTokens
  let shiftedStart := afterCandidate.length
  let shiftedFinish := shiftedStart + shiftedTokens.length
  let afterShifted := afterCandidate ++ shiftedTokens
  let shiftTraceStart := afterShifted.length
  let shiftTraceFinish := shiftTraceStart + shiftTraceTokens.length
  let freeStateBoundary :=
    compactFormulaTransformStateBoundaryTable
      tokens.length (freeTraceStart + 1) freeTrace
  change CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
    proofTokens certificateTokens task tasks source target backTokens
  have hfreedRaw := compactAdditiveNatListDirectLayout_canonical
    statePrefix freed
      (emptyTokens ++ freeTraceTokens ++ candidateTokens ++ shiftedTokens ++
        shiftTraceTokens)
  have hfreed : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      freedStart freedFinish freed := by
    simpa only [tokens, width, statePrefix, backTokens, freedTokens,
      freedStart, freedFinish, List.append_assoc] using hfreedRaw
  have hemptyRaw := compactAdditiveNatListDirectLayout_canonical
    afterFreed empty
      (freeTraceTokens ++ candidateTokens ++ shiftedTokens ++ shiftTraceTokens)
  have hempty : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      emptyStart emptyFinish empty := by
    simpa only [tokens, width, statePrefix, backTokens, freedTokens,
      emptyTokens, afterFreed, emptyStart, emptyFinish,
      List.append_assoc] using hemptyRaw
  have hfreeTraceRaw :=
    compactFormulaTransformStateListDirectLayout_canonical
      afterEmpty freeTrace (candidateTokens ++ shiftedTokens ++ shiftTraceTokens)
  have hfreeTrace :
      CompactAdditiveStructuredListLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          freeTraceStart freeTrace.length freeTraceFinish freeStateBoundary ∧
        CompactFormulaTransformStateListRowLayouts
          (compactFixedWidthTableCode width tokens) width tokens.length
          freeStateBoundary freeTrace ∧
        Nat.size freeStateBoundary ≤ (freeTrace.length + 1) * tokens.length := by
    simpa only [tokens, width, statePrefix, backTokens, freedTokens,
      emptyTokens, freeTraceTokens, afterFreed, afterEmpty,
      freeTraceStart, freeTraceFinish, freeStateBoundary,
      compactFormulaTransformStateBoundaryTable, List.append_assoc] using
      hfreeTraceRaw
  have hcandidateRaw := compactAdditiveNatListListDirectLayout_canonical
    afterFreeTrace candidates (shiftedTokens ++ shiftTraceTokens)
  have hcandidate : CompactAdditiveNatListListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      candidateStart candidateFinish candidates := by
    simpa only [tokens, width, statePrefix, backTokens, freedTokens,
      emptyTokens, freeTraceTokens, candidateTokens, afterFreed, afterEmpty,
      afterFreeTrace, candidateStart, candidateFinish,
      List.append_assoc] using hcandidateRaw
  rcases hcandidate with
    ⟨candidateBoundary, hcandidateStructure,
      hcandidateRows, hcandidateSize⟩
  have hshiftedRaw := compactAdditiveNatListListDirectLayout_canonical
    afterCandidate shifted shiftTraceTokens
  have hshifted : CompactAdditiveNatListListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      shiftedStart shiftedFinish shifted := by
    simpa only [tokens, width, statePrefix, backTokens, freedTokens,
      emptyTokens, freeTraceTokens, candidateTokens, shiftedTokens,
      afterFreed, afterEmpty, afterFreeTrace, afterCandidate,
      shiftedStart, shiftedFinish, List.append_assoc] using hshiftedRaw
  rcases hshifted with
    ⟨shiftedBoundary, hshiftedStructure, hshiftedRows, hshiftedSize⟩
  have hshiftTracesRaw :=
    compactFormulaTransformTraceListDirectLayout_canonical
      afterShifted shiftTraces []
  have hshiftTracesLayout : CompactFormulaTransformTraceListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      shiftTraceStart shiftTraceFinish shiftTraces := by
    simpa only [tokens, width, statePrefix, backTokens, freedTokens,
      emptyTokens, freeTraceTokens, candidateTokens, shiftedTokens,
      shiftTraceTokens, afterFreed, afterEmpty, afterFreeTrace,
      afterCandidate, afterShifted, shiftTraceStart, shiftTraceFinish,
      List.append_nil, List.append_assoc] using hshiftTracesRaw
  rcases hshiftTracesLayout with
    ⟨_shiftTraceBoundary, _hshiftTraceStructure,
      hshiftTraceRows, _hshiftTraceSize⟩
  have hshiftTraces : ∀ index (_hindex : index < Gamma.length),
      ∃ stateBoundary,
        CompactFormulaTransformStateListRowLayouts
          (compactFixedWidthTableCode width tokens) width tokens.length
          stateBoundary
          (compactFormulaTransformStateTrace (1, [])
            (compactSyntaxRunFuelBound (Gamma.getI index))
            (compactFormulaTransformInitialState 0 (Gamma.getI index))) ∧
        Nat.size stateBoundary ≤
          ((compactFormulaTransformStateTrace (1, [])
              (compactSyntaxRunFuelBound (Gamma.getI index))
              (compactFormulaTransformInitialState 0
                (Gamma.getI index))).length + 1) * tokens.length := by
    intro index hindex
    have htraceIndex : index < shiftTraces.length := by
      simpa [shiftTraces, compactFormulaShiftTraceList] using hindex
    rcases CompactFormulaTransformTraceListRowLayouts.trace_rows_with_size
        hshiftTraceRows index htraceIndex with
      ⟨stateBoundary, hstateRows, hstateSize⟩
    refine ⟨stateBoundary, ?_, ?_⟩
    · simpa only [shiftTraces, compactFormulaShiftTraceList_getI
        Gamma index hindex] using hstateRows
    · simpa only [shiftTraces, compactFormulaShiftTraceList_getI
        Gamma index hindex] using hstateSize
  have htokenCount : 1 ≤ tokens.length := by
    simpa only [tokens, statePrefix, currentTokens, nextTokens] using
      compactNumericVerifierStatePairPrefix_tokenCount_pos
        currentState nextState backTokens
  have hframeExists :=
    CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back
      proofTokens certificateTokens task tasks source target none backTokens
      (by simp [task])
  dsimp only at hframeExists
  rcases hframeExists with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframeRaw⟩
  have hframe : CompactNumericVerifierCombineCanonicalFramePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      0 currentTokens.length currentTokens.length
      (currentTokens.length + nextTokens.length)
      proofTokens certificateTokens task tasks source target none
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness := by
    simpa only [currentState, nextState, currentTokens, nextTokens,
      statePrefix, tokens, width] using hframeRaw
  have hstatus : nextCoordinates.statusTag = 0 :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTag_eq_zero
      hframe.2.1 rfl
  rcases CompactNumericVerifierCombineStateGraph.exists_of_all_frame
      (freedStart := freedStart) (freedFinish := freedFinish)
      (freeStateBoundary := freeStateBoundary)
      (shiftCandidateBoundary := candidateBoundary)
      (shiftedBoundary := shiftedBoundary)
      (emptyStart := emptyStart) (emptyFinish := emptyFinish)
      hframe hfreed hempty hfreeTrace.2
        ⟨hcandidateStructure, hcandidateRows, hcandidateSize⟩
        ⟨hshiftedStructure, hshiftedRows, hshiftedSize⟩
        hshiftTraces htokenCount with
    ⟨ruleWitness, hgraph, _hcritical⟩
  dsimp only [CompactNumericVerifierCanonicalNonLeafSuccessStateGraph]
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness,
    ruleWitness, hgraph, hstatus⟩

theorem exists_compactNumericVerifierNonLeafSuccessStateGraph_of_success
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (nextTasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (next : CompactNumericVerifierState)
    (hsuccess : CompactNumericCombineSuccessCase task
      ((proofTokens, certificateTokens), (nextTasks, source)) next) :
    ∃ target backTokens,
      next = (((proofTokens, certificateTokens), (nextTasks, target)), none) ∧
      CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
        proofTokens certificateTokens task nextTasks source target backTokens := by
  rcases hsuccess with ⟨combined, htransition, hnext⟩
  rcases task with
    ⟨tag, ⟨Gamma,
      ⟨firstFormula, ⟨secondFormula, ⟨witness, suffix⟩⟩⟩⟩⟩
  by_cases htag3 : tag = 3
  · subst tag
    cases source with
    | nil => simp [compactNumericCombineTransition] at htransition
    | cons right rest =>
        rcases right with ⟨rightConclusion, rightValid⟩
        cases rest with
        | nil => simp [compactNumericCombineTransition] at htransition
        | cons left tail =>
            rcases left with ⟨leftConclusion, leftValid⟩
            have hcombined : combined =
                ((Gamma, compactAndRuleCheck
                  (Gamma, firstFormula, secondFormula,
                    (leftConclusion, leftValid),
                    rightConclusion, rightValid)), tail) := by
              simpa [compactNumericCombineTransition] using htransition.symm
            subst combined
            refine ⟨(Gamma, compactAndRuleCheck
              (Gamma, firstFormula, secondFormula,
                (leftConclusion, leftValid),
                rightConclusion, rightValid)) :: tail, [], ?_, ?_⟩
            · simpa using hnext
            · exact CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_and
                proofTokens certificateTokens Gamma
                  firstFormula secondFormula witness suffix nextTasks
                  rightConclusion leftConclusion rightValid leftValid tail
  by_cases htag4 : tag = 4
  · subst tag
    cases source with
    | nil => simp [compactNumericCombineTransition] at htransition
    | cons right tail =>
        rcases right with ⟨rightConclusion, rightValid⟩
        have hcombined : combined =
            ((Gamma, compactOrRuleCheck
              (Gamma, firstFormula, secondFormula,
                rightConclusion, rightValid)), tail) := by
          simpa [compactNumericCombineTransition] using htransition.symm
        subst combined
        refine ⟨(Gamma, compactOrRuleCheck
          (Gamma, firstFormula, secondFormula,
            rightConclusion, rightValid)) :: tail, [], ?_, ?_⟩
        · simpa using hnext
        · exact CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_or
            proofTokens certificateTokens Gamma
              firstFormula secondFormula witness suffix nextTasks
              rightConclusion rightValid tail
  by_cases htag5 : tag = 5
  · subst tag
    cases source with
    | nil => simp [compactNumericCombineTransition] at htransition
    | cons premise tail =>
        rcases premise with ⟨premise, premiseValid⟩
        have hcombined : combined =
            ((Gamma, compactAllRuleCheck
              (Gamma, firstFormula, premise, premiseValid)), tail) := by
          simpa [compactNumericCombineTransition] using htransition.symm
        subst combined
        refine ⟨(Gamma, compactAllRuleCheck
          (Gamma, firstFormula, premise, premiseValid)) :: tail,
          compactNumericAllCombineAuxiliaryTokens Gamma firstFormula,
          ?_, ?_⟩
        · simpa using hnext
        · exact CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_all
            proofTokens certificateTokens Gamma
              firstFormula secondFormula witness suffix nextTasks
              premise premiseValid tail
  by_cases htag6 : tag = 6
  · subst tag
    cases source with
    | nil => simp [compactNumericCombineTransition] at htransition
    | cons right tail =>
        rcases right with ⟨rightConclusion, rightValid⟩
        have hcombined : combined =
            ((Gamma, compactExsRuleCheck
              (Gamma, firstFormula, witness,
                rightConclusion, rightValid)), tail) := by
          simpa [compactNumericCombineTransition] using htransition.symm
        subst combined
        refine ⟨(Gamma, compactExsRuleCheck
          (Gamma, firstFormula, witness,
            rightConclusion, rightValid)) :: tail,
          compactNumericExsCombineAuxiliaryTokens firstFormula witness,
          ?_, ?_⟩
        · simpa using hnext
        · exact CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_exs
            proofTokens certificateTokens Gamma
              firstFormula secondFormula witness suffix nextTasks
              rightConclusion rightValid tail
  by_cases htag7 : tag = 7
  · subst tag
    cases source with
    | nil => simp [compactNumericCombineTransition] at htransition
    | cons right tail =>
        rcases right with ⟨rightConclusion, rightValid⟩
        have hcombined : combined =
            ((Gamma, compactWkRuleCheck
              (Gamma, rightConclusion, rightValid)), tail) := by
          simpa [compactNumericCombineTransition] using htransition.symm
        subst combined
        refine ⟨(Gamma, compactWkRuleCheck
          (Gamma, rightConclusion, rightValid)) :: tail, [], ?_, ?_⟩
        · simpa using hnext
        · exact CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_wk
            proofTokens certificateTokens Gamma
              firstFormula secondFormula witness suffix nextTasks
              rightConclusion rightValid tail
  by_cases htag8 : tag = 8
  · subst tag
    cases source with
    | nil => simp [compactNumericCombineTransition] at htransition
    | cons premise tail =>
        rcases premise with ⟨premise, premiseValid⟩
        have hcombined : combined =
            ((Gamma, compactShiftRuleCheck
              (Gamma, premise, premiseValid)), tail) := by
          simpa [compactNumericCombineTransition] using htransition.symm
        subst combined
        refine ⟨(Gamma, compactShiftRuleCheck
          (Gamma, premise, premiseValid)) :: tail,
          compactNumericShiftCombineAuxiliaryTokens premise, ?_, ?_⟩
        · simpa using hnext
        · exact CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_shift
            proofTokens certificateTokens Gamma
              firstFormula secondFormula witness suffix nextTasks
              premise premiseValid tail
  by_cases htag9 : tag = 9
  · subst tag
    cases source with
    | nil => simp [compactNumericCombineTransition] at htransition
    | cons right rest =>
        rcases right with ⟨rightConclusion, rightValid⟩
        cases rest with
        | nil => simp [compactNumericCombineTransition] at htransition
        | cons left tail =>
            rcases left with ⟨leftConclusion, leftValid⟩
            have hcombined : combined =
                ((Gamma, compactCutRuleCheck
                  (Gamma, firstFormula, (leftConclusion, leftValid),
                    rightConclusion, rightValid)), tail) := by
              simpa [compactNumericCombineTransition] using htransition.symm
            subst combined
            refine ⟨(Gamma, compactCutRuleCheck
              (Gamma, firstFormula, (leftConclusion, leftValid),
                rightConclusion, rightValid)) :: tail,
              compactNumericCutCombineAuxiliaryTokens firstFormula, ?_, ?_⟩
            · simpa using hnext
            · exact CompactNumericVerifierCanonicalNonLeafSuccessStateGraph.exists_of_cut
                proofTokens certificateTokens Gamma
                  firstFormula secondFormula witness suffix nextTasks
                  rightConclusion leftConclusion rightValid leftValid tail
  simp [compactNumericCombineTransition, htag3, htag4, htag5,
    htag6, htag7, htag8, htag9] at htransition

private theorem exists_nonLeafSuccessStateGraph_of_public_step_state
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (nextTasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (next : CompactNumericVerifierState)
    (htaskNe : task.1 ≠ 10)
    (hstep : next = compactNumericVerifierStep
      (((proofTokens, certificateTokens), (task :: nextTasks, source)), none))
    (hnextStatus : next.2 = none) :
    ∃ target backTokens,
      next = (((proofTokens, certificateTokens), (nextTasks, target)), none) ∧
      CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
        proofTokens certificateTokens task nextTasks source target backTokens := by
  have hcombineState : next = compactNumericCombineState task
      ((proofTokens, certificateTokens), (nextTasks, source)) := by
    simpa [compactNumericVerifierStep, compactNumericRunningStep, htaskNe]
      using hstep
  rcases (compactNumericCombineState_cases_iff task
      ((proofTokens, certificateTokens), (nextTasks, source)) next).2
      hcombineState with hsuccess | hfailure
  · exact exists_compactNumericVerifierNonLeafSuccessStateGraph_of_success
      proofTokens certificateTokens task nextTasks source next hsuccess
  · simp [hfailure.2] at hnextStatus

theorem exists_compactNumericVerifierNonLeafSuccessStateGraph_of_public_step
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (nextTasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10)
    (hstep :
      (((proofTokens, certificateTokens), (nextTasks, target)), none) =
        compactNumericVerifierStep
          (((proofTokens, certificateTokens),
            (task :: nextTasks, source)), none)) :
    ∃ backTokens,
      CompactNumericVerifierCanonicalNonLeafSuccessStateGraph
        proofTokens certificateTokens task nextTasks source target backTokens := by
  rcases exists_nonLeafSuccessStateGraph_of_public_step_state
      proofTokens certificateTokens task nextTasks source
      (((proofTokens, certificateTokens), (nextTasks, target)), none)
      htaskNe hstep rfl with
    ⟨realizedTarget, backTokens, hnext, hgraph⟩
  have htarget : realizedTarget = target := by
    simpa using (congrArg (fun state : CompactNumericVerifierState =>
      state.1.2.2) hnext).symm
  subst realizedTarget
  exact ⟨backTokens, hgraph⟩

private theorem nonLeafSuccess_of_frame_transition
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    (frame : CompactNumericVerifierCombineStateFrameRealization
      tokenTable width tokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates)
    {combined : CompactNumericChildResult × List CompactNumericChildResult}
    (hcombine : compactNumericCombineTransition frame.task frame.currentValues =
      some combined)
    (hvalues : frame.nextValues = combined.1 :: combined.2) :
    ∃ proofTokens certificateTokens currentTasks currentValues nextTasks
        nextValues task,
      currentTasks = task :: nextTasks ∧
      CompactNumericCombineSuccessCase task
        ((proofTokens, certificateTokens), (nextTasks, currentValues))
        (((proofTokens, certificateTokens), (nextTasks, nextValues)), none) := by
  refine ⟨frame.proofTokens, frame.certificateTokens,
    frame.currentTasks, frame.currentValues, frame.nextTasks, frame.nextValues,
    frame.task, frame.taskStack_eq, ?_⟩
  refine ⟨combined, hcombine, ?_⟩
  simp [hvalues]

theorem CompactNumericVerifierNonLeafSuccessStateGraph.sound_success
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {ruleWitness : CompactNumericVerifierCombineRuleWitness}
    (hgraph : CompactNumericVerifierNonLeafSuccessStateGraph
      tokenTable width tokenCount
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness ruleWitness) :
    ∃ proofTokens certificateTokens currentTasks currentValues nextTasks
        nextValues task,
      currentTasks = task :: nextTasks ∧
      CompactNumericCombineSuccessCase task
        ((proofTokens, certificateTokens), (nextTasks, currentValues))
        (((proofTokens, certificateTokens), (nextTasks, nextValues)), none) := by
  rcases hgraph with ⟨hcombineGraph, hnextStatusTag⟩
  rcases hcombineGraph with ⟨hcurrent, hnext, hhead, hframe, hbranch⟩
  rcases hframe.realize hcurrent hnext hhead with ⟨frame⟩
  rcases hbranch with hsimple | hallShift | hexsCut | hfailure
  · rcases hsimple with ⟨hrows, _hstatus⟩
    have hrows' : CompactNumericSimpleCombineTransitionRows
        tokenTable width tokenCount
        taskCoordinates.tag taskCoordinates.gammaFinish taskCoordinates.gammaCount
          taskCoordinates.gammaBoundary
        taskCoordinates.firstFinish taskCoordinates.firstCount
          taskCoordinates.secondFinish taskCoordinates.secondCount
        ruleWitness.rightGammaCount ruleWitness.rightGammaBoundary
          ruleWitness.rightBoolValue
        ruleWitness.leftGammaCount ruleWitness.leftGammaBoundary
          ruleWitness.leftBoolValue
        currentCoordinates.valueBoundary frame.currentValues.length
        nextCoordinates.valueBoundary frame.nextValues.length
        currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
        ruleWitness.resultBoolValue := by
      simpa only [frame.currentValues_length, frame.nextValues_length] using hrows
    rcases hrows'.sound_combineTransition
        hhead.core frame.taskLayout frame.currentValueRows frame.nextValueRows
        frame.currentValueGraph frame.nextValueGraph with
      ⟨combined, htransition, hvalues⟩
    exact nonLeafSuccess_of_frame_transition frame htransition hvalues
  · rcases hallShift with ⟨hrows, _hstatus⟩
    have hrows' : CompactNumericAllShiftCombineRuleRows
        tokenTable width tokenCount
        taskCoordinates.tag taskCoordinates.gammaFinish taskCoordinates.gammaCount
          taskCoordinates.gammaBoundary
        taskCoordinates.firstFinish taskCoordinates.firstCount
        ruleWitness.rightGammaCount ruleWitness.rightGammaBoundary
          ruleWitness.rightBoolValue
        currentCoordinates.valueBoundary frame.currentValues.length
        nextCoordinates.valueBoundary frame.nextValues.length
        ruleWitness.formulaBoundary ruleWitness.formulaBoundarySize
        ruleWitness.freedStart ruleWitness.freedFinish ruleWitness.freedBoundary
          ruleWitness.freedCount ruleWitness.freedBoundarySize
        ruleWitness.freeStateBoundary ruleWitness.freeStateCount
        ruleWitness.shiftCandidateBoundary ruleWitness.shiftSuccessTable
          ruleWitness.shiftedBoundary ruleWitness.shiftedCount
        ruleWitness.emptyStart ruleWitness.emptyFinish ruleWitness.emptyBoundary
          ruleWitness.emptyBoundarySize
        ruleWitness.shiftWitnessBound ruleWitness.freeTableWidth
          ruleWitness.freeValueBound
        currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
        ruleWitness.resultBoolValue := by
      simpa only [frame.currentValues_length, frame.nextValues_length] using hrows
    rcases hrows'.sound_combineTransition
        hhead.core frame.taskLayout frame.currentValueRows frame.nextValueRows
        frame.currentValueGraph frame.nextValueGraph with
      ⟨combined, htransition, hvalues⟩
    exact nonLeafSuccess_of_frame_transition frame htransition hvalues
  · rcases hexsCut with ⟨hrows, _hstatus⟩
    have hrows' : CompactNumericExsCutCombineRuleRows
        tokenTable width tokenCount
        taskCoordinates.tag taskCoordinates.gammaFinish taskCoordinates.gammaCount
          taskCoordinates.gammaBoundary
        taskCoordinates.firstFinish taskCoordinates.firstCount
          taskCoordinates.secondFinish taskCoordinates.witnessFinish
          taskCoordinates.witnessCount
        ruleWitness.rightGammaCount ruleWitness.rightGammaBoundary
          ruleWitness.rightBoolValue
        ruleWitness.leftGammaCount ruleWitness.leftGammaBoundary
          ruleWitness.leftBoolValue
        currentCoordinates.valueBoundary frame.currentValues.length
        nextCoordinates.valueBoundary frame.nextValues.length
        ruleWitness.formulaBoundary ruleWitness.formulaBoundarySize
        ruleWitness.transformedStart ruleWitness.transformedFinish
          ruleWitness.transformedBoundary ruleWitness.transformedCount
          ruleWitness.transformedBoundarySize
        ruleWitness.transformStateBoundary ruleWitness.transformStateCount
        ruleWitness.emptyStart ruleWitness.emptyFinish ruleWitness.emptyBoundary
          ruleWitness.emptyBoundarySize
        ruleWitness.freeTableWidth ruleWitness.freeValueBound
        currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
        ruleWitness.resultBoolValue := by
      simpa only [frame.currentValues_length, frame.nextValues_length] using hrows
    rcases hrows'.sound_combineTransition
        hhead.core frame.taskLayout frame.currentValueRows frame.nextValueRows
        frame.currentValueGraph frame.nextValueGraph with
      ⟨combined, htransition, hvalues⟩
    exact nonLeafSuccess_of_frame_transition frame htransition hvalues
  · have hfailureStatus : nextCoordinates.statusTag = 1 :=
      hfailure.2.2.1
    omega

#print axioms compactNumericVerifierNonLeafSuccessStateGraphDef_spec
#print axioms compactNumericVerifierNonLeafSuccessStateGraphDef_sigmaZero
#print axioms CompactNumericVerifierNonLeafSuccessStateGraph.sound_success
#print axioms
  exists_compactNumericVerifierNonLeafSuccessStateGraph_of_success
#print axioms
  exists_compactNumericVerifierNonLeafSuccessStateGraph_of_public_step

end FoundationCompactNumericListedDirectVerifierNonLeafSuccessStateGraph
