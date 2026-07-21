import integration.FoundationCompactNumericListedDirectVerifierCombineCanonicalFrameCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds
import integration.FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraph
import integration.FoundationCompactNumericListedDirectVerifierCombineSimpleStateGraphCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineFailureStateGraphCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineExsCutStateGraphCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineAllShiftStateGraphCompleteness
import integration.FoundationCompactNumericListedDirectFormulaTransformTraceListLayout

/-!
# Canonical concrete graph for a verifier combine step

The token table is definitionally the additive encoding of the concrete current
state, the concrete next state, and any rule-specific auxiliary suffix.  The
predicate is used only as a constructive conclusion; it introduces no premise.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTraceListLayout
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierCombineCanonicalFrameCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineSimpleStateGraphCompleteness
open FoundationCompactNumericListedDirectVerifierCombineFailureStateGraphCompleteness
open FoundationCompactNumericListedDirectVerifierCombineExsCutStateGraphCompleteness
open FoundationCompactNumericListedDirectVerifierCombineAllShiftStateGraphCompleteness

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

def CompactNumericVerifierCanonicalCombineGraph
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat) : Prop :=
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  ∃ currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      ruleWitness,
    currentCoordinates.start = 0 ∧
    currentCoordinates.finish = currentTokens.length ∧
    nextCoordinates.start = currentTokens.length ∧
    nextCoordinates.finish = currentTokens.length + nextTokens.length ∧
    CompactNumericVerifierStateCanonicalCorePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      0 currentTokens.length currentState
      currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCanonicalCorePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentTokens.length (currentTokens.length + nextTokens.length)
      nextState nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierCombineStateGraph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness ruleWitness

/-- Quantitative companion to the canonical combine graph.  It retains the
same concrete witness that proves the graph and records a pointwise binary-size
bound for all thirty-four rule coordinates, including canonical zero padding. -/
def CompactNumericVerifierCanonicalCombineBoundedGraph
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat) (ruleCoordinateBound : Nat) : Prop :=
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  ∃ currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      ruleWitness,
    currentCoordinates.start = 0 ∧
    currentCoordinates.finish = currentTokens.length ∧
    nextCoordinates.start = currentTokens.length ∧
    nextCoordinates.finish = currentTokens.length + nextTokens.length ∧
    CompactNumericVerifierStateCanonicalCorePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      0 currentTokens.length currentState
      currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCanonicalCorePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentTokens.length (currentTokens.length + nextTokens.length)
      nextState nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierCombineStateGraph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness ruleWitness ∧
    ∀ coordinate : Fin 34,
      Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
        ruleWitness coordinate) <= ruleCoordinateBound

def compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat) : Nat :=
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  compactNumericAllShiftCombineRuleCoordinateSizeBound width tokens.length

def compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat) : Nat :=
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens ++ backTokens
  compactNumericVerifierSimpleCombineRuleCoordinateSizeBound tokens.length

def compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat) : Nat :=
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  compactNumericExsCutCombineRuleCoordinateSizeBound width tokens.length

theorem CompactNumericVerifierCanonicalCombineBoundedGraph.toGraph
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List CompactNumericChildResult}
    {nextStatus : Option Bool}
    {backTokens : List Nat} {ruleCoordinateBound : Nat}
    (hgraph : CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens task tasks source target
        nextStatus backTokens ruleCoordinateBound) :
    CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens task tasks source target
        nextStatus backTokens := by
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph] at hgraph
  dsimp only [CompactNumericVerifierCanonicalCombineGraph]
  rcases hgraph with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, ruleWitness,
      hcurrentStart, hcurrentFinish, hnextStart, hnextFinish,
      hcurrentPackage, hnextPackage, hcombine, _hcoordinateSize⟩
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness, ruleWitness,
    hcurrentStart, hcurrentFinish, hnextStart, hnextFinish,
    hcurrentPackage, hnextPackage, hcombine⟩

def compactNumericExsCombineAuxiliaryTokens
    (formula witness : List Nat) : List Nat :=
  let transformed :=
    (compactFormulaSubstitutionExact 1 (witness, formula)).getD []
  let trace := compactFormulaTransformStateTrace (2, witness)
    (compactSyntaxRunFuelBound formula)
    (compactFormulaTransformInitialState 1 formula)
  compactAdditiveEncode transformed ++
    compactAdditiveEncode ([] : List Nat) ++ compactAdditiveEncode trace

def compactNumericCutCombineAuxiliaryTokens
    (formula : List Nat) : List Nat :=
  let transformed := (compactFormulaNegationExact 0 formula).getD []
  let trace := compactFormulaTransformStateTrace (3, [])
    (compactSyntaxRunFuelBound formula)
    (compactFormulaTransformInitialState 0 formula)
  compactAdditiveEncode transformed ++
    compactAdditiveEncode ([] : List Nat) ++ compactAdditiveEncode trace

def compactFormulaShiftTraceList
    (formulas : List (List Nat)) : List (List CompactFormulaTransformState) :=
  formulas.map fun formula =>
    compactFormulaTransformStateTrace (1, [])
      (compactSyntaxRunFuelBound formula)
      (compactFormulaTransformInitialState 0 formula)

theorem compactFormulaShiftTraceList_getI
    (formulas : List (List Nat)) (index : Nat)
    (hindex : index < formulas.length) :
    (compactFormulaShiftTraceList formulas).getI index =
      compactFormulaTransformStateTrace (1, [])
        (compactSyntaxRunFuelBound (formulas.getI index))
        (compactFormulaTransformInitialState 0 (formulas.getI index)) := by
  rw [List.getI_eq_getElem _
    (by simpa [compactFormulaShiftTraceList] using hindex)]
  rw [List.getI_eq_getElem formulas hindex]
  simp [compactFormulaShiftTraceList]

def compactNumericShiftCombineAuxiliaryTokens
    (premise : List (List Nat)) : List Nat :=
  let empty : List Nat := []
  let candidates := premise.map fun formula =>
    (compactFormulaShiftExact 0 formula).getD []
  let shifted := (compactFormulaShiftExactList premise).getD []
  let traces := compactFormulaShiftTraceList premise
  compactAdditiveEncode empty ++ compactAdditiveEncode candidates ++
    compactAdditiveEncode shifted ++ compactAdditiveEncode traces

def compactNumericAllCombineAuxiliaryTokens
    (Gamma : List (List Nat)) (formula : List Nat) : List Nat :=
  let freed := (compactFormulaFreeExact formula).getD []
  let empty : List Nat := []
  let freeTrace := compactFormulaTransformStateTrace (0, [])
    (compactSyntaxRunFuelBound formula)
    (compactFormulaTransformInitialState 1 formula)
  let candidates := Gamma.map fun candidateFormula =>
    (compactFormulaShiftExact 0 candidateFormula).getD []
  let shifted := (compactFormulaShiftExactList Gamma).getD []
  let shiftTraces := compactFormulaShiftTraceList Gamma
  compactAdditiveEncode freed ++ compactAdditiveEncode empty ++
    compactAdditiveEncode freeTrace ++ compactAdditiveEncode candidates ++
    compactAdditiveEncode shifted ++ compactAdditiveEncode shiftTraces

theorem CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_and
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion leftConclusion : List (List Nat))
    (rightValid leftValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens
      (3, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks
      ((rightConclusion, rightValid) :: (leftConclusion, leftValid) :: tail)
      ((Gamma, compactAndRuleCheck
        (Gamma, firstFormula, secondFormula,
          (leftConclusion, leftValid), rightConclusion, rightValid)) :: tail)
      none []
      (compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound
        proofTokens certificateTokens
        (3, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
        tasks
        ((rightConclusion, rightValid) :: (leftConclusion, leftValid) :: tail)
        ((Gamma, compactAndRuleCheck
          (Gamma, firstFormula, secondFormula,
            (leftConclusion, leftValid), rightConclusion, rightValid)) :: tail)
        none []) := by
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph,
    compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound]
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
  rcases CompactNumericVerifierCombineStateGraph.exists_of_and_frame
      hframe with ⟨ruleWitness, hgraph, hruleSize⟩
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness, ruleWitness,
    hframe.1.1, hframe.1.2.1, hframe.2.1.1, hframe.2.1.2.1,
    hframe.1, hframe.2.1,
    hgraph, hruleSize⟩

theorem CompactNumericVerifierCanonicalCombineGraph.exists_of_and
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion leftConclusion : List (List Nat))
    (rightValid leftValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens
      (3, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks
      ((rightConclusion, rightValid) :: (leftConclusion, leftValid) :: tail)
      ((Gamma, compactAndRuleCheck
        (Gamma, firstFormula, secondFormula,
          (leftConclusion, leftValid), rightConclusion, rightValid)) :: tail)
      none [] := by
  exact (CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_and
    proofTokens certificateTokens Gamma firstFormula secondFormula witness
      suffix tasks rightConclusion leftConclusion rightValid leftValid tail).toGraph

theorem CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_or
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion : List (List Nat)) (rightValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens
      (4, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactOrRuleCheck
        (Gamma, firstFormula, secondFormula,
          rightConclusion, rightValid)) :: tail)
      none []
      (compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound
        proofTokens certificateTokens
        (4, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
        tasks ((rightConclusion, rightValid) :: tail)
        ((Gamma, compactOrRuleCheck
          (Gamma, firstFormula, secondFormula,
            rightConclusion, rightValid)) :: tail)
        none []) := by
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph,
    compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound]
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
  rcases CompactNumericVerifierCombineStateGraph.exists_of_or_frame
      hframe with ⟨ruleWitness, hgraph, hruleSize⟩
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness, ruleWitness,
    hframe.1.1, hframe.1.2.1, hframe.2.1.1, hframe.2.1.2.1,
    hframe.1, hframe.2.1,
    hgraph, hruleSize⟩

theorem CompactNumericVerifierCanonicalCombineGraph.exists_of_or
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion : List (List Nat)) (rightValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens
      (4, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactOrRuleCheck
        (Gamma, firstFormula, secondFormula,
          rightConclusion, rightValid)) :: tail)
      none [] := by
  exact (CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_or
    proofTokens certificateTokens Gamma firstFormula secondFormula witness
      suffix tasks rightConclusion rightValid tail).toGraph

theorem CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_wk
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion : List (List Nat)) (rightValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens
      (7, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactWkRuleCheck
        (Gamma, rightConclusion, rightValid)) :: tail)
      none []
      (compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound
        proofTokens certificateTokens
        (7, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
        tasks ((rightConclusion, rightValid) :: tail)
        ((Gamma, compactWkRuleCheck
          (Gamma, rightConclusion, rightValid)) :: tail)
        none []) := by
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph,
    compactNumericVerifierCanonicalSimpleRuleCoordinateSizeBound]
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
  rcases CompactNumericVerifierCombineStateGraph.exists_of_wk_frame
      hframe with ⟨ruleWitness, hgraph, hruleSize⟩
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness, ruleWitness,
    hframe.1.1, hframe.1.2.1, hframe.2.1.1, hframe.2.1.2.1,
    hframe.1, hframe.2.1,
    hgraph, hruleSize⟩

theorem CompactNumericVerifierCanonicalCombineGraph.exists_of_wk
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion : List (List Nat)) (rightValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens
      (7, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactWkRuleCheck
        (Gamma, rightConclusion, rightValid)) :: tail)
      none [] := by
  exact (CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_wk
    proofTokens certificateTokens Gamma firstFormula secondFormula witness
      suffix tasks rightConclusion rightValid tail).toGraph

theorem CompactNumericVerifierCanonicalCombineGraph.exists_of_failure
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10)
    (htransition : compactNumericCombineTransition task source = none) :
    CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens task tasks source source (some false) [] := by
  dsimp only [CompactNumericVerifierCanonicalCombineGraph]
  have hframeExists :=
    CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back
      proofTokens certificateTokens task tasks source source
      (some false) [] htaskNe
  dsimp only at hframeExists
  rcases hframeExists with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframe⟩
  have hgraph := CompactNumericVerifierCombineStateGraph.of_failure_frame
    hframe htransition
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness,
    compactNumericVerifierFailureCombineRuleWitness,
    hframe.1.1, hframe.1.2.1, hframe.2.1.1, hframe.2.1.2.1,
    hframe.1, hframe.2.1,
    hgraph⟩

theorem CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_failure
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10)
    (htransition : compactNumericCombineTransition task source = none) :
    CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens task tasks source source
      (some false) [] 0 := by
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph]
  have hframeExists :=
    CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back
      proofTokens certificateTokens task tasks source source
      (some false) [] htaskNe
  dsimp only at hframeExists
  rcases hframeExists with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframe⟩
  have hgraph := CompactNumericVerifierCombineStateGraph.of_failure_frame
    hframe htransition
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness,
    compactNumericVerifierFailureCombineRuleWitness,
    hframe.1.1, hframe.1.2.1, hframe.2.1.1, hframe.2.1.2.1,
    hframe.1, hframe.2.1, hgraph,
    compactNumericVerifierFailureCombineRuleWitness_size_le 0⟩

theorem CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_exs
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (formula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion : List (List Nat)) (rightValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens
      (6, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactExsRuleCheck
        (Gamma, formula, witness, rightConclusion, rightValid)) :: tail)
      none (compactNumericExsCombineAuxiliaryTokens formula witness)
      (compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound
        proofTokens certificateTokens
        (6, (Gamma, (formula, (secondFormula, (witness, suffix)))))
        tasks ((rightConclusion, rightValid) :: tail)
        ((Gamma, compactExsRuleCheck
          (Gamma, formula, witness, rightConclusion, rightValid)) :: tail)
        none (compactNumericExsCombineAuxiliaryTokens formula witness)) := by
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
  change CompactNumericVerifierCanonicalCombineBoundedGraph
    proofTokens certificateTokens task tasks source target none backTokens
      (compactNumericExsCutCombineRuleCoordinateSizeBound width tokens.length)
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
  rcases CompactNumericVerifierCombineStateGraph.exists_of_exs_frame
      (transformedStart := transformedStart)
      (transformedFinish := transformedFinish)
      (transformStateBoundary := transformStateBoundary)
      (emptyStart := emptyStart) (emptyFinish := emptyFinish)
      hframe htransformed hempty ⟨htrace.2.1, htrace.2.2⟩ with
    ⟨ruleWitness, hgraph, hruleBounds⟩
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph,
    compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound]
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness, ruleWitness,
    hframe.1.1, hframe.1.2.1, hframe.2.1.1, hframe.2.1.2.1,
    hframe.1, hframe.2.1,
    hgraph, hruleBounds.coordinate_size⟩

theorem CompactNumericVerifierCanonicalCombineGraph.exists_of_exs
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (formula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion : List (List Nat)) (rightValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens
      (6, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactExsRuleCheck
        (Gamma, formula, witness, rightConclusion, rightValid)) :: tail)
      none (compactNumericExsCombineAuxiliaryTokens formula witness) := by
  exact (CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_exs
    proofTokens certificateTokens Gamma formula secondFormula witness suffix
      tasks rightConclusion rightValid tail).toGraph

theorem CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_cut
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (formula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion leftConclusion : List (List Nat))
    (rightValid leftValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens
      (9, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks
      ((rightConclusion, rightValid) :: (leftConclusion, leftValid) :: tail)
      ((Gamma, compactCutRuleCheck
        (Gamma, formula, (leftConclusion, leftValid),
          rightConclusion, rightValid)) :: tail)
      none (compactNumericCutCombineAuxiliaryTokens formula)
      (compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound
        proofTokens certificateTokens
        (9, (Gamma, (formula, (secondFormula, (witness, suffix)))))
        tasks
        ((rightConclusion, rightValid) ::
          (leftConclusion, leftValid) :: tail)
        ((Gamma, compactCutRuleCheck
          (Gamma, formula, (leftConclusion, leftValid),
            rightConclusion, rightValid)) :: tail)
        none (compactNumericCutCombineAuxiliaryTokens formula)) := by
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
  change CompactNumericVerifierCanonicalCombineBoundedGraph
    proofTokens certificateTokens task tasks source target none backTokens
      (compactNumericExsCutCombineRuleCoordinateSizeBound width tokens.length)
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
  rcases CompactNumericVerifierCombineStateGraph.exists_of_cut_frame
      (transformedStart := transformedStart)
      (transformedFinish := transformedFinish)
      (transformStateBoundary := transformStateBoundary)
      (emptyStart := emptyStart) (emptyFinish := emptyFinish)
      hframe htransformed hempty ⟨htrace.2.1, htrace.2.2⟩ with
    ⟨ruleWitness, hgraph, hruleBounds⟩
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph,
    compactNumericVerifierCanonicalExsCutRuleCoordinateSizeBound]
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness, ruleWitness,
    hframe.1.1, hframe.1.2.1, hframe.2.1.1, hframe.2.1.2.1,
    hframe.1, hframe.2.1,
    hgraph, hruleBounds.coordinate_size⟩

theorem CompactNumericVerifierCanonicalCombineGraph.exists_of_cut
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (formula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (rightConclusion leftConclusion : List (List Nat))
    (rightValid leftValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens
      (9, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks
      ((rightConclusion, rightValid) :: (leftConclusion, leftValid) :: tail)
      ((Gamma, compactCutRuleCheck
        (Gamma, formula, (leftConclusion, leftValid),
          rightConclusion, rightValid)) :: tail)
      none (compactNumericCutCombineAuxiliaryTokens formula) := by
  exact (CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_cut
    proofTokens certificateTokens Gamma formula secondFormula witness suffix
      tasks rightConclusion leftConclusion rightValid leftValid tail).toGraph

theorem CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_shift
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (premise : List (List Nat)) (premiseValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens
      (8, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((premise, premiseValid) :: tail)
      ((Gamma, compactShiftRuleCheck (Gamma, premise, premiseValid)) :: tail)
      none (compactNumericShiftCombineAuxiliaryTokens premise)
      (compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound
        proofTokens certificateTokens
        (8, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
        tasks ((premise, premiseValid) :: tail)
        ((Gamma, compactShiftRuleCheck (Gamma, premise, premiseValid)) :: tail)
        none (compactNumericShiftCombineAuxiliaryTokens premise)) := by
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
  change CompactNumericVerifierCanonicalCombineBoundedGraph
    proofTokens certificateTokens task tasks source target none backTokens
      (compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound
        proofTokens certificateTokens task tasks source target none backTokens)
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
  rcases CompactNumericVerifierCombineStateGraph.exists_of_shift_frame
      (shiftCandidateBoundary := candidateBoundary)
      (shiftedBoundary := shiftedBoundary)
      (emptyStart := emptyStart) (emptyFinish := emptyFinish)
      hframe hempty
        ⟨hcandidateStructure, hcandidateRows, hcandidateSize⟩
        ⟨hshiftedStructure, hshiftedRows, hshiftedSize⟩
        hshiftTraces htokenCount with
    ⟨ruleWitness, hgraph, hbounds⟩
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph,
    compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound]
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness, ruleWitness,
    hframe.1.1, hframe.1.2.1, hframe.2.1.1, hframe.2.1.2.1,
    hframe.1, hframe.2.1,
    hgraph, hbounds.coordinate_size⟩

theorem CompactNumericVerifierCanonicalCombineGraph.exists_of_shift
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (firstFormula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (premise : List (List Nat)) (premiseValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens
      (8, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((premise, premiseValid) :: tail)
      ((Gamma, compactShiftRuleCheck (Gamma, premise, premiseValid)) :: tail)
      none (compactNumericShiftCombineAuxiliaryTokens premise) := by
  exact (CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_shift
    proofTokens certificateTokens Gamma firstFormula secondFormula
      witness suffix tasks premise premiseValid tail).toGraph

theorem CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_all
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (formula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (premise : List (List Nat)) (premiseValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens
      (5, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks ((premise, premiseValid) :: tail)
      ((Gamma, compactAllRuleCheck
        (Gamma, formula, premise, premiseValid)) :: tail)
      none (compactNumericAllCombineAuxiliaryTokens Gamma formula)
      (compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound
        proofTokens certificateTokens
        (5, (Gamma, (formula, (secondFormula, (witness, suffix)))))
        tasks ((premise, premiseValid) :: tail)
        ((Gamma, compactAllRuleCheck
          (Gamma, formula, premise, premiseValid)) :: tail)
        none (compactNumericAllCombineAuxiliaryTokens Gamma formula)) := by
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
  change CompactNumericVerifierCanonicalCombineBoundedGraph
    proofTokens certificateTokens task tasks source target none backTokens
      (compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound
        proofTokens certificateTokens task tasks source target none backTokens)
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
      afterEmpty freeTrace
        (candidateTokens ++ shiftedTokens ++ shiftTraceTokens)
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
    ⟨ruleWitness, hgraph, hbounds⟩
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph,
    compactNumericVerifierCanonicalAllShiftRuleCoordinateSizeBound]
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness, ruleWitness,
    hframe.1.1, hframe.1.2.1, hframe.2.1.1, hframe.2.1.2.1,
    hframe.1, hframe.2.1,
    hgraph, hbounds.coordinate_size⟩

theorem CompactNumericVerifierCanonicalCombineGraph.exists_of_all
    (proofTokens certificateTokens : List Nat)
    (Gamma : List (List Nat))
    (formula secondFormula witness suffix : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (premise : List (List Nat)) (premiseValid : Bool)
    (tail : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens
      (5, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks ((premise, premiseValid) :: tail)
      ((Gamma, compactAllRuleCheck
        (Gamma, formula, premise, premiseValid)) :: tail)
      none (compactNumericAllCombineAuxiliaryTokens Gamma formula) := by
  exact (CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_all
    proofTokens certificateTokens Gamma formula secondFormula witness suffix
      tasks premise premiseValid tail).toGraph

#print axioms CompactNumericVerifierCanonicalCombineGraph.exists_of_and
#print axioms CompactNumericVerifierCanonicalCombineGraph.exists_of_or
#print axioms CompactNumericVerifierCanonicalCombineGraph.exists_of_wk
#print axioms
  CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_and
#print axioms
  CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_or
#print axioms
  CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_wk
#print axioms CompactNumericVerifierCanonicalCombineGraph.exists_of_failure
#print axioms
  CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_failure
#print axioms
  CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_exs
#print axioms
  CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_cut
#print axioms
  CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_shift
#print axioms
  CompactNumericVerifierCanonicalCombineBoundedGraph.exists_of_all
#print axioms CompactNumericVerifierCanonicalCombineGraph.exists_of_exs
#print axioms CompactNumericVerifierCanonicalCombineGraph.exists_of_cut
#print axioms CompactNumericVerifierCanonicalCombineGraph.exists_of_shift
#print axioms CompactNumericVerifierCanonicalCombineGraph.exists_of_all

end FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph
