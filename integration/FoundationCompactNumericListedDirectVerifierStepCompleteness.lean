import integration.FoundationCompactNumericListedDirectVerifierStepExactness
import integration.FoundationCompactNumericListedDirectVerifierParseStateCompleteness
import integration.FoundationCompactNumericListedDirectVerifierHaltedCompleteness
import integration.FoundationCompactNumericListedDirectVerifierFinishCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness

/-!
# Constructive completeness of the complete verifier-step formula

The four executable branches are installed in one 429-column environment.
The witness records the fixed state-table columns and the exact current/next
slice endpoints, so formula existence remains tied to the concrete public step.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierParseStateCompleteness
open FoundationCompactNumericListedDirectVerifierHaltedCompleteness
open FoundationCompactNumericListedDirectVerifierFinishCompleteness
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph
open FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec

structure CompactNumericVerifierStepArguments where
  taskCoordinates : CompactNumericVerifierTaskRowCoordinates
  taskSizeWitness : CompactNumericVerifierTaskSizeWitness
  proofTable : Nat
  proofWidth : Nat
  proofTokenCount : Nat
  proofInputStart : Nat
  proofInputFinish : Nat
  rootStart : Nat
  rootFinish : Nat
  proofTag : Nat
  proofEndpointBound : Nat
  certificateTable : Nat
  certificateWidth : Nat
  certificateTokenCount : Nat
  certificateInputStart : Nat
  certificateInputFinish : Nat
  axiomStart : Nat
  axiomFinish : Nat
  formulaStart : Nat
  formulaFinish : Nat
  suffixStart : Nat
  suffixFinish : Nat
  certificateTag : Nat
  certificateEndpointBound : Nat
  rootGammaFinish : Nat
  rootGammaCount : Nat
  rootGammaBoundary : Nat
  firstFinish : Nat
  firstCount : Nat
  secondFinish : Nat
  secondCount : Nat
  witnessFinish : Nat
  witnessCount : Nat
  suffixCount : Nat
  rootGammaBoundarySize : Nat
  targetStart : Nat
  targetFinish : Nat
  targetGammaFinish : Nat
  targetGammaCount : Nat
  targetGammaBoundary : Nat
  targetBool : Nat
  targetGammaBoundarySize : Nat
  resultBool : Nat
  ruleTable : Nat
  ruleWidth : Nat
  ruleTokenCount : Nat
  ruleProofTag : Nat
  ruleCertificateTag : Nat
  ruleGammaStart : Nat
  ruleGammaFinish : Nat
  ruleGammaBoundary : Nat
  ruleGammaCount : Nat
  ruleGammaBoundarySize : Nat
  ruleFormulaStart : Nat
  ruleFormulaFinish : Nat
  ruleFormulaBoundary : Nat
  ruleFormulaCount : Nat
  ruleFormulaBoundarySize : Nat
  ruleNegatedStart : Nat
  ruleNegatedFinish : Nat
  ruleNegatedBoundary : Nat
  ruleNegatedCount : Nat
  ruleNegatedBoundarySize : Nat
  ruleStateBoundary : Nat
  ruleStateCount : Nat
  ruleEmptyStart : Nat
  ruleEmptyFinish : Nat
  ruleEmptyBoundary : Nat
  ruleEmptyBoundarySize : Nat
  ruleTableWidth : Nat
  ruleValueBound : Nat
  paCoordinates : CompactNumericVerifierPAAxiomJointLeafCoordinates
  firstParseCoordinates : CompactNumericVerifierTaskRowCoordinates
  secondParseCoordinates : CompactNumericVerifierTaskRowCoordinates
  combineCoordinates : CompactNumericVerifierTaskRowCoordinates
  firstParseSize : CompactNumericVerifierTaskSizeWitness
  secondParseSize : CompactNumericVerifierTaskSizeWitness
  combineSize : CompactNumericVerifierTaskSizeWitness

def compactNumericVerifierStepUnusedArguments :
    CompactNumericVerifierStepArguments := by
  repeat constructor

def CompactNumericVerifierStepArguments.ofParseWitness
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    (w : CompactNumericVerifierParseStateGraphWitness
      stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish) :
    CompactNumericVerifierStepArguments where
  taskCoordinates := w.taskCoordinates
  taskSizeWitness := w.taskSizeWitness
  proofTable := w.proofTable
  proofWidth := w.proofWidth
  proofTokenCount := w.proofTokenCount
  proofInputStart := w.proofInputStart
  proofInputFinish := w.proofInputFinish
  rootStart := w.rootStart
  rootFinish := w.rootFinish
  proofTag := w.proofTag
  proofEndpointBound := w.proofEndpointBound
  certificateTable := w.certificateTable
  certificateWidth := w.certificateWidth
  certificateTokenCount := w.certificateTokenCount
  certificateInputStart := w.certificateInputStart
  certificateInputFinish := w.certificateInputFinish
  axiomStart := w.axiomStart
  axiomFinish := w.axiomFinish
  formulaStart := w.formulaStart
  formulaFinish := w.formulaFinish
  suffixStart := w.suffixStart
  suffixFinish := w.suffixFinish
  certificateTag := w.certificateTag
  certificateEndpointBound := w.certificateEndpointBound
  rootGammaFinish := w.rootGammaFinish
  rootGammaCount := w.rootGammaCount
  rootGammaBoundary := w.rootGammaBoundary
  firstFinish := w.firstFinish
  firstCount := w.firstCount
  secondFinish := w.secondFinish
  secondCount := w.secondCount
  witnessFinish := w.witnessFinish
  witnessCount := w.witnessCount
  suffixCount := w.suffixCount
  rootGammaBoundarySize := w.rootGammaBoundarySize
  targetStart := w.targetStart
  targetFinish := w.targetFinish
  targetGammaFinish := w.targetGammaFinish
  targetGammaCount := w.targetGammaCount
  targetGammaBoundary := w.targetGammaBoundary
  targetBool := w.targetBool
  targetGammaBoundarySize := w.targetGammaBoundarySize
  resultBool := w.resultBool
  ruleTable := w.ruleTable
  ruleWidth := w.ruleWidth
  ruleTokenCount := w.ruleTokenCount
  ruleProofTag := w.ruleProofTag
  ruleCertificateTag := w.ruleCertificateTag
  ruleGammaStart := w.ruleGammaStart
  ruleGammaFinish := w.ruleGammaFinish
  ruleGammaBoundary := w.ruleGammaBoundary
  ruleGammaCount := w.ruleGammaCount
  ruleGammaBoundarySize := w.ruleGammaBoundarySize
  ruleFormulaStart := w.ruleFormulaStart
  ruleFormulaFinish := w.ruleFormulaFinish
  ruleFormulaBoundary := w.ruleFormulaBoundary
  ruleFormulaCount := w.ruleFormulaCount
  ruleFormulaBoundarySize := w.ruleFormulaBoundarySize
  ruleNegatedStart := w.ruleNegatedStart
  ruleNegatedFinish := w.ruleNegatedFinish
  ruleNegatedBoundary := w.ruleNegatedBoundary
  ruleNegatedCount := w.ruleNegatedCount
  ruleNegatedBoundarySize := w.ruleNegatedBoundarySize
  ruleStateBoundary := w.ruleStateBoundary
  ruleStateCount := w.ruleStateCount
  ruleEmptyStart := w.ruleEmptyStart
  ruleEmptyFinish := w.ruleEmptyFinish
  ruleEmptyBoundary := w.ruleEmptyBoundary
  ruleEmptyBoundarySize := w.ruleEmptyBoundarySize
  ruleTableWidth := w.ruleTableWidth
  ruleValueBound := w.ruleValueBound
  paCoordinates := w.paCoordinates
  firstParseCoordinates := w.firstParseCoordinates
  secondParseCoordinates := w.secondParseCoordinates
  combineCoordinates := w.combineCoordinates
  firstParseSize := w.firstParseSize
  secondParseSize := w.secondParseSize
  combineSize := w.combineSize

def CompactNumericVerifierStepArguments.ofCombine
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness : CompactNumericVerifierTaskSizeWitness)
    (ruleWitness : CompactNumericVerifierCombineRuleWitness) :
    CompactNumericVerifierStepArguments :=
  { compactNumericVerifierStepUnusedArguments with
    taskCoordinates := taskCoordinates
    taskSizeWitness := taskSizeWitness
    proofTable := ruleWitness.rightGammaCount
    proofWidth := ruleWitness.rightGammaBoundary
    proofTokenCount := ruleWitness.rightBoolValue
    proofInputStart := ruleWitness.leftGammaCount
    proofInputFinish := ruleWitness.leftGammaBoundary
    rootStart := ruleWitness.leftBoolValue
    rootFinish := ruleWitness.formulaBoundary
    proofTag := ruleWitness.formulaBoundarySize
    proofEndpointBound := ruleWitness.transformedStart
    certificateTable := ruleWitness.transformedFinish
    certificateWidth := ruleWitness.transformedBoundary
    certificateTokenCount := ruleWitness.transformedCount
    certificateInputStart := ruleWitness.transformedBoundarySize
    certificateInputFinish := ruleWitness.transformStateBoundary
    axiomStart := ruleWitness.transformStateCount
    axiomFinish := ruleWitness.freedStart
    formulaStart := ruleWitness.freedFinish
    formulaFinish := ruleWitness.freedBoundary
    suffixStart := ruleWitness.freedCount
    suffixFinish := ruleWitness.freedBoundarySize
    certificateTag := ruleWitness.freeStateBoundary
    certificateEndpointBound := ruleWitness.freeStateCount
    rootGammaFinish := ruleWitness.shiftCandidateBoundary
    rootGammaCount := ruleWitness.shiftSuccessTable
    rootGammaBoundary := ruleWitness.shiftedBoundary
    firstFinish := ruleWitness.shiftedCount
    firstCount := ruleWitness.emptyStart
    secondFinish := ruleWitness.emptyFinish
    secondCount := ruleWitness.emptyBoundary
    witnessFinish := ruleWitness.emptyBoundarySize
    witnessCount := ruleWitness.shiftWitnessBound
    suffixCount := ruleWitness.freeTableWidth
    rootGammaBoundarySize := ruleWitness.freeValueBound
    targetStart := ruleWitness.resultBoolValue }

def CompactNumericVerifierStepArguments.Graph
    (arguments : CompactNumericVerifierStepArguments)
    (stateTable stateWidth stateTokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness) : Prop :=
  CompactNumericVerifierStepGraph
    stateTable stateWidth stateTokenCount
    currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
    arguments.taskCoordinates arguments.taskSizeWitness
    arguments.proofTable arguments.proofWidth arguments.proofTokenCount
    arguments.proofInputStart arguments.proofInputFinish
    arguments.rootStart arguments.rootFinish arguments.proofTag
    arguments.proofEndpointBound
    arguments.certificateTable arguments.certificateWidth
    arguments.certificateTokenCount arguments.certificateInputStart
    arguments.certificateInputFinish
    arguments.axiomStart arguments.axiomFinish
    arguments.formulaStart arguments.formulaFinish
    arguments.suffixStart arguments.suffixFinish arguments.certificateTag
    arguments.certificateEndpointBound
    arguments.rootGammaFinish arguments.rootGammaCount
    arguments.rootGammaBoundary arguments.firstFinish arguments.firstCount
    arguments.secondFinish arguments.secondCount arguments.witnessFinish
    arguments.witnessCount arguments.suffixCount
    arguments.rootGammaBoundarySize
    arguments.targetStart arguments.targetFinish
    arguments.targetGammaFinish arguments.targetGammaCount
    arguments.targetGammaBoundary arguments.targetBool
    arguments.targetGammaBoundarySize arguments.resultBool
    arguments.ruleTable arguments.ruleWidth arguments.ruleTokenCount
    arguments.ruleProofTag arguments.ruleCertificateTag
    arguments.ruleGammaStart arguments.ruleGammaFinish
    arguments.ruleGammaBoundary arguments.ruleGammaCount
    arguments.ruleGammaBoundarySize
    arguments.ruleFormulaStart arguments.ruleFormulaFinish
    arguments.ruleFormulaBoundary arguments.ruleFormulaCount
    arguments.ruleFormulaBoundarySize
    arguments.ruleNegatedStart arguments.ruleNegatedFinish
    arguments.ruleNegatedBoundary arguments.ruleNegatedCount
    arguments.ruleNegatedBoundarySize arguments.ruleStateBoundary
    arguments.ruleStateCount arguments.ruleEmptyStart
    arguments.ruleEmptyFinish arguments.ruleEmptyBoundary
    arguments.ruleEmptyBoundarySize arguments.ruleTableWidth
    arguments.ruleValueBound arguments.paCoordinates
    arguments.firstParseCoordinates arguments.secondParseCoordinates
    arguments.combineCoordinates arguments.firstParseSize
    arguments.secondParseSize arguments.combineSize

def CompactNumericVerifierStepArguments.environment
    (arguments : CompactNumericVerifierStepArguments)
    (stateTable stateWidth stateTokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness) : Fin 429 → Nat :=
  compactNumericVerifierParseStateGraphEnvironment
    stateTable stateWidth stateTokenCount
    currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
    arguments.taskCoordinates arguments.taskSizeWitness
    arguments.proofTable arguments.proofWidth arguments.proofTokenCount
    arguments.proofInputStart arguments.proofInputFinish
    arguments.rootStart arguments.rootFinish arguments.proofTag
    arguments.proofEndpointBound
    arguments.certificateTable arguments.certificateWidth
    arguments.certificateTokenCount arguments.certificateInputStart
    arguments.certificateInputFinish
    arguments.axiomStart arguments.axiomFinish
    arguments.formulaStart arguments.formulaFinish
    arguments.suffixStart arguments.suffixFinish arguments.certificateTag
    arguments.certificateEndpointBound
    arguments.rootGammaFinish arguments.rootGammaCount
    arguments.rootGammaBoundary arguments.firstFinish arguments.firstCount
    arguments.secondFinish arguments.secondCount arguments.witnessFinish
    arguments.witnessCount arguments.suffixCount
    arguments.rootGammaBoundarySize
    arguments.targetStart arguments.targetFinish
    arguments.targetGammaFinish arguments.targetGammaCount
    arguments.targetGammaBoundary arguments.targetBool
    arguments.targetGammaBoundarySize arguments.resultBool
    arguments.ruleTable arguments.ruleWidth arguments.ruleTokenCount
    arguments.ruleProofTag arguments.ruleCertificateTag
    arguments.ruleGammaStart arguments.ruleGammaFinish
    arguments.ruleGammaBoundary arguments.ruleGammaCount
    arguments.ruleGammaBoundarySize
    arguments.ruleFormulaStart arguments.ruleFormulaFinish
    arguments.ruleFormulaBoundary arguments.ruleFormulaCount
    arguments.ruleFormulaBoundarySize
    arguments.ruleNegatedStart arguments.ruleNegatedFinish
    arguments.ruleNegatedBoundary arguments.ruleNegatedCount
    arguments.ruleNegatedBoundarySize arguments.ruleStateBoundary
    arguments.ruleStateCount arguments.ruleEmptyStart
    arguments.ruleEmptyFinish arguments.ruleEmptyBoundary
    arguments.ruleEmptyBoundarySize arguments.ruleTableWidth
    arguments.ruleValueBound arguments.paCoordinates
    arguments.firstParseCoordinates arguments.secondParseCoordinates
    arguments.combineCoordinates arguments.firstParseSize
    arguments.secondParseSize arguments.combineSize

structure CompactNumericVerifierStepFormulaWitness
    (stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat) where
  environment : Fin 429 → Nat
  stateTable_eq : environment 0 = stateTable
  stateWidth_eq : environment 1 = stateWidth
  stateTokenCount_eq : environment 2 = stateTokenCount
  currentStart_eq : environment 3 = currentStart
  currentFinish_eq : environment 4 = currentFinish
  nextStart_eq : environment 24 = nextStart
  nextFinish_eq : environment 25 = nextFinish
  formula : compactNumericVerifierStepGraphDef.val.Evalb environment

def CompactNumericVerifierStepArguments.toFormulaWitness
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (arguments : CompactNumericVerifierStepArguments)
    (hcurrentStart : currentCoordinates.start = currentStart)
    (hcurrentFinish : currentCoordinates.finish = currentFinish)
    (hnextStart : nextCoordinates.start = nextStart)
    (hnextFinish : nextCoordinates.finish = nextFinish)
    (hgraph : arguments.Graph stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness) :
    CompactNumericVerifierStepFormulaWitness
      stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish := by
  let env := arguments.environment
    stateTable stateWidth stateTokenCount
    currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
  refine
    { environment := env
      stateTable_eq := by rfl
      stateWidth_eq := by rfl
      stateTokenCount_eq := by rfl
      currentStart_eq := ?_
      currentFinish_eq := ?_
      nextStart_eq := ?_
      nextFinish_eq := ?_
      formula := ?_ }
  · change currentCoordinates.start = currentStart
    exact hcurrentStart
  · change currentCoordinates.finish = currentFinish
    exact hcurrentFinish
  · change nextCoordinates.start = nextStart
    exact hnextStart
  · change nextCoordinates.finish = nextFinish
    exact hnextFinish
  · exact (compactNumericVerifierStepGraphDef_spec
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      arguments.taskCoordinates arguments.taskSizeWitness
      arguments.proofTable arguments.proofWidth arguments.proofTokenCount
      arguments.proofInputStart arguments.proofInputFinish
      arguments.rootStart arguments.rootFinish arguments.proofTag
      arguments.proofEndpointBound
      arguments.certificateTable arguments.certificateWidth
      arguments.certificateTokenCount arguments.certificateInputStart
      arguments.certificateInputFinish
      arguments.axiomStart arguments.axiomFinish
      arguments.formulaStart arguments.formulaFinish
      arguments.suffixStart arguments.suffixFinish arguments.certificateTag
      arguments.certificateEndpointBound
      arguments.rootGammaFinish arguments.rootGammaCount
      arguments.rootGammaBoundary arguments.firstFinish arguments.firstCount
      arguments.secondFinish arguments.secondCount arguments.witnessFinish
      arguments.witnessCount arguments.suffixCount
      arguments.rootGammaBoundarySize
      arguments.targetStart arguments.targetFinish
      arguments.targetGammaFinish arguments.targetGammaCount
      arguments.targetGammaBoundary arguments.targetBool
      arguments.targetGammaBoundarySize arguments.resultBool
      arguments.ruleTable arguments.ruleWidth arguments.ruleTokenCount
      arguments.ruleProofTag arguments.ruleCertificateTag
      arguments.ruleGammaStart arguments.ruleGammaFinish
      arguments.ruleGammaBoundary arguments.ruleGammaCount
      arguments.ruleGammaBoundarySize
      arguments.ruleFormulaStart arguments.ruleFormulaFinish
      arguments.ruleFormulaBoundary arguments.ruleFormulaCount
      arguments.ruleFormulaBoundarySize
      arguments.ruleNegatedStart arguments.ruleNegatedFinish
      arguments.ruleNegatedBoundary arguments.ruleNegatedCount
      arguments.ruleNegatedBoundarySize arguments.ruleStateBoundary
      arguments.ruleStateCount arguments.ruleEmptyStart
      arguments.ruleEmptyFinish arguments.ruleEmptyBoundary
      arguments.ruleEmptyBoundarySize arguments.ruleTableWidth
      arguments.ruleValueBound arguments.paCoordinates
      arguments.firstParseCoordinates arguments.secondParseCoordinates
      arguments.combineCoordinates arguments.firstParseSize
      arguments.secondParseSize arguments.combineSize).2 hgraph

def CompactNumericVerifierCanonicalStepFormula
    (currentState nextState : CompactNumericVerifierState) : Prop :=
  ∃ backTokens : List Nat,
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    Nonempty (CompactNumericVerifierStepFormulaWitness
      (compactFixedWidthTableCode width tokens) width tokens.length
      0 currentTokens.length currentTokens.length
      (currentTokens.length + nextTokens.length))

theorem CompactNumericVerifierCanonicalStepFormula.exists_of_halted
    (proofTokens certificateTokens : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (result : Bool) :
    CompactNumericVerifierCanonicalStepFormula
      (((proofTokens, certificateTokens), (tasks, values)), some result)
      (((proofTokens, certificateTokens), (tasks, values)), some result) := by
  let state : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, values)), some result)
  let stateTokens := compactAdditiveEncode state
  let tokens := stateTokens ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  have hcanonical :=
    CompactNumericVerifierCanonicalHaltedGraph.exists_of_some
      proofTokens certificateTokens tasks values result
  change CompactNumericVerifierCanonicalHaltedGraph state at hcanonical
  dsimp only [CompactNumericVerifierCanonicalHaltedGraph] at hcanonical
  rcases hcanonical with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      hcurrentStart, hcurrentFinish, hnextStart, hnextFinish,
      hcurrentCore, hnextCore, hhalted⟩
  let arguments := compactNumericVerifierStepUnusedArguments
  have hgraph : arguments.Graph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness := by
    exact Or.inl ⟨hcurrentCore, hnextCore, hhalted⟩
  refine ⟨[], ?_⟩
  simp only [List.append_nil]
  change Nonempty (CompactNumericVerifierStepFormulaWitness
    (compactFixedWidthTableCode width tokens) width tokens.length
    0 stateTokens.length stateTokens.length
    (stateTokens.length + stateTokens.length))
  exact ⟨arguments.toFormulaWitness
    hcurrentStart hcurrentFinish hnextStart hnextFinish hgraph⟩

theorem CompactNumericVerifierCanonicalStepFormula.exists_of_finish
    (proofTokens certificateTokens : List Nat)
    (values : List CompactNumericChildResult) :
    let payload : CompactNumericRunningPayload :=
      ((proofTokens, certificateTokens), ([], values))
    CompactNumericVerifierCanonicalStepFormula
      (payload, none) (compactNumericFinishState payload) := by
  let payload : CompactNumericRunningPayload :=
    ((proofTokens, certificateTokens), ([], values))
  let currentState : CompactNumericVerifierState := (payload, none)
  let nextState := compactNumericFinishState payload
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  have hcanonical :=
    CompactNumericVerifierCanonicalFinishGraph.exists
      proofTokens certificateTokens values
  dsimp only [CompactNumericVerifierCanonicalFinishGraph] at hcanonical
  rcases hcanonical with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      hcurrentStart, hcurrentFinish, hnextStart, hnextFinish,
      hcurrentCore, hnextCore, hfinish⟩
  let arguments := compactNumericVerifierStepUnusedArguments
  have hgraph : arguments.Graph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness := by
    exact Or.inr (Or.inl ⟨hcurrentCore, hnextCore, hfinish⟩)
  refine ⟨[], ?_⟩
  simp only [List.append_nil]
  change Nonempty (CompactNumericVerifierStepFormulaWitness
    (compactFixedWidthTableCode width tokens) width tokens.length
    0 currentTokens.length currentTokens.length
    (currentTokens.length + nextTokens.length))
  exact ⟨arguments.toFormulaWitness
    hcurrentStart hcurrentFinish hnextStart hnextFinish hgraph⟩

theorem CompactNumericVerifierCanonicalStepFormula.exists_of_halted_case
    {currentState nextState : CompactNumericVerifierState}
    (hcase : CompactNumericVerifierHaltedStepCase currentState nextState) :
    CompactNumericVerifierCanonicalStepFormula currentState nextState := by
  rcases currentState with
    ⟨⟨⟨proofTokens, certificateTokens⟩, ⟨tasks, values⟩⟩, status⟩
  cases status with
  | none => simp [CompactNumericVerifierHaltedStepCase] at hcase
  | some result =>
      have hnext := hcase.2
      subst nextState
      exact CompactNumericVerifierCanonicalStepFormula.exists_of_halted
        proofTokens certificateTokens tasks values result

theorem CompactNumericVerifierCanonicalStepFormula.exists_of_finish_case
    {currentState nextState : CompactNumericVerifierState}
    (hcase : CompactNumericVerifierFinishStepCase currentState nextState) :
    CompactNumericVerifierCanonicalStepFormula currentState nextState := by
  rcases currentState with
    ⟨⟨⟨proofTokens, certificateTokens⟩, ⟨tasks, values⟩⟩, status⟩
  rcases hcase with ⟨hstatus, htasks, hnext⟩
  change status = none at hstatus
  change tasks = [] at htasks
  subst status
  subst tasks
  subst nextState
  exact CompactNumericVerifierCanonicalStepFormula.exists_of_finish
    proofTokens certificateTokens values

theorem CompactNumericVerifierCanonicalStepFormula.exists_of_parse_case
    {currentState nextState : CompactNumericVerifierState}
    (hcase : CompactNumericVerifierParseStepCase currentState nextState) :
    CompactNumericVerifierCanonicalStepFormula currentState nextState := by
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  have hlayoutsRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hlayouts :
      CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentState ∧
        CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          currentTokens.length (currentTokens.length + nextTokens.length)
          nextState := by
    simpa only [currentTokens, nextTokens, tokens, width,
      List.append_nil] using hlayoutsRaw
  rcases
      exists_compactNumericVerifierParseStateGraphWitness_of_public_step
        hlayouts.1 hlayouts.2 hcase with
    ⟨witness⟩
  let arguments :=
    CompactNumericVerifierStepArguments.ofParseWitness witness
  have hgraph : arguments.Graph
      (compactFixedWidthTableCode width tokens) width tokens.length
      witness.currentCoordinates witness.nextCoordinates
      witness.currentSizeWitness witness.nextSizeWitness := by
    dsimp only [CompactNumericVerifierStepArguments.Graph, arguments,
      CompactNumericVerifierStepArguments.ofParseWitness]
    exact Or.inr (Or.inr (Or.inl witness.graph))
  refine ⟨[], ?_⟩
  simp only [List.append_nil]
  change Nonempty (CompactNumericVerifierStepFormulaWitness
    (compactFixedWidthTableCode width tokens) width tokens.length
    0 currentTokens.length currentTokens.length
    (currentTokens.length + nextTokens.length))
  exact ⟨arguments.toFormulaWitness
    witness.currentStart_eq witness.currentFinish_eq
    witness.nextStart_eq witness.nextFinish_eq hgraph⟩

theorem CompactNumericVerifierCanonicalStepFormula.exists_of_combine
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10) :
    CompactNumericVerifierCanonicalStepFormula
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
      (compactNumericCombineState task
        ((proofTokens, certificateTokens), (tasks, source))) := by
  rcases
      CompactNumericVerifierCanonicalCombineStateGraph.exists_of_public_step
        proofTokens certificateTokens task tasks source htaskNe with
    ⟨target, nextStatus, backTokens, htransition, hcanonical⟩
  rw [htransition]
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  dsimp only [CompactNumericVerifierCanonicalCombineGraph] at hcanonical
  rcases hcanonical with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, ruleWitness,
      hcurrentStart, hcurrentFinish, hnextStart, hnextFinish, hcombine⟩
  let arguments := CompactNumericVerifierStepArguments.ofCombine
    taskCoordinates taskSizeWitness ruleWitness
  have hgraph : arguments.Graph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness := by
    dsimp only [CompactNumericVerifierStepArguments.Graph, arguments,
      CompactNumericVerifierStepArguments.ofCombine]
    refine Or.inr (Or.inr (Or.inr ?_))
    simpa only [compactNumericVerifierStepCombineRuleWitness,
      compactNumericVerifierCombineRuleWitnessOf] using hcombine
  refine ⟨backTokens, ?_⟩
  change Nonempty (CompactNumericVerifierStepFormulaWitness
    (compactFixedWidthTableCode width tokens) width tokens.length
    0 currentTokens.length currentTokens.length
    (currentTokens.length + nextTokens.length))
  exact ⟨arguments.toFormulaWitness
    hcurrentStart hcurrentFinish hnextStart hnextFinish hgraph⟩

theorem CompactNumericVerifierCanonicalStepFormula.exists_of_combine_case
    {currentState nextState : CompactNumericVerifierState}
    (hcase : CompactNumericVerifierCombineStepCase currentState nextState) :
    CompactNumericVerifierCanonicalStepFormula currentState nextState := by
  rcases currentState with
    ⟨⟨⟨proofTokens, certificateTokens⟩, ⟨currentTasks, values⟩⟩, status⟩
  rcases hcase with
    ⟨task, restTasks, hstatus, htasks, htaskNe, hnext⟩
  change status = none at hstatus
  change currentTasks = task :: restTasks at htasks
  subst status
  subst currentTasks
  subst nextState
  exact CompactNumericVerifierCanonicalStepFormula.exists_of_combine
    proofTokens certificateTokens task restTasks values htaskNe

theorem CompactNumericVerifierCanonicalStepFormula.exists_of_public_step
    (currentState : CompactNumericVerifierState) :
    CompactNumericVerifierCanonicalStepFormula
      currentState (compactNumericVerifierStep currentState) := by
  have hcases :=
    (compactNumericVerifierStep_cases_iff
      currentState (compactNumericVerifierStep currentState)).2 rfl
  rcases hcases with hhalted | hfinish | hparse | hcombine
  · exact
      CompactNumericVerifierCanonicalStepFormula.exists_of_halted_case hhalted
  · exact
      CompactNumericVerifierCanonicalStepFormula.exists_of_finish_case hfinish
  · exact
      CompactNumericVerifierCanonicalStepFormula.exists_of_parse_case hparse
  · exact
      CompactNumericVerifierCanonicalStepFormula.exists_of_combine_case hcombine

#print axioms CompactNumericVerifierStepArguments.toFormulaWitness
#print axioms CompactNumericVerifierCanonicalStepFormula.exists_of_halted_case
#print axioms CompactNumericVerifierCanonicalStepFormula.exists_of_finish_case
#print axioms CompactNumericVerifierCanonicalStepFormula.exists_of_parse_case
#print axioms CompactNumericVerifierCanonicalStepFormula.exists_of_combine_case
#print axioms CompactNumericVerifierCanonicalStepFormula.exists_of_public_step

end FoundationCompactNumericListedDirectVerifierStepCompleteness
