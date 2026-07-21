import integration.FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds
import integration.FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
import integration.FoundationCompactNumericListedDirectVerifierStepCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness

/-!
# Quantitative coordinate bounds for canonical verifier steps

The first quantitative layer controls the twenty-one state-core coordinates
that occur twice in every 429-column step row.  The bound retains the exact
canonical task and child-result row widths carried by the canonical core
package; no arbitrary formula witness or unbounded size witness is accepted.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepCoordinateBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafStateCoordinates
open FoundationCompactNumericListedDirectVerifierParseStateCompleteness
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds
open FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph
open FoundationCompactNumericListedDirectVerifierCombineCanonicalCompleteness
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierHaltedCompleteness
open FoundationCompactNumericListedDirectVerifierFinishCompleteness

/-- One common binary-size budget for the table header and the twenty-one
state-core coordinates belonging to one state slice. -/
def compactNumericVerifierStateCoreCoordinateSizeBound
    (width tokenCount : Nat) : Nat :=
  tokenCount * width +
    (tokenCount + 1) * tokenCount +
    (compactNumericVerifierTaskRowTableWidth width tokenCount + 1) +
    (compactNumericChildResultRowTableWidth width tokenCount + 1) +
    width + tokenCount + 4

theorem tokenTableArea_le_stateCoreCoordinateSizeBound
    (width tokenCount : Nat) :
    tokenCount * width <=
      compactNumericVerifierStateCoreCoordinateSizeBound width tokenCount := by
  unfold compactNumericVerifierStateCoreCoordinateSizeBound
  omega

theorem boundaryArea_le_stateCoreCoordinateSizeBound
    (width tokenCount : Nat) :
    (tokenCount + 1) * tokenCount <=
      compactNumericVerifierStateCoreCoordinateSizeBound width tokenCount := by
  unfold compactNumericVerifierStateCoreCoordinateSizeBound
  omega

theorem taskRowWidth_succ_le_stateCoreCoordinateSizeBound
    (width tokenCount : Nat) :
    compactNumericVerifierTaskRowTableWidth width tokenCount + 1 <=
      compactNumericVerifierStateCoreCoordinateSizeBound width tokenCount := by
  unfold compactNumericVerifierStateCoreCoordinateSizeBound
  omega

theorem childRowWidth_succ_le_stateCoreCoordinateSizeBound
    (width tokenCount : Nat) :
    compactNumericChildResultRowTableWidth width tokenCount + 1 <=
      compactNumericVerifierStateCoreCoordinateSizeBound width tokenCount := by
  unfold compactNumericVerifierStateCoreCoordinateSizeBound
  omega

theorem width_le_stateCoreCoordinateSizeBound
    (width tokenCount : Nat) :
    width <=
      compactNumericVerifierStateCoreCoordinateSizeBound width tokenCount := by
  unfold compactNumericVerifierStateCoreCoordinateSizeBound
  omega

theorem tokenCount_le_stateCoreCoordinateSizeBound
    (width tokenCount : Nat) :
    tokenCount <=
      compactNumericVerifierStateCoreCoordinateSizeBound width tokenCount := by
  unfold compactNumericVerifierStateCoreCoordinateSizeBound
  omega

theorem compactAdditiveNatListSlice_coordinates_le
    {tokenTable width tokenCount start count finish : Nat}
    (hslice : CompactAdditiveNatListSlice
      tokenTable width tokenCount start count finish) :
    start < tokenCount ∧ count <= tokenCount ∧ finish <= tokenCount := by
  rcases hslice with ⟨bodyStart, _hbodyStart, hheader, hfinish⟩
  have hstart : start < tokenCount := hheader.1.1
  have hcount : bodyStart + count <= tokenCount := hheader.2
  subst finish
  exact ⟨hstart, by omega, by omega⟩

theorem compactAdditiveStructuredListLayout_coordinates_le
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    start <= tokenCount ∧ count <= tokenCount ∧ finish <= tokenCount := by
  rcases hlayout with ⟨bodyStart, _hbodyStart, hheader, hboundary⟩
  have hstart : start < tokenCount := hheader.1.1
  have hcount : bodyStart + count <= tokenCount := hheader.2
  have hfinish : finish <= tokenCount := hboundary.2.1
  omega

theorem compactAdditiveOptionLayout_coordinates_le
    {tokenTable width tokenCount start tag payloadStart finish : Nat}
    (hlayout : CompactAdditiveOptionLayout
      tokenTable width tokenCount start tag payloadStart finish) :
    start <= tokenCount ∧ payloadStart <= tokenCount ∧
      finish <= tokenCount ∧ tag <= 1 := by
  have hstart : start < tokenCount := hlayout.1.1
  have hpayload : payloadStart = start + 1 := hlayout.1.2.1
  rcases hlayout.2 with hnone | hsome
  · rcases hnone with ⟨htag, hfinish⟩
    omega
  · rcases hsome with ⟨htag, _hpayloadFinish, hfinish⟩
    omega

structure CompactNumericVerifierStateCoreCoordinateSizeBounds
    (coordinates : CompactNumericVerifierStateRowCoordinates)
    (sizeWitness : CompactNumericVerifierStateSizeWitness)
    (bound : Nat) : Prop where
  start : Nat.size coordinates.start <= bound
  finish : Nat.size coordinates.finish <= bound
  proofFinish : Nat.size coordinates.proofFinish <= bound
  proofCount : Nat.size coordinates.proofCount <= bound
  certificateFinish : Nat.size coordinates.certificateFinish <= bound
  certificateCount : Nat.size coordinates.certificateCount <= bound
  tasksFinish : Nat.size coordinates.tasksFinish <= bound
  taskCount : Nat.size coordinates.taskCount <= bound
  taskBoundary : Nat.size coordinates.taskBoundary <= bound
  valuesFinish : Nat.size coordinates.valuesFinish <= bound
  valueCount : Nat.size coordinates.valueCount <= bound
  valueBoundary : Nat.size coordinates.valueBoundary <= bound
  statusTag : Nat.size coordinates.statusTag <= bound
  statusPayloadStart : Nat.size coordinates.statusPayloadStart <= bound
  statusBool : Nat.size coordinates.statusBool <= bound
  taskBoundarySize : Nat.size sizeWitness.taskBoundarySize <= bound
  valueBoundarySize : Nat.size sizeWitness.valueBoundarySize <= bound
  taskTableWidth : Nat.size sizeWitness.taskTableWidth <= bound
  taskValueBound : Nat.size sizeWitness.taskValueBound <= bound
  valueTableWidth : Nat.size sizeWitness.valueTableWidth <= bound
  valueValueBound : Nat.size sizeWitness.valueValueBound <= bound

theorem CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
    {tokenTable width tokenCount start finish : Nat}
    {state : CompactNumericVerifierState}
    {coordinates : CompactNumericVerifierStateRowCoordinates}
    {sizeWitness : CompactNumericVerifierStateSizeWitness}
    (hpackage : CompactNumericVerifierStateCanonicalCorePackage
      tokenTable width tokenCount start finish state coordinates sizeWitness) :
    CompactNumericVerifierStateCoreCoordinateSizeBounds
      coordinates sizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound width tokenCount) := by
  rcases hpackage with
    ⟨_hstartEq, _hfinishEq, _hproofLayout, _hcertificateLayout,
      _htaskLayout, _htaskRows, _hvalueLayout, _hvalueRows,
      _htaskCountEq, _hvalueCountEq,
      htaskTableWidthEq, htaskValueBoundEq,
      hvalueTableWidthEq, hvalueValueBoundEq,
      hstatusCase, hcore⟩
  rcases hcore with
    ⟨hproof, hcertificate, htask, _htaskRowsGraph,
      htaskBoundarySizeEq, htaskBoundarySizeLe,
      hvalue, _hvalueRowsGraph,
      hvalueBoundarySizeEq, hvalueBoundarySizeLe,
      hstatus, _hstatusFormula⟩
  rcases compactAdditiveNatListSlice_coordinates_le hproof with
    ⟨hstart, hproofCount, hproofFinish⟩
  rcases compactAdditiveNatListSlice_coordinates_le hcertificate with
    ⟨_hproofFinishStart, hcertificateCount, hcertificateFinish⟩
  rcases compactAdditiveStructuredListLayout_coordinates_le htask with
    ⟨_hcertificateFinishStart, htaskCount, htasksFinish⟩
  rcases compactAdditiveStructuredListLayout_coordinates_le hvalue with
    ⟨_htasksFinishStart, hvalueCount, hvaluesFinish⟩
  rcases compactAdditiveOptionLayout_coordinates_le hstatus with
    ⟨_hvaluesFinishStart, hstatusPayloadStart, hfinish, hstatusTag⟩
  have htokenCountPos : 1 <= tokenCount := by omega
  have hstatusBool : coordinates.statusBool <= 1 := by
    rcases hstatusCase with hnone | hsome
    · omega
    · rcases hsome with ⟨result, _hresult, _htag, hbool⟩
      rw [hbool]
      cases result <;> simp [compactAdditiveBoolTag]
  have hstatusTagToken : coordinates.statusTag <= tokenCount :=
    hstatusTag.trans htokenCountPos
  have hstatusBoolToken : coordinates.statusBool <= tokenCount :=
    hstatusBool.trans htokenCountPos
  have htaskBoundaryArea :
      sizeWitness.taskBoundarySize <= (tokenCount + 1) * tokenCount := by
    exact htaskBoundarySizeLe.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right htaskCount 1) (Nat.le_refl tokenCount))
  have hvalueBoundaryArea :
      sizeWitness.valueBoundarySize <= (tokenCount + 1) * tokenCount := by
    exact hvalueBoundarySizeLe.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hvalueCount 1) (Nat.le_refl tokenCount))
  have htokenBudget := tokenCount_le_stateCoreCoordinateSizeBound
    width tokenCount
  have hareaBudget := boundaryArea_le_stateCoreCoordinateSizeBound
    width tokenCount
  have hsmall (value : Nat) (hvalue : value <= tokenCount) :
      Nat.size value <=
        compactNumericVerifierStateCoreCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le hvalue).trans htokenBudget
  refine
    { start := hsmall coordinates.start (Nat.le_of_lt hstart)
      finish := hsmall coordinates.finish hfinish
      proofFinish := hsmall coordinates.proofFinish hproofFinish
      proofCount := hsmall coordinates.proofCount hproofCount
      certificateFinish := hsmall coordinates.certificateFinish
        hcertificateFinish
      certificateCount := hsmall coordinates.certificateCount
        hcertificateCount
      tasksFinish := hsmall coordinates.tasksFinish htasksFinish
      taskCount := hsmall coordinates.taskCount htaskCount
      taskBoundary := ?_
      valuesFinish := hsmall coordinates.valuesFinish hvaluesFinish
      valueCount := hsmall coordinates.valueCount hvalueCount
      valueBoundary := ?_
      statusTag := hsmall coordinates.statusTag hstatusTagToken
      statusPayloadStart := hsmall coordinates.statusPayloadStart
        hstatusPayloadStart
      statusBool := hsmall coordinates.statusBool hstatusBoolToken
      taskBoundarySize := ?_
      valueBoundarySize := ?_
      taskTableWidth := ?_
      taskValueBound := ?_
      valueTableWidth := ?_
      valueValueBound := ?_ }
  · rw [← htaskBoundarySizeEq]
    exact htaskBoundaryArea.trans hareaBudget
  · rw [← hvalueBoundarySizeEq]
    exact hvalueBoundaryArea.trans hareaBudget
  · exact (natSize_le_of_le (Nat.le_refl _)).trans
      (htaskBoundaryArea.trans hareaBudget)
  · exact (natSize_le_of_le (Nat.le_refl _)).trans
      (hvalueBoundaryArea.trans hareaBudget)
  · rw [htaskTableWidthEq]
    exact (natSize_le_of_le (Nat.le_refl _)).trans
      ((Nat.le_add_right _ 1).trans
        (taskRowWidth_succ_le_stateCoreCoordinateSizeBound width tokenCount))
  · rw [htaskValueBoundEq, Nat.size_pow]
    exact taskRowWidth_succ_le_stateCoreCoordinateSizeBound width tokenCount
  · rw [hvalueTableWidthEq]
    exact (natSize_le_of_le (Nat.le_refl _)).trans
      ((Nat.le_add_right _ 1).trans
        (childRowWidth_succ_le_stateCoreCoordinateSizeBound width tokenCount))
  · rw [hvalueValueBoundEq, Nat.size_pow]
    exact childRowWidth_succ_le_stateCoreCoordinateSizeBound width tokenCount

theorem canonicalStateTable_size_le_coordinateSizeBound
    (tokens : List Nat) (width : Nat) :
    Nat.size (compactFixedWidthTableCode width tokens) <=
      compactNumericVerifierStateCoreCoordinateSizeBound width tokens.length := by
  exact (compactFixedWidthTableCode_size_le width tokens).trans
    (tokenTableArea_le_stateCoreCoordinateSizeBound width tokens.length)

def compactNumericVerifierTaskCoordinateEnvironment
    (coordinates :
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness :
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskSizeWitness) :
    Fin 14 -> Nat :=
  ![coordinates.start, coordinates.finish, coordinates.tag,
    coordinates.gammaFinish, coordinates.gammaCount,
    coordinates.gammaBoundary, coordinates.firstFinish,
    coordinates.firstCount, coordinates.secondFinish,
    coordinates.secondCount, coordinates.witnessFinish,
    coordinates.witnessCount, coordinates.suffixCount,
    sizeWitness.gammaBoundarySize]

def compactNumericVerifierCombineRuleWitnessPaddedTailEnvironment
    (witness : CompactNumericVerifierCombineRuleWitness) : Fin 348 -> Nat :=
  fun coordinate =>
    if hcoordinate : coordinate.val < 12 then
      compactNumericVerifierCombineRuleWitnessTailEnvironment witness
        ⟨coordinate.val, hcoordinate⟩
    else 0

/-- The bounded task-head relation already bounds every exposed task field.
Taking binary sizes transfers all fourteen fields to the same bit budget used
for the enclosing canonical state. -/
theorem compactNumericVerifierTaskCoordinateEnvironment_size_le
    {tokenTable width tokenCount taskBoundary valueBound bound : Nat}
    {coordinates :
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness :
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskSizeWitness}
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
      coordinates sizeWitness)
    (hvalueBound : Nat.size valueBound <= bound)
    (coordinate : Fin 14) :
    Nat.size (compactNumericVerifierTaskCoordinateEnvironment
      coordinates sizeWitness coordinate) <= bound := by
  rcases hhead with
    ⟨hstart, hfinish, htag, hgammaFinish, hgammaCount,
      hgammaBoundary, hfirstFinish, hfirstCount,
      hsecondFinish, hsecondCount, hwitnessFinish, hwitnessCount,
      hsuffixCount, hgammaBoundarySize,
      _hstartEntry, _hfinishEntry, _hcore⟩
  have hsize {value : Nat} (hvalue : value <= valueBound) :
      Nat.size value <= bound :=
    (Nat.size_le_size hvalue).trans hvalueBound
  fin_cases coordinate <;>
    simp [compactNumericVerifierTaskCoordinateEnvironment] <;>
    apply hsize <;> assumption

def compactNumericVerifierStepFailureEnvironment
    (arguments : CompactNumericVerifierStepArguments)
    (stateTable stateWidth stateTokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness) : Fin 81 -> Nat :=
  compactNumericVerifierParseFailureSeparatedTablesStateGraphEnvironment
    stateTable stateWidth stateTokenCount
    currentCoordinates.start currentCoordinates.finish
    currentCoordinates.proofFinish currentCoordinates.proofCount
    currentCoordinates.certificateFinish currentCoordinates.certificateCount
    currentCoordinates.tasksFinish currentCoordinates.taskCount
    currentCoordinates.taskBoundary currentCoordinates.valuesFinish
    currentCoordinates.valueCount currentCoordinates.valueBoundary
    currentCoordinates.statusTag currentCoordinates.statusPayloadStart
    currentCoordinates.statusBool
    currentSizeWitness.taskBoundarySize currentSizeWitness.valueBoundarySize
    currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
    currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
    nextCoordinates.start nextCoordinates.finish
    nextCoordinates.proofFinish nextCoordinates.proofCount
    nextCoordinates.certificateFinish nextCoordinates.certificateCount
    nextCoordinates.tasksFinish nextCoordinates.taskCount
    nextCoordinates.taskBoundary nextCoordinates.valuesFinish
    nextCoordinates.valueCount nextCoordinates.valueBoundary
    nextCoordinates.statusTag nextCoordinates.statusPayloadStart
    nextCoordinates.statusBool
    nextSizeWitness.taskBoundarySize nextSizeWitness.valueBoundarySize
    nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
    nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
    arguments.taskCoordinates.start arguments.taskCoordinates.finish
    arguments.taskCoordinates.tag arguments.taskCoordinates.gammaFinish
    arguments.taskCoordinates.gammaCount arguments.taskCoordinates.gammaBoundary
    arguments.taskCoordinates.firstFinish arguments.taskCoordinates.firstCount
    arguments.taskCoordinates.secondFinish arguments.taskCoordinates.secondCount
    arguments.taskCoordinates.witnessFinish arguments.taskCoordinates.witnessCount
    arguments.taskCoordinates.suffixCount arguments.taskSizeWitness.gammaBoundarySize
    arguments.proofTable arguments.proofWidth arguments.proofTokenCount
    arguments.proofInputStart arguments.proofInputFinish
    arguments.rootStart arguments.rootFinish arguments.proofTag
    arguments.proofEndpointBound arguments.certificateTable
    arguments.certificateWidth arguments.certificateTokenCount
    arguments.certificateInputStart arguments.certificateInputFinish
    arguments.axiomStart arguments.axiomFinish
    arguments.formulaStart arguments.formulaFinish
    arguments.suffixStart arguments.suffixFinish
    arguments.certificateTag arguments.certificateEndpointBound

def compactNumericVerifierStepTailEnvironment
    (arguments : CompactNumericVerifierStepArguments) : Fin 348 -> Nat :=
  Matrix.vecAppend rfl
    (compactNumericVerifierParseSuccessParsedEnvironment
      arguments.rootGammaFinish arguments.rootGammaCount
      arguments.rootGammaBoundary arguments.firstFinish arguments.firstCount
      arguments.secondFinish arguments.secondCount arguments.witnessFinish
      arguments.witnessCount arguments.suffixCount
      arguments.rootGammaBoundarySize)
    (Matrix.vecAppend rfl
      (compactNumericVerifierParseLeafOutputEnvironment
        arguments.targetStart arguments.targetFinish
        arguments.targetGammaFinish arguments.targetGammaCount
        arguments.targetGammaBoundary arguments.targetBool
        arguments.targetGammaBoundarySize arguments.resultBool)
      (Matrix.vecAppend rfl
        (compactNumericVerifierParseClosedExtraEnvironment
          arguments.ruleTable arguments.ruleWidth arguments.ruleTokenCount
          arguments.ruleProofTag arguments.ruleCertificateTag
          arguments.ruleGammaStart arguments.ruleGammaFinish
          arguments.ruleGammaBoundary arguments.ruleGammaCount
          arguments.ruleGammaBoundarySize arguments.ruleFormulaStart
          arguments.ruleFormulaFinish arguments.ruleFormulaBoundary
          arguments.ruleFormulaCount arguments.ruleFormulaBoundarySize
          arguments.ruleNegatedStart arguments.ruleNegatedFinish
          arguments.ruleNegatedBoundary arguments.ruleNegatedCount
          arguments.ruleNegatedBoundarySize arguments.ruleStateBoundary
          arguments.ruleStateCount arguments.ruleEmptyStart
          arguments.ruleEmptyFinish arguments.ruleEmptyBoundary
          arguments.ruleEmptyBoundarySize arguments.ruleTableWidth
          arguments.ruleValueBound)
        (Matrix.vecAppend rfl
          (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
            arguments.paCoordinates)
          (compactNumericVerifierParseNonLeafEnvironment
            arguments.firstParseCoordinates arguments.secondParseCoordinates
            arguments.combineCoordinates arguments.firstParseSize
            arguments.secondParseSize arguments.combineSize))))

theorem compactNumericVerifierStepEnvironment_eq_vecAppend
    (arguments : CompactNumericVerifierStepArguments)
    (stateTable stateWidth stateTokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness) :
    arguments.environment stateTable stateWidth stateTokenCount
        currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness =
      Matrix.vecAppend rfl
        (compactNumericVerifierStepFailureEnvironment arguments
          stateTable stateWidth stateTokenCount
          currentCoordinates nextCoordinates
          currentSizeWitness nextSizeWitness)
        (compactNumericVerifierStepTailEnvironment arguments) := by
  rfl

def compactNumericVerifierStateCoreCoordinateEnvironment
    (coordinates : CompactNumericVerifierStateRowCoordinates)
    (sizeWitness : CompactNumericVerifierStateSizeWitness) : Fin 21 -> Nat :=
  ![coordinates.start, coordinates.finish,
    coordinates.proofFinish, coordinates.proofCount,
    coordinates.certificateFinish, coordinates.certificateCount,
    coordinates.tasksFinish, coordinates.taskCount,
    coordinates.taskBoundary, coordinates.valuesFinish,
    coordinates.valueCount, coordinates.valueBoundary,
    coordinates.statusTag, coordinates.statusPayloadStart,
    coordinates.statusBool,
    sizeWitness.taskBoundarySize, sizeWitness.valueBoundarySize,
    sizeWitness.taskTableWidth, sizeWitness.taskValueBound,
    sizeWitness.valueTableWidth, sizeWitness.valueValueBound]

def compactNumericVerifierStepStateHeaderEnvironment
    (stateTable stateWidth stateTokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness) : Fin 45 -> Nat :=
  Matrix.vecAppend rfl ![stateTable, stateWidth, stateTokenCount]
    (Matrix.vecAppend rfl
      (compactNumericVerifierStateCoreCoordinateEnvironment
        currentCoordinates currentSizeWitness)
      (compactNumericVerifierStateCoreCoordinateEnvironment
        nextCoordinates nextSizeWitness))

def compactNumericVerifierStepFailureTailEnvironment
    (arguments : CompactNumericVerifierStepArguments) : Fin 36 -> Nat :=
  ![arguments.taskCoordinates.start, arguments.taskCoordinates.finish,
    arguments.taskCoordinates.tag, arguments.taskCoordinates.gammaFinish,
    arguments.taskCoordinates.gammaCount,
    arguments.taskCoordinates.gammaBoundary,
    arguments.taskCoordinates.firstFinish,
    arguments.taskCoordinates.firstCount,
    arguments.taskCoordinates.secondFinish,
    arguments.taskCoordinates.secondCount,
    arguments.taskCoordinates.witnessFinish,
    arguments.taskCoordinates.witnessCount,
    arguments.taskCoordinates.suffixCount,
    arguments.taskSizeWitness.gammaBoundarySize,
    arguments.proofTable, arguments.proofWidth, arguments.proofTokenCount,
    arguments.proofInputStart, arguments.proofInputFinish,
    arguments.rootStart, arguments.rootFinish, arguments.proofTag,
    arguments.proofEndpointBound,
    arguments.certificateTable, arguments.certificateWidth,
    arguments.certificateTokenCount, arguments.certificateInputStart,
    arguments.certificateInputFinish,
    arguments.axiomStart, arguments.axiomFinish,
    arguments.formulaStart, arguments.formulaFinish,
    arguments.suffixStart, arguments.suffixFinish,
    arguments.certificateTag, arguments.certificateEndpointBound]

def compactNumericVerifierStepFailureNonTaskEnvironment
    (arguments : CompactNumericVerifierStepArguments) : Fin 22 -> Nat :=
  ![arguments.proofTable, arguments.proofWidth, arguments.proofTokenCount,
    arguments.proofInputStart, arguments.proofInputFinish,
    arguments.rootStart, arguments.rootFinish, arguments.proofTag,
    arguments.proofEndpointBound,
    arguments.certificateTable, arguments.certificateWidth,
    arguments.certificateTokenCount, arguments.certificateInputStart,
    arguments.certificateInputFinish,
    arguments.axiomStart, arguments.axiomFinish,
    arguments.formulaStart, arguments.formulaFinish,
    arguments.suffixStart, arguments.suffixFinish,
    arguments.certificateTag, arguments.certificateEndpointBound]

set_option maxRecDepth 65536 in
theorem compactNumericVerifierStepFailureNonTaskEnvironment_ofCombine_eq
    (taskCoordinates :
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness :
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskSizeWitness)
    (ruleWitness : CompactNumericVerifierCombineRuleWitness) :
    compactNumericVerifierStepFailureNonTaskEnvironment
        (CompactNumericVerifierStepArguments.ofCombine
          taskCoordinates taskSizeWitness ruleWitness) =
      compactNumericVerifierCombineRuleWitnessHeadEnvironment ruleWitness := by
  funext coordinate
  fin_cases coordinate <;>
    rfl

set_option maxHeartbeats 400000 in
set_option maxRecDepth 65536 in
theorem compactNumericVerifierStepTailEnvironment_ofCombine_eq
    (taskCoordinates :
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness :
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskSizeWitness)
    (ruleWitness : CompactNumericVerifierCombineRuleWitness) :
    compactNumericVerifierStepTailEnvironment
        (CompactNumericVerifierStepArguments.ofCombine
          taskCoordinates taskSizeWitness ruleWitness) =
      compactNumericVerifierCombineRuleWitnessPaddedTailEnvironment
        ruleWitness := by
  funext coordinate
  fin_cases coordinate <;>
    rfl

set_option maxRecDepth 65536 in
theorem compactNumericVerifierStepFailureTailEnvironment_eq_vecAppend
    (arguments : CompactNumericVerifierStepArguments) :
    compactNumericVerifierStepFailureTailEnvironment arguments =
      Matrix.vecAppend rfl
        (compactNumericVerifierTaskCoordinateEnvironment
          arguments.taskCoordinates arguments.taskSizeWitness)
        (compactNumericVerifierStepFailureNonTaskEnvironment arguments) := by
  funext coordinate
  fin_cases coordinate <;>
    rfl

set_option maxHeartbeats 100000 in
set_option maxRecDepth 65536 in
theorem compactNumericVerifierStepFailureEnvironment_eq_vecAppend
    (arguments : CompactNumericVerifierStepArguments)
    (stateTable stateWidth stateTokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness) :
    compactNumericVerifierStepFailureEnvironment arguments
        stateTable stateWidth stateTokenCount
        currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness =
      Matrix.vecAppend rfl
        (compactNumericVerifierStepStateHeaderEnvironment
          stateTable stateWidth stateTokenCount
          currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness)
        (compactNumericVerifierStepFailureTailEnvironment arguments) := by
  simp only [compactNumericVerifierStepFailureEnvironment,
    compactNumericVerifierParseFailureSeparatedTablesStateGraphEnvironment,
    compactNumericVerifierStepStateHeaderEnvironment,
    compactNumericVerifierStateCoreCoordinateEnvironment,
    compactNumericVerifierStepFailureTailEnvironment,
    Matrix.cons_vecAppend, Matrix.empty_vecAppend]

theorem natSize_coordinate_le_finSum
    {length : Nat} (environment : Fin length -> Nat)
    (coordinate : Fin length) :
    Nat.size (environment coordinate) <=
      ∑ index, Nat.size (environment index) := by
  exact Finset.single_le_sum
    (f := fun index => Nat.size (environment index))
    (s := Finset.univ)
    (fun index _ => Nat.zero_le (Nat.size (environment index)))
    (Finset.mem_univ coordinate)

theorem natSize_vecAppend_le
    {leftLength rightLength totalLength bound : Nat}
    (length_eq : totalLength = leftLength + rightLength)
    (left : Fin leftLength -> Nat) (right : Fin rightLength -> Nat)
    (hleft : forall coordinate, Nat.size (left coordinate) <= bound)
    (hright : forall coordinate, Nat.size (right coordinate) <= bound)
    (coordinate : Fin totalLength) :
    Nat.size (Matrix.vecAppend length_eq left right coordinate) <= bound := by
  rw [Matrix.vecAppend_eq_ite]
  dsimp only
  split_ifs with hcoordinate
  · exact hleft ⟨coordinate, hcoordinate⟩
  · exact hright ⟨coordinate - leftLength, by omega⟩

theorem compactNumericVerifierStepFailureTailEnvironment_size_le
    (arguments : CompactNumericVerifierStepArguments)
    {tokenTable width tokenCount taskBoundary valueBound bound : Nat}
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
      arguments.taskCoordinates arguments.taskSizeWitness)
    (hvalueBound : Nat.size valueBound <= bound)
    (hnonTask : forall coordinate : Fin 22,
      Nat.size (compactNumericVerifierStepFailureNonTaskEnvironment
        arguments coordinate) <= bound)
    (coordinate : Fin 36) :
    Nat.size (compactNumericVerifierStepFailureTailEnvironment
      arguments coordinate) <= bound := by
  rw [compactNumericVerifierStepFailureTailEnvironment_eq_vecAppend]
  apply natSize_vecAppend_le rfl
  · exact compactNumericVerifierTaskCoordinateEnvironment_size_le
      hhead hvalueBound
  · exact hnonTask

def compactNumericVerifierStepArgumentsEnvironmentConstant
    (arguments : CompactNumericVerifierStepArguments) : Nat :=
  (∑ coordinate,
      Nat.size
        (compactNumericVerifierStepFailureTailEnvironment arguments coordinate)) +
    ∑ coordinate,
      Nat.size
        (compactNumericVerifierStepTailEnvironment arguments coordinate)

def compactNumericVerifierStepArgumentsCoordinateSizeBound
    (arguments : CompactNumericVerifierStepArguments)
    (stateWidth stateTokenCount : Nat) : Nat :=
    compactNumericVerifierStateCoreCoordinateSizeBound
      stateWidth stateTokenCount +
    compactNumericVerifierStepArgumentsEnvironmentConstant arguments

def compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
    (stateWidth stateTokenCount ruleCoordinateBound : Nat) : Nat :=
  let stateBound :=
    compactNumericVerifierStateCoreCoordinateSizeBound
      stateWidth stateTokenCount
  stateBound + 384 * (stateBound + ruleCoordinateBound)

/-- The 384 non-state coordinates contribute at most 384 copies of any common
pointwise bit-size budget. -/
theorem compactNumericVerifierStepArgumentsEnvironmentConstant_le
    (arguments : CompactNumericVerifierStepArguments) (bound : Nat)
    (hfailure : forall coordinate : Fin 36,
      Nat.size
        (compactNumericVerifierStepFailureTailEnvironment arguments coordinate) <=
          bound)
    (htail : forall coordinate : Fin 348,
      Nat.size
        (compactNumericVerifierStepTailEnvironment arguments coordinate) <=
          bound) :
    compactNumericVerifierStepArgumentsEnvironmentConstant arguments <=
      384 * bound := by
  unfold compactNumericVerifierStepArgumentsEnvironmentConstant
  calc
    _ <= (∑ _coordinate : Fin 36, bound) +
        ∑ _coordinate : Fin 348, bound := by
      apply Nat.add_le_add
      · exact Finset.sum_le_sum fun coordinate _ => hfailure coordinate
      · exact Finset.sum_le_sum fun coordinate _ => htail coordinate
    _ = 384 * bound := by simp; omega

/-- For a combine step, the 384 non-state coordinates reduce to the bounded
task head and the thirty-four coordinates of the concrete rule witness. -/
theorem compactNumericVerifierStepArgumentsEnvironmentConstant_ofCombine_le
    (taskCoordinates :
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness :
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskSizeWitness)
    (ruleWitness : CompactNumericVerifierCombineRuleWitness)
    {tokenTable width tokenCount taskBoundary valueBound bound : Nat}
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
      taskCoordinates taskSizeWitness)
    (hvalueBound : Nat.size valueBound <= bound)
    (hrule : forall coordinate : Fin 34,
      Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
        ruleWitness coordinate) <= bound) :
    compactNumericVerifierStepArgumentsEnvironmentConstant
        (CompactNumericVerifierStepArguments.ofCombine
          taskCoordinates taskSizeWitness ruleWitness) <=
      384 * bound := by
  apply compactNumericVerifierStepArgumentsEnvironmentConstant_le
  · apply compactNumericVerifierStepFailureTailEnvironment_size_le
      _ hhead hvalueBound
    intro coordinate
    rw [compactNumericVerifierStepFailureNonTaskEnvironment_ofCombine_eq]
    simpa [compactNumericVerifierCombineRuleWitnessHeadEnvironment] using
      hrule ⟨coordinate.val, by omega⟩
  · intro coordinate
    rw [compactNumericVerifierStepTailEnvironment_ofCombine_eq]
    simp only [compactNumericVerifierCombineRuleWitnessPaddedTailEnvironment]
    split_ifs with hcoordinate
    · simpa [compactNumericVerifierCombineRuleWitnessTailEnvironment] using
        hrule ⟨coordinate.val + 22, by omega⟩
    · simp

def compactNumericVerifierStepUnusedEnvironmentConstant : Nat :=
  compactNumericVerifierStepArgumentsEnvironmentConstant
    compactNumericVerifierStepUnusedArguments

def compactNumericVerifierStepUnusedCoordinateSizeBound
    (stateWidth stateTokenCount : Nat) : Nat :=
  compactNumericVerifierStepArgumentsCoordinateSizeBound
    compactNumericVerifierStepUnusedArguments stateWidth stateTokenCount

set_option maxHeartbeats 400000 in
set_option maxRecDepth 65536 in
theorem compactNumericVerifierStateCoreCoordinateEnvironment_size_le
    {coordinates : CompactNumericVerifierStateRowCoordinates}
    {sizeWitness : CompactNumericVerifierStateSizeWitness}
    {bound : Nat}
    (hbounds : CompactNumericVerifierStateCoreCoordinateSizeBounds
      coordinates sizeWitness bound)
    (coordinate : Fin 21) :
    Nat.size (compactNumericVerifierStateCoreCoordinateEnvironment
      coordinates sizeWitness coordinate) <= bound := by
  cases hbounds
  fin_cases coordinate <;>
    simp_all [compactNumericVerifierStateCoreCoordinateEnvironment]

theorem compactNumericVerifierStepStateHeaderEnvironment_size_le
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (htable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount)
    (hcurrent : CompactNumericVerifierStateCoreCoordinateSizeBounds
      currentCoordinates currentSizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount))
    (hnext : CompactNumericVerifierStateCoreCoordinateSizeBounds
      nextCoordinates nextSizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount))
    (coordinate : Fin 45) :
    Nat.size (compactNumericVerifierStepStateHeaderEnvironment
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness coordinate) <=
        compactNumericVerifierStateCoreCoordinateSizeBound
          stateWidth stateTokenCount := by
  have hwidth : Nat.size stateWidth <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount :=
    (natSize_le_of_le (Nat.le_refl stateWidth)).trans
      (width_le_stateCoreCoordinateSizeBound stateWidth stateTokenCount)
  have htokenCount : Nat.size stateTokenCount <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount :=
    (natSize_le_of_le (Nat.le_refl stateTokenCount)).trans
      (tokenCount_le_stateCoreCoordinateSizeBound stateWidth stateTokenCount)
  unfold compactNumericVerifierStepStateHeaderEnvironment
  apply natSize_vecAppend_le rfl
  · intro index
    fin_cases index
    · exact htable
    · exact hwidth
    · exact htokenCount
  · intro index
    apply natSize_vecAppend_le rfl
    · intro currentIndex
      exact compactNumericVerifierStateCoreCoordinateEnvironment_size_le
        hcurrent currentIndex
    · intro nextIndex
      exact compactNumericVerifierStateCoreCoordinateEnvironment_size_le
        hnext nextIndex

theorem compactNumericVerifierStepFailureEnvironment_size_le
    (arguments : CompactNumericVerifierStepArguments)
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (htable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount)
    (hcurrent : CompactNumericVerifierStateCoreCoordinateSizeBounds
      currentCoordinates currentSizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount))
    (hnext : CompactNumericVerifierStateCoreCoordinateSizeBounds
      nextCoordinates nextSizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount))
    (coordinate : Fin 81) :
    Nat.size (compactNumericVerifierStepFailureEnvironment arguments
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness coordinate) <=
        compactNumericVerifierStepArgumentsCoordinateSizeBound arguments
          stateWidth stateTokenCount := by
  rw [compactNumericVerifierStepFailureEnvironment_eq_vecAppend,
    Matrix.vecAppend_eq_ite]
  dsimp only
  split_ifs with hleft
  · have hheader := compactNumericVerifierStepStateHeaderEnvironment_size_le
      htable hcurrent hnext ⟨coordinate, hleft⟩
    exact hheader.trans (by
      unfold compactNumericVerifierStepArgumentsCoordinateSizeBound
      omega)
  · have htail := natSize_coordinate_le_finSum
      (compactNumericVerifierStepFailureTailEnvironment arguments)
      ⟨coordinate - 45, by omega⟩
    exact htail.trans (by
      unfold compactNumericVerifierStepArgumentsCoordinateSizeBound
      unfold compactNumericVerifierStepArgumentsEnvironmentConstant
      omega)

theorem compactNumericVerifierStepUnusedFailureEnvironment_size_le
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (htable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount)
    (hcurrent : CompactNumericVerifierStateCoreCoordinateSizeBounds
      currentCoordinates currentSizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount))
    (hnext : CompactNumericVerifierStateCoreCoordinateSizeBounds
      nextCoordinates nextSizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount))
    (coordinate : Fin 81) :
    Nat.size (compactNumericVerifierStepFailureEnvironment
      compactNumericVerifierStepUnusedArguments
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness coordinate) <=
        compactNumericVerifierStepUnusedCoordinateSizeBound
          stateWidth stateTokenCount := by
  exact compactNumericVerifierStepFailureEnvironment_size_le
    compactNumericVerifierStepUnusedArguments
    htable hcurrent hnext coordinate

theorem compactNumericVerifierStepEnvironment_size_le
    (arguments : CompactNumericVerifierStepArguments)
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (htable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount)
    (hcurrent : CompactNumericVerifierStateCoreCoordinateSizeBounds
      currentCoordinates currentSizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount))
    (hnext : CompactNumericVerifierStateCoreCoordinateSizeBounds
      nextCoordinates nextSizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount))
    (coordinate : Fin 429) :
    Nat.size (arguments.environment
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness coordinate) <=
        compactNumericVerifierStepArgumentsCoordinateSizeBound arguments
          stateWidth stateTokenCount := by
  rw [compactNumericVerifierStepEnvironment_eq_vecAppend,
    Matrix.vecAppend_eq_ite]
  dsimp only
  split_ifs with hleft
  · exact compactNumericVerifierStepFailureEnvironment_size_le
      arguments htable hcurrent hnext ⟨coordinate, hleft⟩
  · have htail := natSize_coordinate_le_finSum
      (compactNumericVerifierStepTailEnvironment arguments)
      ⟨coordinate - 81, by omega⟩
    exact htail.trans (by
      unfold compactNumericVerifierStepArgumentsCoordinateSizeBound
      unfold compactNumericVerifierStepArgumentsEnvironmentConstant
      omega)

/-- In the halted and finish branches every non-state argument is the canonical
zero value.  Consequently all 429 entries of the actual formula environment are
controlled by the two canonical state packages and the common table header. -/
theorem compactNumericVerifierStepUnusedEnvironment_size_le
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (htable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount)
    (hcurrent : CompactNumericVerifierStateCoreCoordinateSizeBounds
      currentCoordinates currentSizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount))
    (hnext : CompactNumericVerifierStateCoreCoordinateSizeBounds
      nextCoordinates nextSizeWitness
      (compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount))
    (coordinate : Fin 429) :
    Nat.size (compactNumericVerifierStepUnusedArguments.environment
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness coordinate) <=
        compactNumericVerifierStepUnusedCoordinateSizeBound
          stateWidth stateTokenCount := by
  exact compactNumericVerifierStepEnvironment_size_le
    compactNumericVerifierStepUnusedArguments
    htable hcurrent hnext coordinate

/-- Any real canonical step graph whose two endpoint states retain their
canonical core packages yields the actual 429-coordinate formula witness with
the argument-sensitive coordinate bound. -/
theorem exists_compactNumericVerifierStepFormulaWitness_with_sizeBound
    (arguments : CompactNumericVerifierStepArguments)
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    {currentState nextState : CompactNumericVerifierState}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (htable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount)
    (hcurrentPackage : CompactNumericVerifierStateCanonicalCorePackage
      stateTable stateWidth stateTokenCount currentStart currentFinish
      currentState currentCoordinates currentSizeWitness)
    (hnextPackage : CompactNumericVerifierStateCanonicalCorePackage
      stateTable stateWidth stateTokenCount nextStart nextFinish
      nextState nextCoordinates nextSizeWitness)
    (hgraph : arguments.Graph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness) :
    exists witness : CompactNumericVerifierStepFormulaWitness
        stateTable stateWidth stateTokenCount
        currentStart currentFinish nextStart nextFinish,
      forall coordinate : Fin 429,
        Nat.size (witness.environment coordinate) <=
          compactNumericVerifierStepArgumentsCoordinateSizeBound arguments
            stateWidth stateTokenCount := by
  let witness := arguments.toFormulaWitness
    hcurrentPackage.1 hcurrentPackage.2.1
    hnextPackage.1 hnextPackage.2.1 hgraph
  refine ⟨witness, ?_⟩
  intro coordinate
  change Nat.size (arguments.environment
    stateTable stateWidth stateTokenCount
    currentCoordinates nextCoordinates
    currentSizeWitness nextSizeWitness coordinate) <=
      compactNumericVerifierStepArgumentsCoordinateSizeBound arguments
        stateWidth stateTokenCount
  exact compactNumericVerifierStepEnvironment_size_le arguments
    htable
      (CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
        hcurrentPackage)
      (CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
        hnextPackage)
      coordinate

theorem exists_compactNumericVerifierStepFormulaWitness_of_unusedArguments
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    {currentState nextState : CompactNumericVerifierState}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (htable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount)
    (hcurrentPackage : CompactNumericVerifierStateCanonicalCorePackage
      stateTable stateWidth stateTokenCount currentStart currentFinish
      currentState currentCoordinates currentSizeWitness)
    (hnextPackage : CompactNumericVerifierStateCanonicalCorePackage
      stateTable stateWidth stateTokenCount nextStart nextFinish
      nextState nextCoordinates nextSizeWitness)
    (hgraph : compactNumericVerifierStepUnusedArguments.Graph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness) :
    exists witness : CompactNumericVerifierStepFormulaWitness
        stateTable stateWidth stateTokenCount
        currentStart currentFinish nextStart nextFinish,
      forall coordinate : Fin 429,
        Nat.size (witness.environment coordinate) <=
          compactNumericVerifierStepUnusedCoordinateSizeBound
            stateWidth stateTokenCount := by
  exact exists_compactNumericVerifierStepFormulaWitness_with_sizeBound
    compactNumericVerifierStepUnusedArguments
    htable hcurrentPackage hnextPackage hgraph

/-- A retained parse witness gives a real formula witness and a quantitative
bound without reconstructing either endpoint package from an existential
formula realization. -/
theorem exists_compactNumericVerifierParseStepFormulaWitness_with_sizeBound
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    (w : CompactNumericVerifierParseStateGraphWitness
      stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish)
    (htable : Nat.size stateTable <=
      compactNumericVerifierStateCoreCoordinateSizeBound
        stateWidth stateTokenCount) :
    exists witness : CompactNumericVerifierStepFormulaWitness
        stateTable stateWidth stateTokenCount
        currentStart currentFinish nextStart nextFinish,
      forall coordinate : Fin 429,
        Nat.size (witness.environment coordinate) <=
          compactNumericVerifierStepArgumentsCoordinateSizeBound
            (CompactNumericVerifierStepArguments.ofParseWitness w)
            stateWidth stateTokenCount := by
  rcases w.currentPackage with ⟨currentState, hcurrentPackage⟩
  rcases w.nextPackage with ⟨nextState, hnextPackage⟩
  let arguments := CompactNumericVerifierStepArguments.ofParseWitness w
  have hgraph : arguments.Graph
      stateTable stateWidth stateTokenCount
      w.currentCoordinates w.nextCoordinates
      w.currentSizeWitness w.nextSizeWitness := by
    dsimp only [CompactNumericVerifierStepArguments.Graph, arguments,
      CompactNumericVerifierStepArguments.ofParseWitness]
    exact Or.inr (Or.inr (Or.inl w.graph))
  exact exists_compactNumericVerifierStepFormulaWitness_with_sizeBound
    arguments htable hcurrentPackage hnextPackage hgraph

/-- A concrete canonical combine graph retains the two endpoint state packages
and therefore produces the real 429-coordinate formula witness with the exact
combine-argument coordinate budget. -/
theorem exists_compactNumericVerifierCombineStepFormulaWitness_with_sizeBound
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat)
    (hcanonical : CompactNumericVerifierCanonicalCombineGraph
      proofTokens certificateTokens task tasks source target
      nextStatus backTokens) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    exists taskCoordinates :
        FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskRowCoordinates,
      exists taskSizeWitness :
        FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskSizeWitness,
      exists ruleWitness :
        FoundationCompactNumericListedDirectVerifierCombineBranchRows.CompactNumericVerifierCombineRuleWitness,
      exists witness : CompactNumericVerifierStepFormulaWitness
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentTokens.length
          (currentTokens.length + nextTokens.length),
        forall coordinate : Fin 429,
          Nat.size (witness.environment coordinate) <=
            compactNumericVerifierStepArgumentsCoordinateSizeBound
              (CompactNumericVerifierStepArguments.ofCombine
                taskCoordinates taskSizeWitness ruleWitness)
              width tokens.length := by
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
      _hcurrentStart, _hcurrentFinish, _hnextStart, _hnextFinish,
      hcurrentPackage, hnextPackage, hcombine⟩
  let arguments := CompactNumericVerifierStepArguments.ofCombine
    taskCoordinates taskSizeWitness ruleWitness
  have hgraph : arguments.Graph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness := by
    dsimp only [CompactNumericVerifierStepArguments.Graph, arguments,
      CompactNumericVerifierStepArguments.ofCombine]
    refine Or.inr (Or.inr (Or.inr ?_))
    simpa only [
      FoundationCompactNumericListedDirectVerifierStepFormula.compactNumericVerifierStepCombineRuleWitness,
      FoundationCompactNumericListedDirectVerifierCombineBranchRows.compactNumericVerifierCombineRuleWitnessOf]
      using hcombine
  refine ⟨taskCoordinates, taskSizeWitness, ruleWitness, ?_⟩
  exact exists_compactNumericVerifierStepFormulaWitness_with_sizeBound
    arguments
    (canonicalStateTable_size_le_coordinateSizeBound tokens width)
    hcurrentPackage hnextPackage hgraph

/-- A canonical combine graph with a public pointwise rule-coordinate bound
produces the actual 429-column row under one witness-independent expression. -/
theorem exists_compactNumericVerifierBoundedCombineStepFormulaWitness_with_sizeBound
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat) (ruleCoordinateBound : Nat)
    (hcanonical : CompactNumericVerifierCanonicalCombineBoundedGraph
      proofTokens certificateTokens task tasks source target
      nextStatus backTokens ruleCoordinateBound) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    exists taskCoordinates :
        FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskRowCoordinates,
      exists taskSizeWitness :
        FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskSizeWitness,
      exists ruleWitness :
        FoundationCompactNumericListedDirectVerifierCombineBranchRows.CompactNumericVerifierCombineRuleWitness,
      exists witness : CompactNumericVerifierStepFormulaWitness
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentTokens.length
          (currentTokens.length + nextTokens.length),
        forall coordinate : Fin 429,
          Nat.size (witness.environment coordinate) <=
            compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
              width tokens.length ruleCoordinateBound := by
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  dsimp only [CompactNumericVerifierCanonicalCombineBoundedGraph] at hcanonical
  rcases hcanonical with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, ruleWitness,
      _hcurrentStart, _hcurrentFinish, _hnextStart, _hnextFinish,
      hcurrentPackage, hnextPackage, hcombine, hrule⟩
  let arguments := CompactNumericVerifierStepArguments.ofCombine
    taskCoordinates taskSizeWitness ruleWitness
  have hgraph : arguments.Graph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness := by
    dsimp only [CompactNumericVerifierStepArguments.Graph, arguments,
      CompactNumericVerifierStepArguments.ofCombine]
    refine Or.inr (Or.inr (Or.inr ?_))
    simpa only [
      FoundationCompactNumericListedDirectVerifierStepFormula.compactNumericVerifierStepCombineRuleWitness,
      FoundationCompactNumericListedDirectVerifierCombineBranchRows.compactNumericVerifierCombineRuleWitnessOf]
      using hcombine
  have hstateBounds :=
    CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
      hcurrentPackage
  let stateBound :=
    compactNumericVerifierStateCoreCoordinateSizeBound width tokens.length
  let commonBound := stateBound + ruleCoordinateBound
  have hstateValueBound : Nat.size currentSizeWitness.taskValueBound ≤
      stateBound := by
    simpa only [stateBound, width, tokens, currentTokens, nextTokens,
      currentState, nextState] using hstateBounds.taskValueBound
  have hvalueBound : Nat.size currentSizeWitness.taskValueBound ≤
      commonBound := by
    exact hstateValueBound.trans (by
      dsimp only [commonBound, stateBound]
      omega)
  have hruleCommon : ∀ coordinate : Fin 34,
      Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
        ruleWitness coordinate) ≤ commonBound := by
    intro coordinate
    exact (hrule coordinate).trans (by
      dsimp only [commonBound, stateBound]
      omega)
  have hconstant :
      compactNumericVerifierStepArgumentsEnvironmentConstant arguments ≤
        384 * commonBound := by
    exact compactNumericVerifierStepArgumentsEnvironmentConstant_ofCombine_le
      taskCoordinates taskSizeWitness ruleWitness
      hcombine.2.2.1 hvalueBound hruleCommon
  rcases exists_compactNumericVerifierStepFormulaWitness_with_sizeBound
      arguments
      (canonicalStateTable_size_le_coordinateSizeBound tokens width)
      hcurrentPackage hnextPackage hgraph with
    ⟨stepWitness, hstepWitness⟩
  refine ⟨taskCoordinates, taskSizeWitness, ruleWitness, stepWitness, ?_⟩
  intro coordinate
  have hraw := hstepWitness coordinate
  have htotal :
      compactNumericVerifierStepArgumentsCoordinateSizeBound
          arguments width tokens.length ≤
        compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
          width tokens.length ruleCoordinateBound := by
    dsimp only [compactNumericVerifierStepArgumentsCoordinateSizeBound,
      compactNumericVerifierCanonicalCombineStepCoordinateSizeBound,
      stateBound, commonBound]
    exact Nat.add_le_add_left hconstant _
  exact hraw.trans htotal

/-- Every executable combine step chooses its concrete auxiliary suffix and
rule-coordinate budget internally, then realizes the actual 429-column row
under the corresponding public canonical expression. -/
theorem exists_compactNumericVerifierPublicCombineStepFormulaWitness_with_sizeBound
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult)
    (htaskNe : task.1 ≠ 10) :
    ∃ target nextStatus backTokens ruleCoordinateBound,
      compactNumericCombineState task
          ((proofTokens, certificateTokens), (tasks, source)) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus) ∧
      let currentState : CompactNumericVerifierState :=
        (((proofTokens, certificateTokens), (task :: tasks, source)), none)
      let nextState : CompactNumericVerifierState :=
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
      let currentTokens := compactAdditiveEncode currentState
      let nextTokens := compactAdditiveEncode nextState
      let tokens := currentTokens ++ nextTokens ++ backTokens
      let width := (compactBinaryNatPayloadBits tokens).length
      ∃ witness : CompactNumericVerifierStepFormulaWitness
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentTokens.length
          (currentTokens.length + nextTokens.length),
        ∀ coordinate : Fin 429,
          Nat.size (witness.environment coordinate) ≤
            compactNumericVerifierCanonicalCombineStepCoordinateSizeBound
              width tokens.length ruleCoordinateBound := by
  rcases
      CompactNumericVerifierCanonicalCombineBoundedStateGraph.exists_of_public_step
        proofTokens certificateTokens task tasks source htaskNe with
    ⟨target, nextStatus, backTokens, ruleCoordinateBound,
      htransition, hcanonical⟩
  refine ⟨target, nextStatus, backTokens, ruleCoordinateBound,
    htransition, ?_⟩
  have hstep :=
    exists_compactNumericVerifierBoundedCombineStepFormulaWitness_with_sizeBound
      proofTokens certificateTokens task tasks source target nextStatus
        backTokens ruleCoordinateBound hcanonical
  dsimp only at hstep ⊢
  rcases hstep with
    ⟨_taskCoordinates, _taskSizeWitness, _ruleWitness,
      witness, hwitness⟩
  exact ⟨witness, hwitness⟩

theorem exists_compactNumericVerifierHaltedStepFormulaWitness_with_sizeBound
    (proofTokens certificateTokens : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult)
    (result : Bool) :
    let state : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, values)), some result)
    let stateTokens := compactAdditiveEncode state
    let tokens := stateTokens ++ stateTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    exists witness : CompactNumericVerifierStepFormulaWitness
        (compactFixedWidthTableCode width tokens) width tokens.length
        0 stateTokens.length stateTokens.length
        (stateTokens.length + stateTokens.length),
      forall coordinate : Fin 429,
        Nat.size (witness.environment coordinate) <=
          compactNumericVerifierStepUnusedCoordinateSizeBound
            width tokens.length := by
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
      _hcurrentStart, _hcurrentFinish, _hnextStart, _hnextFinish,
      hcurrentPackage, hnextPackage, hhalted⟩
  have hgraph : compactNumericVerifierStepUnusedArguments.Graph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness := by
    exact Or.inl ⟨hcurrentPackage.core, hnextPackage.core, hhalted⟩
  exact exists_compactNumericVerifierStepFormulaWitness_of_unusedArguments
    (canonicalStateTable_size_le_coordinateSizeBound tokens width)
    hcurrentPackage hnextPackage hgraph

theorem exists_compactNumericVerifierFinishStepFormulaWitness_with_sizeBound
    (proofTokens certificateTokens : List Nat)
    (values : List
      FoundationCompactNumericListedRuleChecks.CompactNumericChildResult) :
    let payload : CompactNumericRunningPayload :=
      ((proofTokens, certificateTokens), ([], values))
    let currentState : CompactNumericVerifierState := (payload, none)
    let nextState := compactNumericFinishState payload
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    exists witness : CompactNumericVerifierStepFormulaWitness
        (compactFixedWidthTableCode width tokens) width tokens.length
        0 currentTokens.length currentTokens.length
        (currentTokens.length + nextTokens.length),
      forall coordinate : Fin 429,
        Nat.size (witness.environment coordinate) <=
          compactNumericVerifierStepUnusedCoordinateSizeBound
            width tokens.length := by
  let payload : CompactNumericRunningPayload :=
    ((proofTokens, certificateTokens), ([], values))
  let currentState : CompactNumericVerifierState := (payload, none)
  let nextState := compactNumericFinishState payload
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  have hcanonical := CompactNumericVerifierCanonicalFinishGraph.exists
    proofTokens certificateTokens values
  dsimp only [CompactNumericVerifierCanonicalFinishGraph] at hcanonical
  rcases hcanonical with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      _hcurrentStart, _hcurrentFinish, _hnextStart, _hnextFinish,
      hcurrentPackage, hnextPackage, hfinish⟩
  have hgraph : compactNumericVerifierStepUnusedArguments.Graph
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness := by
    exact Or.inr (Or.inl
      ⟨hcurrentPackage.core, hnextPackage.core, hfinish⟩)
  exact exists_compactNumericVerifierStepFormulaWitness_of_unusedArguments
    (canonicalStateTable_size_le_coordinateSizeBound tokens width)
    hcurrentPackage hnextPackage hgraph

#print axioms compactAdditiveNatListSlice_coordinates_le
#print axioms compactAdditiveStructuredListLayout_coordinates_le
#print axioms compactAdditiveOptionLayout_coordinates_le
#print axioms
  CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
#print axioms canonicalStateTable_size_le_coordinateSizeBound
#print axioms compactNumericVerifierTaskCoordinateEnvironment_size_le
#print axioms compactNumericVerifierStepEnvironment_eq_vecAppend
#print axioms compactNumericVerifierStepFailureNonTaskEnvironment_ofCombine_eq
#print axioms compactNumericVerifierStepTailEnvironment_ofCombine_eq
#print axioms compactNumericVerifierStepFailureTailEnvironment_eq_vecAppend
#print axioms compactNumericVerifierStepFailureEnvironment_eq_vecAppend
#print axioms natSize_coordinate_le_finSum
#print axioms natSize_vecAppend_le
#print axioms compactNumericVerifierStepFailureTailEnvironment_size_le
#print axioms compactNumericVerifierStepArgumentsEnvironmentConstant_le
#print axioms
  compactNumericVerifierStepArgumentsEnvironmentConstant_ofCombine_le
#print axioms compactNumericVerifierStateCoreCoordinateEnvironment_size_le
#print axioms compactNumericVerifierStepStateHeaderEnvironment_size_le
#print axioms compactNumericVerifierStepFailureEnvironment_size_le
#print axioms compactNumericVerifierStepUnusedFailureEnvironment_size_le
#print axioms compactNumericVerifierStepEnvironment_size_le
#print axioms compactNumericVerifierStepUnusedEnvironment_size_le
#print axioms
  exists_compactNumericVerifierStepFormulaWitness_with_sizeBound
#print axioms
  exists_compactNumericVerifierStepFormulaWitness_of_unusedArguments
#print axioms
  exists_compactNumericVerifierParseStepFormulaWitness_with_sizeBound
#print axioms
  exists_compactNumericVerifierCombineStepFormulaWitness_with_sizeBound
#print axioms
  exists_compactNumericVerifierBoundedCombineStepFormulaWitness_with_sizeBound
#print axioms
  exists_compactNumericVerifierPublicCombineStepFormulaWitness_with_sizeBound
#print axioms
  exists_compactNumericVerifierHaltedStepFormulaWitness_with_sizeBound
#print axioms
  exists_compactNumericVerifierFinishStepFormulaWitness_with_sizeBound

end FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
