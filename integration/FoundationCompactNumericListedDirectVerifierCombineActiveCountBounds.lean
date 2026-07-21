import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraph
import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
import integration.FoundationCompactNumericListedDirectVerifierStepCoordinateBounds

/-!
# Numeric loop controls for an active verifier combine branch

The rule witness contains coordinates for every combine branch.  Coordinates
unused by the selected disjunct need only have short binary representations;
they are not numerical loop bounds.  This file bounds exactly the counts used
by the active branch, together with the four counts exposed by the task head.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineActiveCountBounds

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectFormulaShiftExactListRows
open FoundationCompactNumericListedDirectFormulaShiftListRow
open FoundationCompactNumericListedDirectFormulaTransformTotalOutcomeFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalTraceFormula
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectChildResultBoundedHeadEquality
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineSuccessRows
open FoundationCompactNumericListedDirectVerifierCombineFailureRows
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepCoordinateBounds
open FoundationCompactNumericListedDirectVerifierCombineCanonicalGraph
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectArithmeticPrimitives

/-- One public bound for every numerical loop count in a combine row. -/
def compactNumericVerifierCombineActiveCountLimit (tokenCount : Nat) : Nat :=
  tokenCount + 16 * (tokenCount + 1) * (tokenCount + 1) + 9

theorem le_compactNumericVerifierCombineActiveCountLimit
    {value tokenCount : Nat} (hvalue : value <= tokenCount) :
    value <= compactNumericVerifierCombineActiveCountLimit tokenCount := by
  unfold compactNumericVerifierCombineActiveCountLimit
  omega

/-- The exact formula-transform trace has its advertised quadratic length. -/
theorem CompactFormulaTransformTotalExactBoundedGraph.stateCount_le_activeLimit
    {tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound : Nat}
    (hinputCount : inputCount <= tokenCount)
    (hgraph : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      emptyBoundary binderArity tableWidth valueBound) :
    stateCount <= compactNumericVerifierCombineActiveCountLimit tokenCount := by
  have hstep : inputCount + 1 <= tokenCount + 1 := by omega
  have hquadratic :
      16 * (inputCount + 1) * (inputCount + 1) <=
        16 * (tokenCount + 1) * (tokenCount + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 16 hstep) hstep
  have hcount :
      stateCount = 16 * (inputCount + 1) * (inputCount + 1) + 8 + 1 := by
    exact hgraph.1
  rw [hcount]
  unfold compactNumericVerifierCombineActiveCountLimit
  omega

/-- A genuine list-shift row cannot expose a source formula longer than the
common token stream containing that formula. -/
theorem CompactFormulaShiftListRow.sourceInnerCount_le_tokenCount
    {tokenTable width tokenCount sourceBoundary candidateBoundary successTable
      formulaCount index emptyStart emptyFinish emptyBoundary sourceStart
      sourceFinish sourceInnerCount sourceInnerBoundary sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize stateBoundary stateCount
      tableWidth valueBound successValue : Nat}
    {finalCoordinates :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateRowCoordinates}
    {finalSizeWitness :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateCoreSizeWitness}
    (hrow : CompactFormulaShiftListRow
      tokenTable width tokenCount sourceBoundary candidateBoundary successTable
      formulaCount index emptyStart emptyFinish emptyBoundary sourceStart
      sourceFinish sourceInnerCount sourceInnerBoundary sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize stateBoundary stateCount
      tableWidth valueBound successValue finalCoordinates finalSizeWitness) :
    sourceInnerCount <= tokenCount := by
  rcases hrow with
    ⟨_hindex, _hsourceStart, _hsourceFinish, hsource,
      _hcandidateStart, _hcandidateFinish, _hcandidate, _hsuccess, _houtcome⟩
  exact structuredListLayout_count_le_tokenCount hsource.1

/-- The defaulted shifted candidate is encoded in the same token stream, so
its formula length is bounded by the same token count. -/
theorem CompactFormulaShiftListRow.candidateInnerCount_le_tokenCount
    {tokenTable width tokenCount sourceBoundary candidateBoundary successTable
      formulaCount index emptyStart emptyFinish emptyBoundary sourceStart
      sourceFinish sourceInnerCount sourceInnerBoundary sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize stateBoundary stateCount
      tableWidth valueBound successValue : Nat}
    {finalCoordinates :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateRowCoordinates}
    {finalSizeWitness :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateCoreSizeWitness}
    (hrow : CompactFormulaShiftListRow
      tokenTable width tokenCount sourceBoundary candidateBoundary successTable
      formulaCount index emptyStart emptyFinish emptyBoundary sourceStart
      sourceFinish sourceInnerCount sourceInnerBoundary sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize stateBoundary stateCount
      tableWidth valueBound successValue finalCoordinates finalSizeWitness) :
    candidateInnerCount <= tokenCount := by
  rcases hrow with
    ⟨_hindex, _hsourceStart, _hsourceFinish, _hsource,
      _hcandidateStart, _hcandidateFinish, hcandidate, _hsuccess, _houtcome⟩
  exact structuredListLayout_count_le_tokenCount hcandidate.1

/-- Every per-formula shift trace has the same fixed quadratic execution
bound; the exponential `valueBound` is not used as a row-count bound. -/
theorem CompactFormulaShiftListRow.stateCount_le_activeLimit
    {tokenTable width tokenCount sourceBoundary candidateBoundary successTable
      formulaCount index emptyStart emptyFinish emptyBoundary sourceStart
      sourceFinish sourceInnerCount sourceInnerBoundary sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize stateBoundary stateCount
      tableWidth valueBound successValue : Nat}
    {finalCoordinates :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateRowCoordinates}
    {finalSizeWitness :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateCoreSizeWitness}
    (hrow : CompactFormulaShiftListRow
      tokenTable width tokenCount sourceBoundary candidateBoundary successTable
      formulaCount index emptyStart emptyFinish emptyBoundary sourceStart
      sourceFinish sourceInnerCount sourceInnerBoundary sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize stateBoundary stateCount
      tableWidth valueBound successValue finalCoordinates finalSizeWitness) :
    stateCount <= compactNumericVerifierCombineActiveCountLimit tokenCount := by
  rcases hrow with
    ⟨_hindex, _hsourceStart, _hsourceFinish, hsource,
      _hcandidateStart, _hcandidateFinish, _hcandidate, _hsuccess, houtcome⟩
  exact CompactFormulaTransformTotalExactBoundedGraph.stateCount_le_activeLimit
    (structuredListLayout_count_le_tokenCount hsource.1) houtcome.1

/-- The three list lengths stored in one formula-transform state are genuine
token-table list counts, hence are numerically bounded by `tokenCount`. -/
structure CompactFormulaTransformStateCoreCountControls
    (tokenCount : Nat)
    (coordinates :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateRowCoordinates) :
    Prop where
  parserTokensCount_le : coordinates.parserTokensCount <= tokenCount
  parserTasksCount_le : coordinates.parserTasksCount <= tokenCount
  outputCount_le : coordinates.outputCount <= tokenCount

theorem CompactFormulaTransformStateCoreGraph.countControls
    {tokenTable width tokenCount : Nat}
    {coordinates :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateRowCoordinates}
    {sizeWitness :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateCoreSizeWitness}
    (hcore :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateCoreGraph
        tokenTable width tokenCount coordinates sizeWitness) :
    CompactFormulaTransformStateCoreCountControls tokenCount coordinates := by
  rcases hcore with
    ⟨_outerSplit, hparser, houtput, _houtputRows, _houtputSizeEq,
      _houtputSize⟩
  rcases hparser with
    ⟨_parserSplit, htokens, _htokenRows, _htaskSplit, htasks,
      _htaskRows, _htokenSizeEq, _htokenSize, _htaskSizeEq, _htaskSize⟩
  exact
    { parserTokensCount_le :=
        structuredListLayout_count_le_tokenCount htokens
      parserTasksCount_le :=
        structuredListLayout_count_le_tokenCount htasks
      outputCount_le :=
        structuredListLayout_count_le_tokenCount houtput }

theorem CompactFormulaTransformStateAtRows.countControls
    {tokenTable width tokenCount stateBoundary stateCount index : Nat}
    {coordinates :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateRowCoordinates}
    {sizeWitness :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateCoreSizeWitness}
    (hrow :
      FoundationCompactNumericListedDirectFormulaTransformStateAtRows.CompactFormulaTransformStateAtRows
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness) :
    CompactFormulaTransformStateCoreCountControls tokenCount coordinates :=
  CompactFormulaTransformStateCoreGraph.countControls hrow.2.2.2

/-- Once the bounded existential coordinates of an adjacent transform step
are instantiated, both actual state rows retain the same three count bounds. -/
theorem CompactFormulaTransformAdjacentStepWitnessBounded.countControls
    {tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount valueBound : Nat}
    {currentCoordinates nextCoordinates :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateRowCoordinates}
    {currentSize nextSize :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateCoreSizeWitness}
    (hbounded :
      FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula.CompactFormulaTransformAdjacentStepWitnessBounded
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize) :
    CompactFormulaTransformStateCoreCountControls
        tokenCount currentCoordinates /\
      CompactFormulaTransformStateCoreCountControls
        tokenCount nextCoordinates := by
  rcases hbounded with
    ⟨_slot0, _hslot0, _slot1, _hslot1, _slot2, _hslot2,
      _slot3, _hslot3, _slot4, _hslot4, _slot5, _hslot5,
      _slot6, _hslot6, _consumedCount, _hconsumedCount,
      _mappedHead, _hmappedHead, hrow, _hcurrentStatus, _hnextStatus⟩
  exact
    ⟨CompactFormulaTransformStateAtRows.countControls hrow.1,
      CompactFormulaTransformStateAtRows.countControls hrow.2.1⟩

theorem CompactFormulaShiftListRow.finalStateCountControls
    {tokenTable width tokenCount sourceBoundary candidateBoundary successTable
      formulaCount index emptyStart emptyFinish emptyBoundary sourceStart
      sourceFinish sourceInnerCount sourceInnerBoundary sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize stateBoundary stateCount
      tableWidth valueBound successValue : Nat}
    {finalCoordinates :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateRowCoordinates}
    {finalSizeWitness :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateCoreSizeWitness}
    (hrow : CompactFormulaShiftListRow
      tokenTable width tokenCount sourceBoundary candidateBoundary successTable
      formulaCount index emptyStart emptyFinish emptyBoundary sourceStart
      sourceFinish sourceInnerCount sourceInnerBoundary sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize stateBoundary stateCount
      tableWidth valueBound successValue finalCoordinates finalSizeWitness) :
    CompactFormulaTransformStateCoreCountControls
      tokenCount finalCoordinates := by
  rcases hrow with
    ⟨_hindex, _hsourceStart, _hsourceFinish, _hsource,
      _hcandidateStart, _hcandidateFinish, _hcandidate, _hsuccess, houtcome⟩
  exact CompactFormulaTransformStateAtRows.countControls houtcome.2.1

/-- Formula-coordinate form of the per-row execution controls.  This is the
bridge used after the 29 bounded witnesses of the Sigma-zero row formula have
been instantiated. -/
structure CompactFormulaShiftListRowExecutionCountControls
    (environment : Fin 40 -> Nat) : Prop where
  sourceInnerCount_le : environment 13 <= environment 2
  candidateInnerCount_le : environment 18 <= environment 2
  stateCount_le : environment 22 <=
    compactNumericVerifierCombineActiveCountLimit (environment 2)
  finalParserTokensCount_le : environment 32 <= environment 2
  finalParserTasksCount_le : environment 34 <= environment 2
  finalOutputCount_le : environment 36 <= environment 2

theorem compactFormulaShiftListRowDef_executionCountControls
    (environment : Fin 40 -> Nat)
    (hrow : compactFormulaShiftListRowDef.val.Evalb environment) :
    CompactFormulaShiftListRowExecutionCountControls environment := by
  have hsemantic := (compactFormulaShiftListRowDef_eval environment).mp hrow
  have hfinal :=
    CompactFormulaShiftListRow.finalStateCountControls hsemantic
  exact
    { sourceInnerCount_le :=
        CompactFormulaShiftListRow.sourceInnerCount_le_tokenCount hsemantic
      candidateInnerCount_le :=
        CompactFormulaShiftListRow.candidateInnerCount_le_tokenCount hsemantic
      stateCount_le :=
        CompactFormulaShiftListRow.stateCount_le_activeLimit hsemantic
      finalParserTokensCount_le := hfinal.parserTokensCount_le
      finalParserTasksCount_le := hfinal.parserTasksCount_le
      finalOutputCount_le := hfinal.outputCount_le }

/-- The original bounded witnesses of an exact list shift determine one and
the same 40-coordinate row environment carrying the execution controls. -/
theorem CompactFormulaShiftExactListRows.exists_rowEnvironment_with_countControls
    {tokenTable width tokenCount sourceBoundary formulaCount candidateBoundary
      successTable expectedBoundary expectedCount emptyStart emptyFinish
      emptyBoundary emptyBoundarySize witnessBound : Nat}
    (hrows : CompactFormulaShiftExactListRows
      tokenTable width tokenCount sourceBoundary formulaCount candidateBoundary
      successTable expectedBoundary expectedCount emptyStart emptyFinish
      emptyBoundary emptyBoundarySize witnessBound)
    {index : Nat} (hindex : index < formulaCount) :
    ∃ environment : Fin 40 -> Nat,
      environment 0 = tokenTable /\
      environment 1 = width /\
      environment 2 = tokenCount /\
      environment 3 = sourceBoundary /\
      environment 4 = candidateBoundary /\
      environment 5 = successTable /\
      environment 6 = formulaCount /\
      environment 7 = index /\
      environment 8 = emptyStart /\
      environment 9 = emptyFinish /\
      environment 10 = emptyBoundary /\
      compactFormulaShiftListRowDef.val.Evalb environment /\
      CompactFormulaShiftListRowExecutionCountControls environment := by
  rcases hrows.2.1 index hindex with
    ⟨sourceStart, _hsourceStart, sourceFinish, _hsourceFinish,
      sourceInnerCount, _hsourceInnerCount,
      sourceInnerBoundary, _hsourceInnerBoundary,
      sourceBoundarySize, _hsourceBoundarySize,
      candidateStart, _hcandidateStart, candidateFinish, _hcandidateFinish,
      candidateInnerCount, _hcandidateInnerCount,
      candidateInnerBoundary, _hcandidateInnerBoundary,
      candidateBoundarySize, _hcandidateBoundarySize,
      stateBoundary, _hstateBoundary, stateCount, _hstateCount,
      tableWidth, _htableWidth, valueBound, _hvalueBound,
      successValue, _hsuccessValue, finalStart, _hfinalStart,
      finalFinish, _hfinalFinish, finalParserFinish, _hfinalParserFinish,
      finalParserTokensFinish, _hfinalParserTokensFinish,
      finalParserTasksFinish, _hfinalParserTasksFinish,
      finalParserTokensBoundary, _hfinalParserTokensBoundary,
      finalParserTokensCount, _hfinalParserTokensCount,
      finalParserTasksBoundary, _hfinalParserTasksBoundary,
      finalParserTasksCount, _hfinalParserTasksCount,
      finalOutputBoundary, _hfinalOutputBoundary,
      finalOutputCount, _hfinalOutputCount,
      finalParserTokensBoundarySize, _hfinalParserTokensBoundarySize,
      finalParserTasksBoundarySize, _hfinalParserTasksBoundarySize,
      finalOutputBoundarySize, _hfinalOutputBoundarySize, hrow⟩
  let finalCoordinates :=
    FoundationCompactNumericListedDirectFormulaTransformStateFormula.compactFormulaTransformStateRowCoordinatesOf
      finalStart finalFinish finalParserFinish finalParserTokensFinish
      finalParserTasksFinish finalParserTokensBoundary finalParserTokensCount
      finalParserTasksBoundary finalParserTasksCount finalOutputBoundary
      finalOutputCount
  let finalSizeWitness :
      FoundationCompactNumericListedDirectFormulaTransformStateFormula.CompactFormulaTransformStateCoreSizeWitness :=
    { parserTokensBoundarySize := finalParserTokensBoundarySize
      parserTasksBoundarySize := finalParserTasksBoundarySize
      outputBoundarySize := finalOutputBoundarySize }
  let environment := compactFormulaShiftListRowEnvironment
    tokenTable width tokenCount sourceBoundary candidateBoundary successTable
    formulaCount index emptyStart emptyFinish emptyBoundary sourceStart
    sourceFinish sourceInnerCount sourceInnerBoundary sourceBoundarySize
    candidateStart candidateFinish candidateInnerCount candidateInnerBoundary
    candidateBoundarySize stateBoundary stateCount tableWidth valueBound
    successValue finalCoordinates finalSizeWitness
  have heval : compactFormulaShiftListRowDef.val.Evalb environment := by
    dsimp only [environment]
    exact (compactFormulaShiftListRowDef_spec
      tokenTable width tokenCount sourceBoundary candidateBoundary successTable
      formulaCount index emptyStart emptyFinish emptyBoundary sourceStart
      sourceFinish sourceInnerCount sourceInnerBoundary sourceBoundarySize
      candidateStart candidateFinish candidateInnerCount
      candidateInnerBoundary candidateBoundarySize stateBoundary stateCount
      tableWidth valueBound successValue finalCoordinates finalSizeWitness).mpr
        hrow
  refine ⟨environment, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    heval, compactFormulaShiftListRowDef_executionCountControls environment
      heval⟩ <;>
    rfl

/-- The output list of the total list-shift is either the candidate list or
the empty default, hence never longer than the source formula list. -/
theorem CompactFormulaShiftExactListRows.expectedCount_le_formulaCount
    {tokenTable width tokenCount sourceBoundary formulaCount candidateBoundary
      successTable expectedBoundary expectedCount emptyStart emptyFinish
      emptyBoundary emptyBoundarySize witnessBound : Nat}
    (hrows : CompactFormulaShiftExactListRows
      tokenTable width tokenCount sourceBoundary formulaCount candidateBoundary
      successTable expectedBoundary expectedCount emptyStart emptyFinish
      emptyBoundary emptyBoundarySize witnessBound) :
    expectedCount <= formulaCount := by
  rcases hrows.2.2 with hsuccess | hfailure
  · rw [hsuccess.2.1]
  · rw [hfailure.2]
    exact Nat.zero_le _

/-- A child-result head exposes the same context count as its checked core. -/
theorem CompactNumericChildResultBoundedHeadEq.expectedGammaCount_le_tokenCount
    {tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool : Nat}
    (hhead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound targetIndex expectedBool) :
    expectedGammaCount <= tokenCount := by
  rcases hhead with
    ⟨targetStart, _htargetStart, targetFinish, _htargetFinish,
      targetGammaFinish, _htargetGammaFinish,
      targetGammaCount, _htargetGammaCount,
      targetGammaBoundary, _htargetGammaBoundary,
      targetBoolValue, _htargetBoolValue,
      targetGammaBoundarySize, _htargetGammaBoundarySize,
      _hstartEntry, _hfinishEntry, hcore, hsame, _hbool⟩
  have htarget := (CompactNumericChildResultCoreGraph.bounds hcore).gammaCount_le
  have htarget' : targetGammaCount <= tokenCount := by
    simpa only [compactNumericChildResultRowCoordinatesOf] using htarget
  rw [← hsame.1]
  exact htarget'

/-- Branch-sensitive bounds.  No claim is made about coordinates ignored by
the selected disjunct. -/
def CompactNumericVerifierCombineActiveRuleCountBounds
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool : Nat)
    (witness : CompactNumericVerifierCombineRuleWitness) : Prop :=
  let limit := compactNumericVerifierCombineActiveCountLimit tokenCount
  (CompactNumericSimpleCombineSuccessRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witness.rightGammaCount witness.rightGammaBoundary
        witness.rightBoolValue
      witness.leftGammaCount witness.leftGammaBoundary witness.leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound witness.resultBoolValue nextStatusTag /\
    witness.rightGammaCount <= limit /\
    (taskTag = 3 -> witness.leftGammaCount <= limit)) \/
  (CompactNumericAllShiftCombineSuccessRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary firstFinish firstCount
      witness.rightGammaCount witness.rightGammaBoundary
        witness.rightBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      witness.formulaBoundary witness.formulaBoundarySize
      witness.freedStart witness.freedFinish witness.freedBoundary
        witness.freedCount witness.freedBoundarySize
      witness.freeStateBoundary witness.freeStateCount
      witness.shiftCandidateBoundary witness.shiftSuccessTable
      witness.shiftedBoundary witness.shiftedCount
      witness.emptyStart witness.emptyFinish witness.emptyBoundary
        witness.emptyBoundarySize
      witness.shiftWitnessBound witness.freeTableWidth witness.freeValueBound
      tableWidth valueBound witness.resultBoolValue nextStatusTag /\
    witness.rightGammaCount <= limit /\
    (taskTag = 5 ->
      witness.freedCount <= limit /\
      witness.freeStateCount <= limit /\
      witness.shiftedCount <= limit) /\
    (taskTag = 8 -> witness.shiftedCount <= limit)) \/
  (CompactNumericExsCutCombineSuccessRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      witness.rightGammaCount witness.rightGammaBoundary
        witness.rightBoolValue
      witness.leftGammaCount witness.leftGammaBoundary witness.leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      witness.formulaBoundary witness.formulaBoundarySize
      witness.transformedStart witness.transformedFinish
        witness.transformedBoundary witness.transformedCount
        witness.transformedBoundarySize
      witness.transformStateBoundary witness.transformStateCount
      witness.emptyStart witness.emptyFinish witness.emptyBoundary
        witness.emptyBoundarySize
      witness.freeTableWidth witness.freeValueBound
      tableWidth valueBound witness.resultBoolValue nextStatusTag /\
    witness.rightGammaCount <= limit /\
    witness.transformedCount <= limit /\
    witness.transformStateCount <= limit /\
    (taskTag = 9 -> witness.leftGammaCount <= limit)) \/
  CompactNumericVerifierCombineFailureRows
    tokenTable width tokenCount taskTag sourceBoundary sourceCount
      targetBoundary targetCount tableWidth valueBound
      nextStatusTag nextStatusBool

structure CompactNumericVerifierCombineCountControls
    (tokenCount : Nat)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (ruleWitness : CompactNumericVerifierCombineRuleWitness) : Prop where
  taskGammaCount_le : taskCoordinates.gammaCount <=
    compactNumericVerifierCombineActiveCountLimit tokenCount
  taskFirstCount_le : taskCoordinates.firstCount <=
    compactNumericVerifierCombineActiveCountLimit tokenCount
  taskSecondCount_le : taskCoordinates.secondCount <=
    compactNumericVerifierCombineActiveCountLimit tokenCount
  taskWitnessCount_le : taskCoordinates.witnessCount <=
    compactNumericVerifierCombineActiveCountLimit tokenCount

private theorem activeRuleCountBounds_of_branchRows
    {tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool : Nat}
    {witness : CompactNumericVerifierCombineRuleWitness}
    (hgammaCount : gammaCount <= tokenCount)
    (hfirstCount : firstCount <= tokenCount)
    (hrows : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool witness) :
    CompactNumericVerifierCombineActiveRuleCountBounds
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool witness := by
  dsimp only [CompactNumericVerifierCombineActiveRuleCountBounds]
  rcases hrows with hsimple | hallShift | hexsCut | hfailure
  · left
    have hsimpleProof := hsimple
    rcases hsimple with ⟨htransition, hstatus⟩
    rcases htransition with
      ⟨hrule, hrightRows, hrightHead, hleftHead⟩
    refine ⟨hsimpleProof, ?_, ?_⟩
    · exact le_compactNumericVerifierCombineActiveCountLimit
        (CompactNumericChildResultBoundedHeadEq.expectedGammaCount_le_tokenCount
          hrightHead)
    · intro htag
      exact le_compactNumericVerifierCombineActiveCountLimit
        (CompactNumericChildResultBoundedHeadEq.expectedGammaCount_le_tokenCount
          (hleftHead htag).2)
  · right; left
    have hallShiftProof := hallShift
    rcases hallShift with ⟨hallShiftRows, hstatus⟩
    refine ⟨hallShiftProof, ?_, ?_, ?_⟩
    · rcases hallShiftRows with hall | hshift
      · rcases hall with
          ⟨_hallTag, _hsource, _hformula, _hfreed, _hpremise,
            hhead, _hcheck, _hpush⟩
        exact le_compactNumericVerifierCombineActiveCountLimit
          (CompactNumericChildResultBoundedHeadEq.expectedGammaCount_le_tokenCount
            hhead)
      · rcases hshift with
          ⟨_hshiftTag, _hsource, _hpremise, hhead, _hcheck, _hpush⟩
        exact le_compactNumericVerifierCombineActiveCountLimit
          (CompactNumericChildResultBoundedHeadEq.expectedGammaCount_le_tokenCount
            hhead)
    · intro htag
      rcases hallShiftRows with hall | hshift
      · rcases hall with
          ⟨_hallTag, _hsource, _hformula, hfreed, _hpremise,
            _hhead, hcheck, _hpush⟩
        have hfreedCount := structuredListLayout_count_le_tokenCount hfreed.1
        have hfreeState :=
          CompactFormulaTransformTotalExactBoundedGraph.stateCount_le_activeLimit
            hfirstCount hcheck.1
        have hshiftedCount :=
          CompactFormulaShiftExactListRows.expectedCount_le_formulaCount
            hcheck.2.1
        exact
          ⟨le_compactNumericVerifierCombineActiveCountLimit hfreedCount,
            hfreeState,
            le_compactNumericVerifierCombineActiveCountLimit
              (hshiftedCount.trans hgammaCount)⟩
      · omega
    · intro htag
      rcases hallShiftRows with hall | hshift
      · omega
      · rcases hshift with
          ⟨_hshiftTag, _hsource, _hpremise, hhead, hcheck, _hpush⟩
        have hpremiseCount :=
          CompactNumericChildResultBoundedHeadEq.expectedGammaCount_le_tokenCount
            hhead
        exact le_compactNumericVerifierCombineActiveCountLimit
          ((CompactFormulaShiftExactListRows.expectedCount_le_formulaCount
            hcheck.1).trans hpremiseCount)
  · right; right; left
    have hexsCutProof := hexsCut
    rcases hexsCut with ⟨hexsCutRows, hstatus⟩
    rcases hexsCutRows with
      ⟨hformula, htransformed, hempty, hexsCutBranch⟩
    refine ⟨hexsCutProof, ?_, ?_, ?_, ?_⟩
    · rcases hexsCutBranch with hexs | hcut
      · rcases hexs with
          ⟨_hexsTag, _hsource, _hrightRows, hrightHead,
            _hcheck, _hpush⟩
        exact le_compactNumericVerifierCombineActiveCountLimit
          (CompactNumericChildResultBoundedHeadEq.expectedGammaCount_le_tokenCount
            hrightHead)
      · rcases hcut with
          ⟨_hcutTag, _hsource, _hrightRows, _hleftRows,
            hrightHead, _hleftHead, _hcheck, _hpush⟩
        exact le_compactNumericVerifierCombineActiveCountLimit
          (CompactNumericChildResultBoundedHeadEq.expectedGammaCount_le_tokenCount
            hrightHead)
    · exact le_compactNumericVerifierCombineActiveCountLimit
        (structuredListLayout_count_le_tokenCount htransformed.1)
    · rcases hexsCutBranch with hexs | hcut
      · rcases hexs with
          ⟨_hexsTag, _hsource, _hrightRows, _hrightHead,
            hcheck, _hpush⟩
        exact
          CompactFormulaTransformTotalExactBoundedGraph.stateCount_le_activeLimit
            hfirstCount hcheck.1
      · rcases hcut with
          ⟨_hcutTag, _hsource, _hrightRows, _hleftRows,
            _hrightHead, _hleftHead, hcheck, _hpush⟩
        exact
          CompactFormulaTransformTotalExactBoundedGraph.stateCount_le_activeLimit
            hfirstCount hcheck.1
    · intro htag
      rcases hexsCutBranch with hexs | hcut
      · omega
      · rcases hcut with
          ⟨_hcutTag, _hsource, _hrightRows, _hleftRows,
            _hrightHead, hleftHead, _hcheck, _hpush⟩
        exact le_compactNumericVerifierCombineActiveCountLimit
          (CompactNumericChildResultBoundedHeadEq.expectedGammaCount_le_tokenCount
            hleftHead)
  · right; right; right
    exact hfailure

theorem CompactNumericVerifierCombineStateGraph.countControls
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {ruleWitness : CompactNumericVerifierCombineRuleWitness}
    (hgraph : CompactNumericVerifierCombineStateGraph
      tokenTable width tokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      ruleWitness) :
    CompactNumericVerifierCombineCountControls
        tokenCount taskCoordinates ruleWitness /\
      CompactNumericVerifierCombineActiveRuleCountBounds
        tokenTable width tokenCount
        taskCoordinates.tag taskCoordinates.gammaFinish
          taskCoordinates.gammaCount taskCoordinates.gammaBoundary
        taskCoordinates.firstFinish taskCoordinates.firstCount
          taskCoordinates.secondFinish taskCoordinates.secondCount
        taskCoordinates.witnessFinish taskCoordinates.witnessCount
        currentCoordinates.valueBoundary currentCoordinates.valueCount
        nextCoordinates.valueBoundary nextCoordinates.valueCount
        currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
        nextCoordinates.statusTag nextCoordinates.statusBool ruleWitness := by
  rcases hgraph with ⟨_current, _next, hhead, _frame, hbranch⟩
  have htask := CompactNumericVerifierTaskCoreGraph.bounds hhead.core
  refine ⟨?_, activeRuleCountBounds_of_branchRows
    htask.gammaCount_le htask.firstCount_le hbranch⟩
  exact
    { taskGammaCount_le :=
        le_compactNumericVerifierCombineActiveCountLimit htask.gammaCount_le
      taskFirstCount_le :=
        le_compactNumericVerifierCombineActiveCountLimit htask.firstCount_le
      taskSecondCount_le :=
        le_compactNumericVerifierCombineActiveCountLimit htask.secondCount_le
      taskWitnessCount_le :=
        le_compactNumericVerifierCombineActiveCountLimit htask.witnessCount_le }

/-- The public form of the controls refers only to the actual 429-column row
environment. -/
def CompactNumericVerifierCombineEnvironmentCountControls
    (environment : Fin 429 -> Nat) : Prop :=
  let limit := compactNumericVerifierCombineActiveCountLimit (environment 2)
  let ruleWitness := compactNumericVerifierCombineRuleWitnessOf
    (environment 59) (environment 60) (environment 61)
    (environment 62) (environment 63) (environment 64)
    (environment 65) (environment 66) (environment 67)
    (environment 68) (environment 69) (environment 70)
    (environment 71) (environment 72) (environment 73)
    (environment 74) (environment 75) (environment 76)
    (environment 77) (environment 78) (environment 79)
    (environment 80) (environment 81) (environment 82)
    (environment 83) (environment 84) (environment 85)
    (environment 86) (environment 87) (environment 88)
    (environment 89) (environment 90) (environment 91)
    (environment 92)
  environment 49 <= limit /\
    environment 52 <= limit /\
    environment 54 <= limit /\
    environment 56 <= limit /\
    CompactNumericVerifierCombineActiveRuleCountBounds
      (environment 0) (environment 1) (environment 2)
      (environment 47) (environment 48) (environment 49) (environment 50)
      (environment 51) (environment 52) (environment 53) (environment 54)
      (environment 55) (environment 56)
      (environment 14) (environment 13) (environment 35) (environment 34)
      (environment 22) (environment 23) (environment 36) (environment 38)
      ruleWitness

set_option maxRecDepth 4000 in
theorem CompactNumericVerifierCombineStateGraph.environmentCountControls
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      FoundationCompactNumericListedDirectVerifierStateFormula.CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      FoundationCompactNumericListedDirectVerifierStateFormula.CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {ruleWitness : CompactNumericVerifierCombineRuleWitness}
    (hgraph : CompactNumericVerifierCombineStateGraph
      tokenTable width tokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
      ruleWitness) :
    let arguments := CompactNumericVerifierStepArguments.ofCombine
      taskCoordinates taskSizeWitness ruleWitness
    CompactNumericVerifierCombineEnvironmentCountControls
      (arguments.environment tokenTable width tokenCount
        currentCoordinates nextCoordinates currentSizeWitness
          nextSizeWitness) := by
  dsimp only
  rcases CompactNumericVerifierCombineStateGraph.countControls hgraph with
    ⟨htask, hrule⟩
  change taskCoordinates.gammaCount <=
      compactNumericVerifierCombineActiveCountLimit tokenCount /\
    taskCoordinates.firstCount <=
      compactNumericVerifierCombineActiveCountLimit tokenCount /\
    taskCoordinates.secondCount <=
      compactNumericVerifierCombineActiveCountLimit tokenCount /\
    taskCoordinates.witnessCount <=
      compactNumericVerifierCombineActiveCountLimit tokenCount /\ _
  exact ⟨htask.taskGammaCount_le, htask.taskFirstCount_le,
    htask.taskSecondCount_le, htask.taskWitnessCount_le, hrule⟩

/- The canonical combine graph produces one formula witness carrying both its
coordinate-size bound and its numerical loop controls. -/
set_option maxRecDepth 4000 in
theorem
    exists_compactNumericVerifierCombineStepFormulaWitness_with_countControls
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
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
    exists taskCoordinates : CompactNumericVerifierTaskRowCoordinates,
      exists taskSizeWitness : CompactNumericVerifierTaskSizeWitness,
      exists ruleWitness : CompactNumericVerifierCombineRuleWitness,
      exists witness : CompactNumericVerifierStepFormulaWitness
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentTokens.length
          (currentTokens.length + nextTokens.length),
        CompactNumericVerifierCombineEnvironmentCountControls
            witness.environment /\
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
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness := by
    dsimp only [CompactNumericVerifierStepArguments.Graph, arguments,
      CompactNumericVerifierStepArguments.ofCombine]
    refine Or.inr (Or.inr (Or.inr ?_))
    simpa only [
      FoundationCompactNumericListedDirectVerifierStepFormula.compactNumericVerifierStepCombineRuleWitness,
      compactNumericVerifierCombineRuleWitnessOf] using hcombine
  let witness := arguments.toFormulaWitness
    hcurrentPackage.1 hcurrentPackage.2.1
    hnextPackage.1 hnextPackage.2.1 hgraph
  refine ⟨taskCoordinates, taskSizeWitness, ruleWitness, witness, ?_, ?_⟩
  · change CompactNumericVerifierCombineEnvironmentCountControls
      (arguments.environment (compactFixedWidthTableCode width tokens)
        width tokens.length currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness)
    exact CompactNumericVerifierCombineStateGraph.environmentCountControls
      hcombine
  · intro coordinate
    change Nat.size (arguments.environment
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
      coordinate) <=
        compactNumericVerifierStepArgumentsCoordinateSizeBound arguments
          width tokens.length
    exact compactNumericVerifierStepEnvironment_size_le arguments
      (canonicalStateTable_size_le_coordinateSizeBound tokens width)
      (CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
        hcurrentPackage)
      (CompactNumericVerifierStateCanonicalCorePackage.coordinateSizeBounds
        hnextPackage)
      coordinate

#print axioms
  CompactFormulaTransformTotalExactBoundedGraph.stateCount_le_activeLimit
#print axioms CompactFormulaShiftListRow.sourceInnerCount_le_tokenCount
#print axioms CompactFormulaShiftListRow.candidateInnerCount_le_tokenCount
#print axioms CompactFormulaShiftListRow.stateCount_le_activeLimit
#print axioms compactFormulaShiftListRowDef_executionCountControls
#print axioms CompactFormulaTransformStateCoreGraph.countControls
#print axioms CompactFormulaTransformStateAtRows.countControls
#print axioms CompactFormulaTransformAdjacentStepWitnessBounded.countControls
#print axioms CompactFormulaShiftListRow.finalStateCountControls
#print axioms
  CompactFormulaShiftExactListRows.exists_rowEnvironment_with_countControls
#print axioms
  CompactFormulaShiftExactListRows.expectedCount_le_formulaCount
#print axioms
  CompactNumericChildResultBoundedHeadEq.expectedGammaCount_le_tokenCount
#print axioms CompactNumericVerifierCombineStateGraph.countControls
#print axioms CompactNumericVerifierCombineStateGraph.environmentCountControls
#print axioms
  exists_compactNumericVerifierCombineStepFormulaWitness_with_countControls

end FoundationCompactNumericListedDirectVerifierCombineActiveCountBounds
