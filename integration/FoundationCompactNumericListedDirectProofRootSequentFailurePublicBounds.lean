import integration.FoundationCompactNumericListedDirectProofRootSequentFailureSharedRowsPublicBounds
import integration.FoundationCompactNumericListedDirectSequentFormulaCanonicalDataPublicBounds
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds
import integration.FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
import integration.FoundationCompactNumericListedDirectTraceBounds

/-!
# Public bounds for proof-root sequent failure

For a nonempty body whose count-prefixed sequent parser returns no output, this
module installs the successful prefix and first failed formula trace in the
shared canonical table.  Every nested endpoint and every root coordinate is
bounded by an explicit function of the original root-input weight.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootSequentFailurePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedStateBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData
open FoundationCompactNumericListedDirectSequentFormulaCanonicalDataPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectSequentFormulaEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaFailureSemantics
open FoundationCompactNumericListedDirectSequentFormulaFailureBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaNoOutputBoundedFormula
open FoundationCompactNumericListedDirectProofRootSequentFailureBoundedFormula
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectProofRootSequentFailureSharedRowsPublicBounds

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

private theorem nat_le_two_pow_of_size_le
    {value sizeBound : Nat} (hsize : Nat.size value <= sizeBound) :
    value <= 2 ^ sizeBound :=
  (Nat.size_le.mp hsize).le

private theorem structuredList_count_eq_of_same_start
    {tokenTable width tokenCount start
      leftCount leftFinish leftBoundary
      rightCount rightFinish rightBoundary : Nat}
    (hleft : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start leftCount leftFinish leftBoundary)
    (hright : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start rightCount rightFinish rightBoundary) :
    leftCount = rightCount := by
  rcases hleft with
    ⟨_leftBody, _hleftBody, hleftHeader, _hleftBoundary⟩
  rcases hright with
    ⟨_rightBody, _hrightBody, hrightHeader, _hrightBoundary⟩
  exact (CompactAdditiveTokenCell.value_eq_tableValue hleftHeader.1).trans
    (CompactAdditiveTokenCell.value_eq_tableValue hrightHeader.1).symm

private theorem compactFormulaParserNoOutputLocalTrace_weight_le_rootBound
    {tokens : List Nat} {states : CompactFormulaTokenParserDirectTrace}
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound tokens)
      (compactFormulaParserInitialState 0 tokens) none states)
    {streamWeight : Nat}
    (hstream : compactAdditiveValueWeight tokens <= streamWeight) :
    compactAdditiveValueWeight states <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight := by
  have hlocal := hvalid.1
  have hrows := compactAdditiveValueWeight_list_le states
    (compactNumericFormulaParserStateWeightBound
      (compactAdditiveValueWeight tokens)
      (compactSyntaxRunFuelBound tokens)
      (compactSyntaxRunFuelBound tokens))
    (fun state hstate => by
      simpa only [Nat.zero_add] using
        compactFormulaParserLocalTrace_member_state_weight_le
          hlocal hstate)
  have hraw :
      compactAdditiveValueWeight states <=
        compactNumericFormulaParserTraceWeightBound
          (compactAdditiveValueWeight tokens) 0
            (compactSyntaxRunFuelBound tokens) := by
    unfold compactNumericFormulaParserTraceWeightBound
    rw [hlocal.1] at hrows
    simpa only [Nat.zero_add] using hrows
  have hfuel := compactSyntaxRunFuelBound_le_weightBound hstream
  unfold compactNumericRootSyntaxParserTraceWeightBound
  exact hraw.trans
    (compactNumericFormulaParserTraceWeightBound_mono
      hstream (by omega) hfuel)

def compactProofRootSequentFailurePrefixInputWeightBound
    (inputWeight : Nat) : Nat :=
  Nat.size inputWeight + 1 + inputWeight * inputWeight

def compactProofRootSequentFailureSharedDataWeightBound
    (inputWeight : Nat) : Nat :=
  inputWeight + inputWeight +
    compactProofRootSequentFailurePrefixInputWeightBound inputWeight +
    compactSequentFormulaCanonicalSuffixesWeightBound
      (compactProofRootSequentFailurePrefixInputWeightBound inputWeight) +
    compactNumericNestedListWeightBound inputWeight +
    compactSequentFormulaCanonicalParserTracesWeightBound
      (compactProofRootSequentFailurePrefixInputWeightBound inputWeight) +
    compactNumericRootSyntaxParserTraceWeightBound inputWeight

def compactProofRootSequentFailureSharedCoordinateBound
    (inputWeight : Nat) : Nat :=
  compactProofRootSequentFailureSharedCoordinateSizeBound
    (compactProofRootSequentFailureSharedDataWeightBound inputWeight)

def compactProofRootSequentFailurePrefixCoordinateBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootSequentFailureSharedCoordinateBound inputWeight
  compactSequentFormulaEndpointPublicCoordinateSizeBound
    sharedBound sharedBound

def compactProofRootSequentFailureParserCoordinateBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootSequentFailureSharedCoordinateBound inputWeight
  compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
    sharedBound sharedBound

def compactProofRootSequentFailureBoundarySizeBound
    (inputWeight : Nat) : Nat :=
  (inputWeight + 1) *
    compactProofRootSequentFailureSharedCoordinateBound inputWeight

def compactProofRootSequentFailureArithmeticCoordinateBound
    (inputWeight : Nat) : Nat :=
  compactProofRootSequentFailureBoundarySizeBound inputWeight +
    compactProofRootSequentFailurePrefixCoordinateBound inputWeight +
    compactProofRootSequentFailureParserCoordinateBound inputWeight +
    inputWeight + 16

def compactProofRootSequentFailureRootCoordinateBound
    (inputWeight : Nat) : Nat :=
  compactProofRootSequentFailureBoundarySizeBound inputWeight +
    compactProofRootSequentFailureArithmeticCoordinateBound inputWeight +
    inputWeight + 10

def compactProofRootSequentFailurePublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootSequentFailureSharedCoordinateBound inputWeight +
    compactProofRootSequentFailureRootCoordinateBound inputWeight + 2

private theorem compactProofRootSequentFailureBoundary_le_root
    (inputWeight : Nat) :
    compactProofRootSequentFailureBoundarySizeBound inputWeight <=
      compactProofRootSequentFailureRootCoordinateBound inputWeight := by
  unfold compactProofRootSequentFailureRootCoordinateBound
  omega

private theorem compactProofRootSequentFailureBoundary_le_arithmetic
    (inputWeight : Nat) :
    compactProofRootSequentFailureBoundarySizeBound inputWeight <=
      compactProofRootSequentFailureArithmeticCoordinateBound
        inputWeight := by
  unfold compactProofRootSequentFailureArithmeticCoordinateBound
  omega

private theorem compactProofRootSequentFailureInput_le_root
    (inputWeight : Nat) :
    inputWeight <=
      compactProofRootSequentFailureRootCoordinateBound inputWeight := by
  unfold compactProofRootSequentFailureRootCoordinateBound
  omega

private theorem compactProofRootSequentFailureArithmeticPow_size_le_root
    (inputWeight : Nat) :
    Nat.size
        (2 ^
          compactProofRootSequentFailureArithmeticCoordinateBound
            inputWeight) <=
      compactProofRootSequentFailureRootCoordinateBound inputWeight := by
  rw [Nat.size_pow]
  unfold compactProofRootSequentFailureRootCoordinateBound
  omega

private theorem compactProofRootSequentFailureShared_le_public
    (inputWeight : Nat) :
    compactProofRootSequentFailureSharedCoordinateBound inputWeight <=
      compactProofRootSequentFailurePublicCoordinateSizeBound
        inputWeight := by
  unfold compactProofRootSequentFailurePublicCoordinateSizeBound
  omega

private theorem compactProofRootSequentFailureRootPow_size_le_public
    (inputWeight : Nat) :
    Nat.size
        (2 ^
          compactProofRootSequentFailureRootCoordinateBound inputWeight) <=
      compactProofRootSequentFailurePublicCoordinateSizeBound
        inputWeight := by
  rw [Nat.size_pow]
  unfold compactProofRootSequentFailurePublicCoordinateSizeBound
  omega

structure CompactProofRootSequentFailurePublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width : Nat.size width <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  bodyStart : Nat.size bodyStart <= bound
  bodyFinish : Nat.size bodyFinish <= bound
  endpointBound : Nat.size endpointBound <= bound

structure CompactProofRootSequentFailureEndpointCoordinateSizeBounds
    (coordinates : CompactProofRootSequentFailureEndpointCoordinates)
    (bound : Nat) : Prop where
  inputBoundary : Nat.size coordinates.inputBoundary <= bound
  inputCount : Nat.size coordinates.inputCount <= bound
  inputBoundarySize : Nat.size coordinates.inputBoundarySize <= bound
  bodyBoundary : Nat.size coordinates.bodyBoundary <= bound
  bodyCount : Nat.size coordinates.bodyCount <= bound
  bodyBoundarySize : Nat.size coordinates.bodyBoundarySize <= bound
  tag : Nat.size coordinates.tag <= bound
  sequentBound : Nat.size coordinates.sequentBound <= bound

structure CompactProofRootSequentFailureArithmeticPublicBounds
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish inputWeight : Nat) : Prop where
  tokenTable :
    Nat.size tokenTable <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  width_size :
    Nat.size width <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  width_value :
    width <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  tokenCount_size :
    Nat.size tokenCount <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  tokenCount_value :
    tokenCount <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  inputStart :
    Nat.size inputStart <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  inputFinish :
    Nat.size inputFinish <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  bodyStart :
    Nat.size bodyStart <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  bodyFinish :
    Nat.size bodyFinish <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight

structure CompactProofRootSequentFailurePreparedSharedPublicBounds
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish prefixInputStart prefixInputFinish
      valueStart valueFinish inputWeight : Nat) : Prop where
  tokenTable :
    Nat.size tokenTable <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  width_size :
    Nat.size width <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  width_value :
    width <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  tokenCount_size :
    Nat.size tokenCount <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  tokenCount_value :
    tokenCount <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  inputStart :
    Nat.size inputStart <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  inputFinish :
    Nat.size inputFinish <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  bodyStart :
    Nat.size bodyStart <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  bodyFinish :
    Nat.size bodyFinish <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  prefixInputStart :
    Nat.size prefixInputStart <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  prefixInputFinish :
    Nat.size prefixInputFinish <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  valueStart :
    Nat.size valueStart <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight
  valueFinish :
    Nat.size valueFinish <=
      compactProofRootSequentFailureSharedCoordinateBound inputWeight

structure CompactProofRootSequentFailurePreparedPackage
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish prefixInputStart prefixInputFinish
      valueStart valueFinish failedStart failedFinish count : Nat)
    (input body prefixInput inputTail : List Nat)
    (formulaValues : List (List Nat))
    (prefixCoordinates : CompactSequentFormulaEndpointCoordinates)
    (inputWeight : Nat) : Prop where
  inputLayout :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input
  bodyLayout :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount bodyStart bodyFinish body
  prefixInputLayout :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount
        prefixInputStart prefixInputFinish prefixInput
  valueStructure :
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount valueStart formulaValues.length
        valueFinish prefixCoordinates.valueBoundary
  prefixGraph :
    CompactSequentFormulaEndpointGraph
      tokenTable width tokenCount prefixInputStart prefixInputFinish
        valueStart valueFinish failedStart failedFinish prefixCoordinates
  prefixPublic :
    CompactSequentFormulaEndpointPublicBounds
      failedStart failedFinish prefixCoordinates
        (compactSequentFormulaEndpointPublicCoordinateSizeBound
          width tokenCount)
  prefixBounded :
    CompactSequentFormulaEndpointBoundedGraph
      tokenTable width tokenCount prefixInputStart prefixInputFinish
        valueStart valueFinish failedStart failedFinish
          (2 ^
            compactSequentFormulaEndpointPublicCoordinateSizeBound
              width tokenCount)
  failureBounded :
    CompactParserSyntaxNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount failedStart failedFinish 1 0 0
        (2 ^
          compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
            width tokenCount)
  prefixActualToPublic :
    compactSequentFormulaEndpointPublicCoordinateSizeBound
        width tokenCount <=
      compactProofRootSequentFailurePrefixCoordinateBound inputWeight
  failureActualToPublic :
    compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
        width tokenCount <=
      compactProofRootSequentFailureParserCoordinateBound inputWeight
  prefixInput_eq :
    prefixInput = prefixCoordinates.valueCount :: inputTail
  failedIndex_lt : prefixCoordinates.valueCount < count
  sharedPublic :
    CompactProofRootSequentFailurePreparedSharedPublicBounds
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish prefixInputStart prefixInputFinish
        valueStart valueFinish inputWeight

structure CompactProofRootSequentFailureCanonicalData
    (count inputWeight : Nat)
    (inputTail prefixInput failedInput : List Nat)
    (formulaValues suffixes : List (List Nat))
    (parserTraces : List CompactFormulaTokenParserDirectTrace)
    (failureStates : CompactFormulaTokenParserDirectTrace) : Prop where
  prefixInput_eq :
    prefixInput = formulaValues.length :: inputTail
  prefixParser :
    compactSequentTokenValueParser prefixInput =
      some (formulaValues, failedInput)
  failedIndex_lt : formulaValues.length < count
  suffixCount : suffixes.length = formulaValues.length + 1
  parserCount : parserTraces.length = formulaValues.length
  firstSuffix : suffixes.getI 0 = inputTail
  finalSuffix : suffixes.getI formulaValues.length = failedInput
  steps :
    ∀ index < formulaValues.length,
      CompactFormulaTokenParserDirectTraceValid
          0 (suffixes.getI index) (suffixes.getI (index + 1))
            (parserTraces.getI index) ∧
        suffixes.getI index =
          formulaValues.getI index ++ suffixes.getI (index + 1)
  failureStartWell :
    CompactSyntaxTaskStackFieldsWellFormed [(1, 0, 0)]
  failureLocal :
    CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound failedInput)
      (failedInput, [(1, 0, 0)], none) none failureStates
  prefixInputWeight :
    compactAdditiveValueWeight prefixInput <=
      compactProofRootSequentFailurePrefixInputWeightBound inputWeight
  suffixWeight :
    compactAdditiveValueWeight suffixes <=
      compactSequentFormulaCanonicalSuffixesWeightBound
        (compactProofRootSequentFailurePrefixInputWeightBound inputWeight)
  formulaValuesWeight :
    compactAdditiveValueWeight formulaValues <=
      compactNumericNestedListWeightBound inputWeight
  parserWeight :
    compactAdditiveValueWeight parserTraces <=
      compactSequentFormulaCanonicalParserTracesWeightBound
        (compactProofRootSequentFailurePrefixInputWeightBound inputWeight)
  failureWeight :
    compactAdditiveValueWeight failureStates <=
      compactNumericRootSyntaxParserTraceWeightBound inputWeight

structure CompactProofRootSequentFailureRootRowsPackage
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish inputBoundary inputBoundarySize
      bodyBoundary bodyBoundarySize tag arithmeticBound inputWeight : Nat)
    (input body : List Nat) : Prop where
  inputLayout :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input
  inputWitness :
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart input.length inputFinish
        inputBoundary inputBoundarySize
  bodyWitness :
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount bodyStart body.length bodyFinish
        bodyBoundary bodyBoundarySize
  rootCons :
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount bodyBoundary body.length
        inputBoundary input.length tag
  tag_le : tag <= 9
  sequent :
    CompactSequentFormulaNoOutputEndpointBoundedGraph
      tokenTable width tokenCount bodyStart bodyFinish
        (2 ^ arithmeticBound)
  arithmeticPublic :
    CompactProofRootSequentFailureArithmeticPublicBounds
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish inputWeight

private theorem
    compactProofRootSequentFailureSharedCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactProofRootSequentFailureSharedCoordinateSizeBound left <=
      compactProofRootSequentFailureSharedCoordinateSizeBound right := by
  have htwice : 2 * left <= 2 * right :=
    Nat.mul_le_mul_left 2 h
  have hproduct : left * (2 * left) <= right * (2 * right) :=
    Nat.mul_le_mul h htwice
  unfold compactProofRootSequentFailureSharedCoordinateSizeBound
  omega

private theorem prefixEndpoint_bounded_of_public
    {tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish : Nat}
    {coordinates : CompactSequentFormulaEndpointCoordinates}
    {bound : Nat}
    (hgraph : CompactSequentFormulaEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        valueStart valueFinish finalStart finalFinish coordinates)
    (hpublic : CompactSequentFormulaEndpointPublicBounds
      finalStart finalFinish coordinates bound) :
    CompactSequentFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        valueStart valueFinish finalStart finalFinish (2 ^ bound) := by
  unfold CompactSequentFormulaEndpointBoundedGraph
  have hsmall
      {value : Nat}
      (hvalue : value ∈
        compactSequentFormulaEndpointCoordinateValues coordinates) :
      value <= 2 ^ bound :=
    nat_le_two_pow_of_size_le (hpublic.value_size_le value hvalue)
  refine
    ⟨coordinates.inputBoundary,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.inputCount,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.inputBoundarySize,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.firstStart,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.firstFinish,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.firstBoundary,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.firstCount,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.firstBoundarySize,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.suffixBoundary,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.suffixCount,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.valueBoundary,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.valueCount,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.valueBoundarySize,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.finalBoundary,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.finalCount,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.finalBoundarySize,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.traceTableWidth,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      coordinates.traceValueBound,
        hsmall (by simp [compactSequentFormulaEndpointCoordinateValues]),
      by simpa only [
        compactSequentFormulaEndpointCoordinatesOfValues] using hgraph⟩

private theorem failureEndpoint_bounded_of_public
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates}
    {bound : Nat}
    (hgraph : CompactParserSyntaxNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish 1 0 0 coordinates)
    (hpublic : CompactParserSyntaxNoOutputExactEndpointPublicBounds
      coordinates bound) :
    CompactParserSyntaxNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish 1 0 0
        (2 ^ bound) := by
  unfold CompactParserSyntaxNoOutputExactEndpointBoundedGraph
  have hsmall
      {value : Nat}
      (hvalue : value ∈
        compactParserSyntaxNoOutputExactEndpointCoordinateValues
          coordinates) :
      value <= 2 ^ bound :=
    nat_le_two_pow_of_size_le (hpublic.value_size_le value hvalue)
  refine
    ⟨coordinates.inputBoundary,
        hsmall (by
          simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues]),
      coordinates.inputCount,
        hsmall (by
          simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues]),
      coordinates.inputBoundarySize,
        hsmall (by
          simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues]),
      coordinates.stateBoundary,
        hsmall (by
          simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues]),
      coordinates.stateCount,
        hsmall (by
          simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues]),
      coordinates.tableWidth,
        hsmall (by
          simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues]),
      coordinates.valueBound,
        hsmall (by
          simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues]),
      by simpa only [
        compactParserSyntaxNoOutputExactEndpointCoordinatesOfValues]
          using hgraph⟩

private theorem rootEndpoint_bounded_of_sizeBounds
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootSequentFailureEndpointCoordinates}
    {bound : Nat}
    (hgraph :
      CompactProofRootSequentFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates)
    (hsize :
      CompactProofRootSequentFailureEndpointCoordinateSizeBounds
        coordinates bound) :
    CompactProofRootSequentFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish (2 ^ bound) := by
  unfold CompactProofRootSequentFailureEndpointBoundedGraph
  refine
    ⟨coordinates.inputBoundary,
        nat_le_two_pow_of_size_le hsize.inputBoundary,
      coordinates.inputCount,
        nat_le_two_pow_of_size_le hsize.inputCount,
      coordinates.inputBoundarySize,
        nat_le_two_pow_of_size_le hsize.inputBoundarySize,
      coordinates.bodyBoundary,
        nat_le_two_pow_of_size_le hsize.bodyBoundary,
      coordinates.bodyCount,
        nat_le_two_pow_of_size_le hsize.bodyCount,
      coordinates.bodyBoundarySize,
        nat_le_two_pow_of_size_le hsize.bodyBoundarySize,
      coordinates.tag,
        nat_le_two_pow_of_size_le hsize.tag,
      coordinates.sequentBound,
        nat_le_two_pow_of_size_le hsize.sequentBound,
      by simpa only [
        compactProofRootSequentFailureEndpointCoordinatesOfValues]
          using hgraph⟩

set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootSequentFailureCanonicalData_of_cons_body_none_with_publicBounds
    (tag count : Nat) (inputTail : List Nat)
    (hparser :
      compactSequentTokenValueParser (count :: inputTail) = none) :
    let input := tag :: count :: inputTail
    let inputWeight := compactAdditiveValueWeight input
    ∃ prefixInput : List Nat,
    ∃ failedInput : List Nat,
    ∃ formulaValues : List (List Nat),
    ∃ suffixes : List (List Nat),
    ∃ parserTraces : List CompactFormulaTokenParserDirectTrace,
    ∃ failureStates : CompactFormulaTokenParserDirectTrace,
      CompactProofRootSequentFailureCanonicalData
        count inputWeight inputTail prefixInput failedInput
          formulaValues suffixes parserTraces failureStates := by
  rcases (compactSequentTokenValueParser_cons_eq_none_iff
      count inputTail).mp hparser with
    ⟨failedIndex, hfailedIndex, parsedValues, failedInput,
      hprefixRepeat, hfailedValueParser⟩
  have hfailedParser : compactFormulaTokenParser 0 failedInput = none := by
    simpa [compactFormulaTokenValueParser] using hfailedValueParser
  rcases compactFormulaTokenValuesRepeat_sound hprefixRepeat with
    ⟨Gamma, hGammaLength, hinputTail, hparsedValues⟩
  have hprefixRepeat' :
      compactFormulaTokenValuesRepeat Gamma.length inputTail =
        some (Gamma.map compactArithmeticFormulaTokens, failedInput) := by
    simpa only [hGammaLength, hparsedValues] using hprefixRepeat
  have hfailedIndex' : Gamma.length < count := by omega
  rcases
      exists_compactSequentFormulaCanonicalDirectData_with_publicBounds
        Gamma failedInput with
    ⟨suffixes, parserTraces, hsuffixCount, hparserCount,
      hfirst, hfinal, hsteps, hsuffixWeight, hparserWeight⟩
  have hfirstInputTail : suffixes.getI 0 = inputTail := by
    calc
      suffixes.getI 0 =
          Gamma.flatMap compactArithmeticFormulaTokens ++ failedInput :=
        hfirst
      _ = inputTail := hinputTail.symm
  have houtput : compactSyntaxParserStateOutput
      ((compactSyntaxParserStep^[compactSyntaxRunFuelBound failedInput])
        (compactFormulaParserInitialState 0 failedInput)) = none := by
    simpa [compactFormulaTokenParser,
      compactFormulaTokenParserRun] using hfailedParser
  rcases (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound failedInput)
      (compactFormulaParserInitialState 0 failedInput) none).mp houtput with
    ⟨failureStates, hfailureValid⟩
  have hfailureLocal : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound failedInput)
      (failedInput, [(1, 0, 0)], none) none failureStates := by
    simpa [compactFormulaParserInitialState,
      compactFormulaTask] using hfailureValid
  have hfailureStartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  let input := tag :: count :: inputTail
  let body := count :: inputTail
  let prefixInput := Gamma.length :: inputTail
  let formulaValues := Gamma.map compactArithmeticFormulaTokens
  let inputWeight := compactAdditiveValueWeight input
  have hbodyWeight : compactAdditiveValueWeight body <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show body <:+ input from by simp [body, input])
  have htailWeight :
      compactAdditiveValueWeight inputTail <= inputWeight := by
    exact (compactAdditiveValueWeight_suffix_le
      (show inputTail <:+ body from by simp [body])).trans hbodyWeight
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have hprefixLength : prefixInput.length <= inputWeight := by
    have htailLength : inputTail.length + 1 <= input.length := by
      simp [input]
    simpa [prefixInput] using htailLength.trans hinputLength
  have hcountWeight :
      compactAdditiveValueWeight count <= inputWeight :=
    compactAdditiveValueWeight_nat_mem_le
      (show count ∈ input from by simp [input])
  have hfailedIndexWeight :
      compactAdditiveValueWeight Gamma.length <= inputWeight := by
    simp only [compactAdditiveValueWeight_nat] at hcountWeight ⊢
    have hsize := Nat.size_le_size (Nat.le_of_lt hfailedIndex')
    omega
  have hprefixMember :
      ∀ value ∈ prefixInput,
        compactAdditiveValueWeight value <= inputWeight := by
    intro value hvalue
    simp only [prefixInput, List.mem_cons] at hvalue
    rcases hvalue with rfl | htail
    · exact hfailedIndexWeight
    · exact compactAdditiveValueWeight_nat_mem_le
        (show value ∈ input from by simp [input, htail])
  have hprefixWeightRaw :=
    compactAdditiveValueWeight_list_le
      prefixInput inputWeight hprefixMember
  have hprefixLengthSize :
      Nat.size prefixInput.length <= Nat.size inputWeight :=
    Nat.size_le_size hprefixLength
  have hprefixWeight :
      compactAdditiveValueWeight prefixInput <=
        compactProofRootSequentFailurePrefixInputWeightBound
          inputWeight := by
    unfold compactProofRootSequentFailurePrefixInputWeightBound
    have hproduct := Nat.mul_le_mul_right inputWeight hprefixLength
    omega
  have hsuffixWeightPublic :
      compactAdditiveValueWeight suffixes <=
        compactSequentFormulaCanonicalSuffixesWeightBound
          (compactProofRootSequentFailurePrefixInputWeightBound
            inputWeight) := by
    have hstreamEq :
        compactSequentListTokens Gamma ++ failedInput = prefixInput := by
      simp [prefixInput, compactSequentListTokens, hinputTail]
    rw [hstreamEq] at hsuffixWeight
    exact hsuffixWeight.trans
      (FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.compactSequentFormulaCanonicalSuffixesWeightBound_mono
        hprefixWeight)
  have hparserWeightPublic :
      compactAdditiveValueWeight parserTraces <=
        compactSequentFormulaCanonicalParserTracesWeightBound
          (compactProofRootSequentFailurePrefixInputWeightBound
            inputWeight) := by
    have hstreamEq :
        compactSequentListTokens Gamma ++ failedInput = prefixInput := by
      simp [prefixInput, compactSequentListTokens, hinputTail]
    rw [hstreamEq] at hparserWeight
    exact hparserWeight.trans
      (FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.compactSequentFormulaCanonicalParserTracesWeightBound_mono
        hprefixWeight)
  have hformulaValuesWeight :
      compactAdditiveValueWeight formulaValues <=
        compactNumericNestedListWeightBound inputWeight := by
    have hraw :=
      (compactFormulaTokenValuesRepeat_components_weight_le
        hprefixRepeat').1
    dsimp only [formulaValues]
    exact hraw.trans
      (compactNumericNestedListWeightBound_mono htailWeight)
  have hfailedInputWeight :
      compactAdditiveValueWeight failedInput <= inputWeight := by
    have hfailedSuffix : failedInput <:+ inputTail :=
      ⟨Gamma.flatMap compactArithmeticFormulaTokens, hinputTail.symm⟩
    exact (compactAdditiveValueWeight_suffix_le hfailedSuffix).trans
      htailWeight
  have hfailureWeight :
      compactAdditiveValueWeight failureStates <=
        compactNumericRootSyntaxParserTraceWeightBound inputWeight :=
    compactFormulaParserNoOutputLocalTrace_weight_le_rootBound
      hfailureLocal hfailedInputWeight
  refine
    ⟨prefixInput, failedInput, formulaValues, suffixes,
      parserTraces, failureStates, ?_⟩
  exact
    { prefixInput_eq := by
        simp [prefixInput, formulaValues]
      prefixParser := by
        simpa [prefixInput, formulaValues,
          compactSequentTokenValueParser] using hprefixRepeat'
      failedIndex_lt := by
        simpa [formulaValues] using hfailedIndex'
      suffixCount := by
        simpa [formulaValues] using hsuffixCount
      parserCount := by
        simpa [formulaValues] using hparserCount
      firstSuffix := hfirstInputTail
      finalSuffix := by
        simpa [formulaValues] using hfinal
      steps := by
        intro index hindex
        simpa [formulaValues] using hsteps index (by
          simpa [formulaValues] using hindex)
      failureStartWell := hfailureStartWell
      failureLocal := hfailureLocal
      prefixInputWeight := hprefixWeight
      suffixWeight := hsuffixWeightPublic
      formulaValuesWeight := hformulaValuesWeight
      parserWeight := hparserWeightPublic
      failureWeight := hfailureWeight }

set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootSequentFailurePreparedPackage_of_cons_body_none_with_publicBounds
    (tag count : Nat) (inputTail : List Nat)
    (hparser :
      compactSequentTokenValueParser (count :: inputTail) = none) :
    let input := tag :: count :: inputTail
    let body := count :: inputTail
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ prefixInputStart prefixInputFinish valueStart valueFinish,
    ∃ failedStart failedFinish,
    ∃ prefixInput : List Nat,
    ∃ formulaValues : List (List Nat),
    ∃ prefixCoordinates : CompactSequentFormulaEndpointCoordinates,
      CompactProofRootSequentFailurePreparedPackage
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish prefixInputStart prefixInputFinish
          valueStart valueFinish failedStart failedFinish count
          input body prefixInput inputTail formulaValues
          prefixCoordinates inputWeight := by
  let input := tag :: count :: inputTail
  let body := count :: inputTail
  let inputWeight := compactAdditiveValueWeight input
  rcases
      exists_compactProofRootSequentFailureCanonicalData_of_cons_body_none_with_publicBounds
        tag count inputTail hparser with
    ⟨prefixInput, failedInput, formulaValues, suffixes,
      parserTraces, failureStates, hcanonical⟩
  have hbodyWeight :
      compactAdditiveValueWeight body <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show body <:+ input from by simp [body, input])
  have hprefixWeight :
      compactAdditiveValueWeight prefixInput <=
        compactProofRootSequentFailurePrefixInputWeightBound
          inputWeight := by
    simpa only [inputWeight, input] using hcanonical.prefixInputWeight
  have hsuffixWeight :
      compactAdditiveValueWeight suffixes <=
        compactSequentFormulaCanonicalSuffixesWeightBound
          (compactProofRootSequentFailurePrefixInputWeightBound
            inputWeight) := by
    simpa only [inputWeight, input] using hcanonical.suffixWeight
  have hformulaValuesWeight :
      compactAdditiveValueWeight formulaValues <=
        compactNumericNestedListWeightBound inputWeight := by
    simpa only [inputWeight, input] using hcanonical.formulaValuesWeight
  have hparserWeight :
      compactAdditiveValueWeight parserTraces <=
        compactSequentFormulaCanonicalParserTracesWeightBound
          (compactProofRootSequentFailurePrefixInputWeightBound
            inputWeight) := by
    simpa only [inputWeight, input] using hcanonical.parserWeight
  have hfailureWeight :
      compactAdditiveValueWeight failureStates <=
        compactNumericRootSyntaxParserTraceWeightBound inputWeight := by
    simpa only [inputWeight, input] using hcanonical.failureWeight
  rcases
      exists_compactProofRootSequentFailureSharedRows_with_publicBounds
        input body prefixInput suffixes formulaValues
          parserTraces failureStates with
    ⟨tokenTable, width, tokenCount,
      inputStart, inputFinish, bodyStart, bodyFinish,
      prefixInputStart, prefixInputFinish, valueStart, valueFinish,
      _failureStateStart, _failureStateFinish,
      suffixBoundary, valueBoundary, failureStateBoundary,
      hshared, hsharedPublic⟩
  have hsharedDataWeight :
      compactProofRootSequentFailureSharedDataWeight
          input body prefixInput suffixes formulaValues
            parserTraces failureStates <=
        compactProofRootSequentFailureSharedDataWeightBound
          inputWeight := by
    unfold compactProofRootSequentFailureSharedDataWeight
      compactProofRootSequentFailureSharedDataWeightBound
    omega
  have hsharedCoordinate :
      compactProofRootSequentFailureSharedCoordinateSizeBound
          (compactProofRootSequentFailureSharedDataWeight
            input body prefixInput suffixes formulaValues
              parserTraces failureStates) <=
        compactProofRootSequentFailureSharedCoordinateBound
          inputWeight := by
    unfold compactProofRootSequentFailureSharedCoordinateBound
    exact
      compactProofRootSequentFailureSharedCoordinateSizeBound_mono
        hsharedDataWeight
  let sharedBound :=
    compactProofRootSequentFailureSharedCoordinateBound inputWeight
  have hwidthValue : width <= sharedBound :=
    hsharedPublic.width_value.trans (by
      simpa only [sharedBound] using hsharedCoordinate)
  have htokenCountValue : tokenCount <= sharedBound :=
    hsharedPublic.tokenCount_value.trans (by
      simpa only [sharedBound] using hsharedCoordinate)
  have hparserRows :
      ∀ index < formulaValues.length,
        ∃ parserStateBoundary,
          CompactUnifiedParserStateListRowLayouts
              tokenTable width tokenCount parserStateBoundary
                (parserTraces.getI index) ∧
            Nat.size parserStateBoundary <=
              ((parserTraces.getI index).length + 1) * tokenCount := by
    intro index hindex
    apply hshared.parserRows index
    rw [hcanonical.parserCount]
    exact hindex
  have hsuffixCount' :
      suffixes.length = formulaValues.length + 1 :=
    hcanonical.suffixCount
  have hparserCount' :
      parserTraces.length = formulaValues.length :=
    hcanonical.parserCount
  have hsteps' :
      ∀ index < formulaValues.length,
        CompactFormulaTokenParserDirectTraceValid
            0 (suffixes.getI index) (suffixes.getI (index + 1))
              (parserTraces.getI index) ∧
          suffixes.getI index =
            formulaValues.getI index ++ suffixes.getI (index + 1) :=
    hcanonical.steps
  have hprefixInputEq :
      prefixInput = formulaValues.length :: suffixes.getI 0 := by
    calc
      prefixInput = formulaValues.length :: inputTail :=
        hcanonical.prefixInput_eq
      _ = formulaValues.length :: suffixes.getI 0 := by
        rw [hcanonical.firstSuffix]
  have hfinalEq : suffixes.getI formulaValues.length = failedInput :=
    hcanonical.finalSuffix
  rcases
      exists_compactSequentFormulaEndpointGraph_of_rows_with_publicBounds
        hshared.prefixInputLayout hshared.suffixRows
        hshared.suffixBoundary_size_le
        hshared.valueStructure hshared.valueRows
        hshared.valueBoundary_size_le
        hparserRows hsuffixCount' hparserCount' hsteps'
        hprefixInputEq hfinalEq with
    ⟨failedStart, failedFinish, prefixCoordinates,
      hprefixGraph, hprefixPublic⟩
  have hprefixActualToPublic :
      compactSequentFormulaEndpointPublicCoordinateSizeBound
          width tokenCount <=
        compactProofRootSequentFailurePrefixCoordinateBound
          inputWeight := by
    dsimp only [compactProofRootSequentFailurePrefixCoordinateBound,
      sharedBound]
    exact
      FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.compactSequentFormulaEndpointPublicCoordinateSizeBound_mono
        hwidthValue htokenCountValue
  let prefixActualBound :=
    compactSequentFormulaEndpointPublicCoordinateSizeBound
      width tokenCount
  have hprefixBounded :
      CompactSequentFormulaEndpointBoundedGraph
        tokenTable width tokenCount prefixInputStart prefixInputFinish
          valueStart valueFinish failedStart failedFinish
          (2 ^ prefixActualBound) :=
    prefixEndpoint_bounded_of_public hprefixGraph hprefixPublic
  rcases hprefixGraph.sound with
    ⟨decodedPrefixInput, decodedValues, decodedFailedInput,
      hdecodedPrefixLayout, _hdecodedValuesLayout,
      hdecodedFailedLayout, hdecodedPrefixParser⟩
  have hdecodedPrefixEq : decodedPrefixInput = prefixInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hshared.prefixInputLayout hdecodedPrefixLayout).1
  rw [hdecodedPrefixEq] at hdecodedPrefixParser
  have hknownPrefixParser : compactSequentTokenValueParser prefixInput =
      some (formulaValues, failedInput) :=
    hcanonical.prefixParser
  have hdecodedPairEq :
      (decodedValues, decodedFailedInput) =
        (formulaValues, failedInput) :=
    Option.some.inj
      (hdecodedPrefixParser.symm.trans hknownPrefixParser)
  have hdecodedFailedEq : decodedFailedInput = failedInput :=
    congrArg Prod.snd hdecodedPairEq
  rw [hdecodedFailedEq] at hdecodedFailedLayout
  rcases
      exists_compactParserSyntaxNoOutputExactEndpointGraph_of_rows_with_publicBounds
        hdecodedFailedLayout hshared.failureStateRows
        hshared.failureStateBoundary_size_le
        hcanonical.failureStartWell hcanonical.failureLocal with
    ⟨failureCoordinates, hfailureGraph,
      hfailurePublic, _hfailureBoundaryEq⟩
  have hfailureActualToPublic :
      compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
          width tokenCount <=
        compactProofRootSequentFailureParserCoordinateBound
          inputWeight := by
    dsimp only [
      compactProofRootSequentFailureParserCoordinateBound,
      compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound,
      compactParserSyntaxExactEndpointPublicCoordinateSizeBound,
      sharedBound]
    exact
      FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.compactSequentFormulaStepPublicCoordinateSizeBound_mono
        hwidthValue htokenCountValue
  let failureActualBound :=
    compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
      width tokenCount
  have hfailureBounded :
      CompactParserSyntaxNoOutputExactEndpointBoundedGraph
        tokenTable width tokenCount failedStart failedFinish
          1 0 0 (2 ^ failureActualBound) :=
    failureEndpoint_bounded_of_public hfailureGraph hfailurePublic
  have hprefixPartsForCount := hprefixGraph
  rcases hprefixPartsForCount with
    ⟨_hprefixInputWitnessForCount, _hfirstWitnessForCount,
      _hfinalWitnessForCount, _htraceGraphForCount,
      _hfirstStartEntryForCount, _hfirstFinishEntryForCount,
      _hfinalStartEntryForCount, _hfinalFinishEntryForCount,
      _hprefixConsForCount, hprefixValueStructureForCount,
      _hprefixValueSizeEqForCount, _hprefixValueSizeForCount⟩
  have hvalueCountEq :
      prefixCoordinates.valueCount = formulaValues.length :=
    structuredList_count_eq_of_same_start
      hprefixValueStructureForCount hshared.valueStructure
  have hprefixInputPublicEq :
      prefixInput = prefixCoordinates.valueCount :: inputTail := by
    rw [hcanonical.prefixInput_eq, hvalueCountEq]
  have hfailedCoordinate :
      prefixCoordinates.valueCount < count := by
    rw [hvalueCountEq]
    exact hcanonical.failedIndex_lt
  have hpreparedSharedPublic :
      CompactProofRootSequentFailurePreparedSharedPublicBounds
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish prefixInputStart prefixInputFinish
          valueStart valueFinish inputWeight := by
    exact
      { tokenTable := hsharedPublic.tokenTable.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        width_size := hsharedPublic.width_size.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        width_value := by
          simpa only [sharedBound] using hwidthValue
        tokenCount_size := hsharedPublic.tokenCount_size.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        tokenCount_value := by
          simpa only [sharedBound] using htokenCountValue
        inputStart := hsharedPublic.rootInputStart.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        inputFinish := hsharedPublic.rootInputFinish.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        bodyStart := hsharedPublic.bodyStart.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        bodyFinish := hsharedPublic.bodyFinish.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        prefixInputStart := hsharedPublic.prefixInputStart.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        prefixInputFinish := hsharedPublic.prefixInputFinish.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        valueStart := hsharedPublic.valueStart.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        valueFinish := hsharedPublic.valueFinish.trans (by
          simpa only [sharedBound] using hsharedCoordinate) }
  refine
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, prefixInputStart, prefixInputFinish,
      valueStart, valueFinish, failedStart, failedFinish,
      prefixInput, formulaValues, prefixCoordinates, ?_⟩
  exact
    { inputLayout := by
        simpa only [input] using hshared.rootInputLayout
      bodyLayout := by
        simpa only [body] using hshared.bodyLayout
      prefixInputLayout := hshared.prefixInputLayout
      valueStructure := by
        simpa only [hvalueCountEq] using hprefixValueStructureForCount
      prefixGraph := hprefixGraph
      prefixPublic := hprefixPublic
      prefixBounded := by
        simpa only [prefixActualBound] using hprefixBounded
      failureBounded := by
        simpa only [failureActualBound] using hfailureBounded
      prefixActualToPublic := hprefixActualToPublic
      failureActualToPublic := hfailureActualToPublic
      prefixInput_eq := hprefixInputPublicEq
      failedIndex_lt := hfailedCoordinate
      sharedPublic := hpreparedSharedPublic }

set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootSequentFailureArithmeticBoundedGraph_of_cons_body_none_with_publicBounds
    (tag count : Nat) (inputTail : List Nat)
    (hparser :
      compactSequentTokenValueParser (count :: inputTail) = none) :
    let input := tag :: count :: inputTail
    let body := count :: inputTail
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount bodyStart bodyFinish body ∧
        CompactSequentFormulaNoOutputEndpointBoundedGraph
          tokenTable width tokenCount bodyStart bodyFinish
            (2 ^
              compactProofRootSequentFailureArithmeticCoordinateBound
                inputWeight) ∧
        CompactProofRootSequentFailureArithmeticPublicBounds
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish inputWeight := by
  let input := tag :: count :: inputTail
  let body := count :: inputTail
  let inputWeight := compactAdditiveValueWeight input
  rcases
      exists_compactProofRootSequentFailurePreparedPackage_of_cons_body_none_with_publicBounds
        tag count inputTail hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, prefixInputStart, prefixInputFinish,
      valueStart, valueFinish, failedStart, failedFinish,
      prefixInput, formulaValues, prefixCoordinates, hprepared⟩
  let sharedBound :=
    compactProofRootSequentFailureSharedCoordinateBound inputWeight
  let prefixActualBound :=
    compactSequentFormulaEndpointPublicCoordinateSizeBound
      width tokenCount
  let failureActualBound :=
    compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
      width tokenCount
  have hprefixGraph := hprepared.prefixGraph
  have hprefixPublic := hprepared.prefixPublic
  have hsharedPublic := hprepared.sharedPublic
  have hprefixActualToPublic := hprepared.prefixActualToPublic
  have hfailureActualToPublic := hprepared.failureActualToPublic
  have hwidthValue : width <= sharedBound := by
    simpa only [sharedBound] using hsharedPublic.width_value
  have htokenCountValue : tokenCount <= sharedBound := by
    simpa only [sharedBound] using hsharedPublic.tokenCount_value
  have hprefixBounded :
      CompactSequentFormulaEndpointBoundedGraph
        tokenTable width tokenCount prefixInputStart prefixInputFinish
          valueStart valueFinish failedStart failedFinish
            (2 ^ prefixActualBound) := by
    simpa only [prefixActualBound] using hprepared.prefixBounded
  have hfailureBounded :
      CompactParserSyntaxNoOutputExactEndpointBoundedGraph
        tokenTable width tokenCount failedStart failedFinish
          1 0 0 (2 ^ failureActualBound) := by
    simpa only [failureActualBound] using hprepared.failureBounded
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have hbodyWeight : compactAdditiveValueWeight body <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show body <:+ input from by simp [body, input])
  have hprefixParts := hprefixGraph
  rcases hprefixParts with
    ⟨hprefixInputWitness, hfirstWitness, _hfinalWitness,
      _htraceGraph, _hfirstStartEntry, _hfirstFinishEntry,
      _hfinalStartEntry, _hfinalFinishEntry, hprefixCons,
      hprefixValueStructure, _hprefixValueSizeEq,
      _hprefixValueSize⟩
  have hvalueCountEq :
      prefixCoordinates.valueCount = formulaValues.length :=
    structuredList_count_eq_of_same_start
      hprefixValueStructure hprepared.valueStructure
  rcases hprefixInputWitness.realize with
    ⟨prefixInputFromRows, hprefixInputCount,
      hprefixInputFromRowsLayout, hprefixInputRows⟩
  rcases hfirstWitness.realize with
    ⟨firstFromRows, hfirstCount,
      _hfirstFromRowsLayout, hfirstRows⟩
  have hprefixInputFromRowsEq : prefixInputFromRows = prefixInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hprepared.prefixInputLayout hprefixInputFromRowsLayout).1
  have hprefixCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount prefixCoordinates.firstBoundary
        firstFromRows.length prefixCoordinates.inputBoundary
        prefixInputFromRows.length prefixCoordinates.valueCount := by
    simpa only [hfirstCount, hprefixInputCount] using hprefixCons
  have hprefixInputFromRowsCons :
      prefixInputFromRows =
        prefixCoordinates.valueCount :: firstFromRows :=
    hprefixCons'.eq_cons_of_rows hfirstRows hprefixInputRows
  have hfirstFromRowsEq : firstFromRows = inputTail := by
    rw [hprefixInputFromRowsEq,
      hprepared.prefixInput_eq] at hprefixInputFromRowsCons
    simp only [List.cons.injEq] at hprefixInputFromRowsCons
    exact hprefixInputFromRowsCons.2.symm
  rcases
      CompactAdditiveNatListDirectLayout.exists_witnessRows
        hprepared.bodyLayout with
    ⟨bodyBoundary, bodyBoundarySize, hbodyWitness⟩
  rcases hbodyWitness.realize with
    ⟨bodyFromRows, hbodyCount, hbodyFromRowsLayout, hbodyRows⟩
  have hbodyFromRowsEq : bodyFromRows = body :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hprepared.bodyLayout hbodyFromRowsLayout).1
  subst bodyFromRows
  have hbodyEq : body = count :: firstFromRows := by
    simp [body, hfirstFromRowsEq]
  have hbodyCons : CompactAdditiveNatListConsRows
      tokenTable width tokenCount prefixCoordinates.firstBoundary
        firstFromRows.length bodyBoundary body.length count :=
    CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hfirstRows hbodyRows hbodyEq
  let arithmeticCoordinates :
      CompactSequentFormulaFailureArithmeticCoordinates :=
    { inputBoundary := bodyBoundary
      inputCount := body.length
      inputBoundarySize := bodyBoundarySize
      tailStart := prefixCoordinates.firstStart
      tailFinish := prefixCoordinates.firstFinish
      tailBoundary := prefixCoordinates.firstBoundary
      tailCount := prefixCoordinates.firstCount
      tailBoundarySize := prefixCoordinates.firstBoundarySize
      prefixInputStart := prefixInputStart
      prefixInputFinish := prefixInputFinish
      prefixInputBoundary := prefixCoordinates.inputBoundary
      prefixInputCount := prefixCoordinates.inputCount
      prefixInputBoundarySize := prefixCoordinates.inputBoundarySize
      count := count
      failedIndex := prefixCoordinates.valueCount
      valueStart := valueStart
      valueFinish := valueFinish
      failedStart := failedStart
      failedFinish := failedFinish
      prefixBound := 2 ^ prefixActualBound
      failureBound := 2 ^ failureActualBound }
  have harithmeticGraph :
      CompactSequentFormulaFailureArithmeticGraph
        tokenTable width tokenCount bodyStart bodyFinish
          arithmeticCoordinates := by
    unfold CompactSequentFormulaFailureArithmeticGraph
    dsimp only [arithmeticCoordinates]
    refine ⟨hbodyWitness, hfirstWitness, hprefixInputWitness,
      ?_, hprefixCons, ?_, hprefixBounded, hfailureBounded⟩
    · simpa only [hfirstCount, hbodyCount] using hbodyCons
    · exact hprepared.failedIndex_lt
  let boundaryBound :=
    compactProofRootSequentFailureBoundarySizeBound inputWeight
  have hbodyLength : body.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le body).trans hbodyWeight
  have hbodyArea :
      (body.length + 1) * tokenCount <= boundaryBound := by
    dsimp only [boundaryBound,
      compactProofRootSequentFailureBoundarySizeBound, sharedBound]
    exact Nat.mul_le_mul
      (Nat.add_le_add_right hbodyLength 1) htokenCountValue
  have hbodyBoundarySize :
      Nat.size bodyBoundary <= boundaryBound := by
    rw [← hbodyWitness.2.2.1]
    exact hbodyWitness.2.2.2.trans hbodyArea
  have hbodyCountSize : Nat.size body.length <= inputWeight :=
    natSize_le_of_le hbodyLength
  have hbodyBoundarySizeSize :
      Nat.size bodyBoundarySize <= boundaryBound :=
    (natSize_le_of_le hbodyWitness.2.2.2).trans hbodyArea
  let prefixPublicBound :=
    compactProofRootSequentFailurePrefixCoordinateBound inputWeight
  have hprefixSize
      {value : Nat}
      (hvalue :
        value ∈
          compactSequentFormulaEndpointCoordinateValues
            prefixCoordinates) :
      Nat.size value <= prefixPublicBound :=
    (hprefixPublic.value_size_le value hvalue).trans
      (by simpa only [prefixPublicBound] using hprefixActualToPublic)
  have hprefixInputStartSize :
      Nat.size prefixInputStart <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.prefixInputStart
  have hprefixInputFinishSize :
      Nat.size prefixInputFinish <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.prefixInputFinish
  have hvalueStartSize : Nat.size valueStart <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.valueStart
  have hvalueFinishSize : Nat.size valueFinish <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.valueFinish
  have hfailedStartSize : Nat.size failedStart <= prefixPublicBound :=
    hprefixPublic.finalStart_size_le.trans
      (by simpa only [prefixPublicBound] using hprefixActualToPublic)
  have hfailedFinishSize : Nat.size failedFinish <= prefixPublicBound :=
    hprefixPublic.finalFinish_size_le.trans
      (by simpa only [prefixPublicBound] using hprefixActualToPublic)
  have hcountWeight :
      compactAdditiveValueWeight count <= inputWeight :=
    compactAdditiveValueWeight_nat_mem_le
      (show count ∈ input from by simp [input])
  have hcountSize : Nat.size count <= inputWeight := by
    simpa only [compactAdditiveValueWeight_nat] using
      (Nat.le_trans (Nat.le_add_right (Nat.size count) 1) hcountWeight)
  let failurePublicBound :=
    compactProofRootSequentFailureParserCoordinateBound inputWeight
  let arithmeticBound :=
    compactProofRootSequentFailureArithmeticCoordinateBound inputWeight
  have htoArithmeticBoundary : boundaryBound <= arithmeticBound := by
    dsimp only [boundaryBound, arithmeticBound,
      compactProofRootSequentFailureArithmeticCoordinateBound]
    omega
  have htoArithmeticShared : sharedBound <= arithmeticBound := by
    have hfactor : 1 <= inputWeight + 1 := by omega
    have hscaled :
        sharedBound <= (inputWeight + 1) * sharedBound := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right sharedBound hfactor
    have hsharedBoundary : sharedBound <= boundaryBound := by
      simpa only [boundaryBound,
        compactProofRootSequentFailureBoundarySizeBound,
        sharedBound] using hscaled
    exact hsharedBoundary.trans htoArithmeticBoundary
  have htoArithmeticPrefix : prefixPublicBound <= arithmeticBound := by
    dsimp only [prefixPublicBound, arithmeticBound,
      compactProofRootSequentFailureArithmeticCoordinateBound]
    omega
  have htoArithmeticFailure : failurePublicBound <= arithmeticBound := by
    dsimp only [failurePublicBound, arithmeticBound,
      compactProofRootSequentFailureArithmeticCoordinateBound]
    omega
  have htoArithmeticInput : inputWeight <= arithmeticBound := by
    dsimp only [arithmeticBound,
      compactProofRootSequentFailureArithmeticCoordinateBound]
    omega
  have hprefixEndpointBoundSize :
      Nat.size (2 ^ prefixActualBound) <= arithmeticBound := by
    rw [Nat.size_pow]
    have hactual : prefixActualBound <= prefixPublicBound := by
      simpa only [prefixActualBound, prefixPublicBound] using
        hprefixActualToPublic
    exact (Nat.add_le_add_right hactual 1).trans (by
      dsimp only [arithmeticBound,
        compactProofRootSequentFailureArithmeticCoordinateBound]
      omega)
  have hfailureEndpointBoundSize :
      Nat.size (2 ^ failureActualBound) <= arithmeticBound := by
    rw [Nat.size_pow]
    have hactual : failureActualBound <= failurePublicBound := by
      simpa only [failureActualBound, failurePublicBound] using
        hfailureActualToPublic
    exact (Nat.add_le_add_right hactual 1).trans (by
      dsimp only [arithmeticBound,
        compactProofRootSequentFailureArithmeticCoordinateBound]
      omega)
  have harithmeticBounded :
      CompactSequentFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount bodyStart bodyFinish
          (2 ^ arithmeticBound) := by
    unfold CompactSequentFormulaFailureEndpointBoundedGraph
    have hprefixSmall
        {value : Nat}
        (hvalue :
          value ∈
            compactSequentFormulaEndpointCoordinateValues
              prefixCoordinates) :
        value <= 2 ^ arithmeticBound :=
      nat_le_two_pow_of_size_le
        ((hprefixSize hvalue).trans htoArithmeticPrefix)
    refine
      ⟨bodyBoundary,
          nat_le_two_pow_of_size_le
            (hbodyBoundarySize.trans htoArithmeticBoundary),
        body.length,
          nat_le_two_pow_of_size_le
            (hbodyCountSize.trans htoArithmeticInput),
        bodyBoundarySize,
          nat_le_two_pow_of_size_le
            (hbodyBoundarySizeSize.trans htoArithmeticBoundary),
        prefixCoordinates.firstStart,
          hprefixSmall (by
            simp [compactSequentFormulaEndpointCoordinateValues]),
        prefixCoordinates.firstFinish,
          hprefixSmall (by
            simp [compactSequentFormulaEndpointCoordinateValues]),
        prefixCoordinates.firstBoundary,
          hprefixSmall (by
            simp [compactSequentFormulaEndpointCoordinateValues]),
        prefixCoordinates.firstCount,
          hprefixSmall (by
            simp [compactSequentFormulaEndpointCoordinateValues]),
        prefixCoordinates.firstBoundarySize,
          hprefixSmall (by
            simp [compactSequentFormulaEndpointCoordinateValues]),
        prefixInputStart,
          nat_le_two_pow_of_size_le
            (hprefixInputStartSize.trans htoArithmeticShared),
        prefixInputFinish,
          nat_le_two_pow_of_size_le
            (hprefixInputFinishSize.trans htoArithmeticShared),
        prefixCoordinates.inputBoundary,
          hprefixSmall (by
            simp [compactSequentFormulaEndpointCoordinateValues]),
        prefixCoordinates.inputCount,
          hprefixSmall (by
            simp [compactSequentFormulaEndpointCoordinateValues]),
        prefixCoordinates.inputBoundarySize,
          hprefixSmall (by
            simp [compactSequentFormulaEndpointCoordinateValues]),
        count,
          nat_le_two_pow_of_size_le
            (hcountSize.trans htoArithmeticInput),
        prefixCoordinates.valueCount,
          hprefixSmall (by
            simp [compactSequentFormulaEndpointCoordinateValues]),
        valueStart,
          nat_le_two_pow_of_size_le
            (hvalueStartSize.trans htoArithmeticShared),
        valueFinish,
          nat_le_two_pow_of_size_le
            (hvalueFinishSize.trans htoArithmeticShared),
        failedStart,
          nat_le_two_pow_of_size_le
            (hfailedStartSize.trans htoArithmeticPrefix),
        failedFinish,
          nat_le_two_pow_of_size_le
            (hfailedFinishSize.trans htoArithmeticPrefix),
        2 ^ prefixActualBound,
          nat_le_two_pow_of_size_le hprefixEndpointBoundSize,
        2 ^ failureActualBound,
          nat_le_two_pow_of_size_le hfailureEndpointBoundSize,
        by simpa only [
          arithmeticCoordinates,
          compactSequentFormulaFailureArithmeticCoordinatesOfValues]
            using harithmeticGraph⟩
  have hsequent :
      CompactSequentFormulaNoOutputEndpointBoundedGraph
        tokenTable width tokenCount bodyStart bodyFinish
          (2 ^ arithmeticBound) :=
    Or.inr harithmeticBounded
  have htableShared : Nat.size tokenTable <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.tokenTable
  have hwidthSizeShared : Nat.size width <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.width_size
  have htokenCountSizeShared : Nat.size tokenCount <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.tokenCount_size
  have hinputStartShared : Nat.size inputStart <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.inputStart
  have hinputFinishShared : Nat.size inputFinish <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.inputFinish
  have hbodyStartShared : Nat.size bodyStart <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.bodyStart
  have hbodyFinishShared : Nat.size bodyFinish <= sharedBound :=
    by simpa only [sharedBound] using hsharedPublic.bodyFinish
  refine ⟨tokenTable, width, tokenCount,
    inputStart, inputFinish, bodyStart, bodyFinish,
    by simpa only [input] using hprepared.inputLayout,
    by simpa only [body] using hprepared.bodyLayout,
    ?_, ?_⟩
  · simpa only [arithmeticBound] using hsequent
  · exact
      { tokenTable := by
          simpa only [sharedBound] using htableShared
        width_size := by
          simpa only [sharedBound] using hwidthSizeShared
        width_value := by
          simpa only [sharedBound] using hwidthValue
        tokenCount_size := by
          simpa only [sharedBound] using htokenCountSizeShared
        tokenCount_value := by
          simpa only [sharedBound] using htokenCountValue
        inputStart := by
          simpa only [sharedBound] using hinputStartShared
        inputFinish := by
          simpa only [sharedBound] using hinputFinishShared
        bodyStart := by
          simpa only [sharedBound] using hbodyStartShared
        bodyFinish := by
          simpa only [sharedBound] using hbodyFinishShared }

set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootSequentFailureRootRowsPackage_of_cons_body_none_with_publicBounds
    (tag count : Nat) (inputTail : List Nat) (htag : tag <= 9)
    (hparser :
      compactSequentTokenValueParser (count :: inputTail) = none) :
    let input := tag :: count :: inputTail
    let body := count :: inputTail
    let inputWeight := compactAdditiveValueWeight input
    let arithmeticBound :=
      compactProofRootSequentFailureArithmeticCoordinateBound inputWeight
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ inputBoundary inputBoundarySize bodyBoundary bodyBoundarySize,
      CompactProofRootSequentFailureRootRowsPackage
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish inputBoundary inputBoundarySize
          bodyBoundary bodyBoundarySize tag arithmeticBound inputWeight
          input body := by
  let input := tag :: count :: inputTail
  let body := count :: inputTail
  let inputWeight := compactAdditiveValueWeight input
  rcases
      exists_compactProofRootSequentFailureArithmeticBoundedGraph_of_cons_body_none_with_publicBounds
        tag count inputTail hparser with
    ⟨tokenTable, width, tokenCount,
      inputStart, inputFinish, bodyStart, bodyFinish,
      hinputLayout, hbodyLayout, hsequentRaw, harithmeticPublic⟩
  let arithmeticBound :=
    compactProofRootSequentFailureArithmeticCoordinateBound inputWeight
  have hsequent :
      CompactSequentFormulaNoOutputEndpointBoundedGraph
        tokenTable width tokenCount bodyStart bodyFinish
          (2 ^ arithmeticBound) := by
    simpa only [arithmeticBound] using hsequentRaw
  rcases
      CompactAdditiveNatListDirectLayout.exists_witnessRows hbodyLayout with
    ⟨bodyBoundary, bodyBoundarySize, hbodyWitness⟩
  rcases hbodyWitness.realize with
    ⟨bodyFromRows, hbodyCount, hbodyFromRowsLayout, hbodyRows⟩
  have hbodyFromRowsEq : bodyFromRows = body :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hbodyLayout hbodyFromRowsLayout).1
  subst bodyFromRows
  rcases
      CompactAdditiveNatListDirectLayout.exists_witnessRows
        hinputLayout with
    ⟨inputBoundary, inputBoundarySize, hinputWitness⟩
  rcases hinputWitness.realize with
    ⟨inputFromRows, hinputCount, hinputFromRowsLayout, hinputRows⟩
  have hinputFromRowsEq : inputFromRows = input :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hinputLayout hinputFromRowsLayout).1
  subst inputFromRows
  have hrootEq : input = tag :: body := by
    simp [input, body]
  have hrootCons : CompactAdditiveNatListConsRows
      tokenTable width tokenCount bodyBoundary body.length
        inputBoundary input.length tag :=
    CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hbodyRows hinputRows hrootEq
  refine
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, inputBoundary, inputBoundarySize,
      bodyBoundary, bodyBoundarySize, ?_⟩
  exact
    { inputLayout := hinputLayout
      inputWitness := hinputWitness
      bodyWitness := hbodyWitness
      rootCons := hrootCons
      tag_le := htag
      sequent := hsequent
      arithmeticPublic := harithmeticPublic }

set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootSequentFailureRootGraphPackage_of_cons_body_none_with_publicBounds
    (tag count : Nat) (inputTail : List Nat) (htag : tag <= 9)
    (hparser :
      compactSequentTokenValueParser (count :: inputTail) = none) :
    let input := tag :: count :: inputTail
    let body := count :: inputTail
    let inputWeight := compactAdditiveValueWeight input
    let arithmeticBound :=
      compactProofRootSequentFailureArithmeticCoordinateBound inputWeight
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ inputBoundary inputBoundarySize bodyBoundary bodyBoundarySize,
      CompactProofRootSequentFailureRootRowsPackage
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish inputBoundary inputBoundarySize
            bodyBoundary bodyBoundarySize tag arithmeticBound inputWeight
            input body ∧
        CompactProofRootSequentFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish
            { inputBoundary := inputBoundary
              inputCount := input.length
              inputBoundarySize := inputBoundarySize
              bodyBoundary := bodyBoundary
              bodyCount := body.length
              bodyBoundarySize := bodyBoundarySize
              tag := tag
              sequentBound := 2 ^ arithmeticBound } := by
  let input := tag :: count :: inputTail
  let body := count :: inputTail
  let inputWeight := compactAdditiveValueWeight input
  let arithmeticBound :=
    compactProofRootSequentFailureArithmeticCoordinateBound inputWeight
  rcases
      exists_compactProofRootSequentFailureRootRowsPackage_of_cons_body_none_with_publicBounds
        tag count inputTail htag hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, inputBoundary, inputBoundarySize,
      bodyBoundary, bodyBoundarySize, hrootRows⟩
  have hinputLayout := hrootRows.inputLayout
  have hinputWitness := hrootRows.inputWitness
  have hbodyWitness := hrootRows.bodyWitness
  have hrootCons := hrootRows.rootCons
  have hsequent := hrootRows.sequent
  let rootCoordinates :
      CompactProofRootSequentFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := inputBoundarySize
      bodyBoundary := bodyBoundary
      bodyCount := body.length
      bodyBoundarySize := bodyBoundarySize
      tag := tag
      sequentBound := 2 ^ arithmeticBound }
  have hrootGraph :
      CompactProofRootSequentFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish rootCoordinates := by
    unfold CompactProofRootSequentFailureEndpointGraph
    dsimp only [rootCoordinates]
    exact ⟨hinputWitness, hbodyWitness,
      hrootRows.tag_le, hrootCons, hsequent⟩
  refine
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, inputBoundary, inputBoundarySize,
      bodyBoundary, bodyBoundarySize, hrootRows, ?_⟩
  simpa only [rootCoordinates] using hrootGraph

set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootSequentFailureEndpointSizePackage_of_cons_body_none_with_publicBounds
    (tag count : Nat) (inputTail : List Nat) (htag : tag <= 9)
    (hparser :
      compactSequentTokenValueParser (count :: inputTail) = none) :
    let input := tag :: count :: inputTail
    let inputWeight := compactAdditiveValueWeight input
    let rootBound :=
      compactProofRootSequentFailureRootCoordinateBound inputWeight
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootSequentFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSequentFailureArithmeticPublicBounds
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish inputWeight ∧
        CompactProofRootSequentFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish coordinates ∧
        CompactProofRootSequentFailureEndpointCoordinateSizeBounds
          coordinates rootBound := by
  let input := tag :: count :: inputTail
  let body := count :: inputTail
  let inputWeight := compactAdditiveValueWeight input
  let sharedBound :=
    compactProofRootSequentFailureSharedCoordinateBound inputWeight
  let boundaryBound :=
    compactProofRootSequentFailureBoundarySizeBound inputWeight
  let arithmeticBound :=
    compactProofRootSequentFailureArithmeticCoordinateBound inputWeight
  rcases
      exists_compactProofRootSequentFailureRootGraphPackage_of_cons_body_none_with_publicBounds
        tag count inputTail htag hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, inputBoundary, inputBoundarySize,
      bodyBoundary, bodyBoundarySize, hrootRows, hrootGraphRaw⟩
  have hinputLayout := hrootRows.inputLayout
  have hinputWitness := hrootRows.inputWitness
  have hbodyWitness := hrootRows.bodyWitness
  have harithmeticPublic := hrootRows.arithmeticPublic
  have htokenCountValue : tokenCount <= sharedBound := by
    simpa only [sharedBound] using harithmeticPublic.tokenCount_value
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have hbodyWeight : compactAdditiveValueWeight body <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show body <:+ input from by simp [body, input])
  have hbodyLength : body.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le body).trans hbodyWeight
  let rootCoordinates :
      CompactProofRootSequentFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := inputBoundarySize
      bodyBoundary := bodyBoundary
      bodyCount := body.length
      bodyBoundarySize := bodyBoundarySize
      tag := tag
      sequentBound := 2 ^ arithmeticBound }
  have hrootGraph :
      CompactProofRootSequentFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish rootCoordinates := by
    simpa only [rootCoordinates] using hrootGraphRaw
  have hinputArea :
      (input.length + 1) * tokenCount <= boundaryBound := by
    dsimp only [boundaryBound,
      compactProofRootSequentFailureBoundarySizeBound, sharedBound]
    exact Nat.mul_le_mul
      (Nat.add_le_add_right hinputLength 1) htokenCountValue
  have hinputBoundarySize :
      Nat.size inputBoundary <= boundaryBound := by
    rw [← hinputWitness.2.2.1]
    exact hinputWitness.2.2.2.trans hinputArea
  have hinputCountSize : Nat.size input.length <= inputWeight :=
    natSize_le_of_le hinputLength
  have hinputBoundarySizeSize :
      Nat.size inputBoundarySize <= boundaryBound :=
    (natSize_le_of_le hinputWitness.2.2.2).trans hinputArea
  have hbodyArea :
      (body.length + 1) * tokenCount <= boundaryBound := by
    dsimp only [boundaryBound,
      compactProofRootSequentFailureBoundarySizeBound, sharedBound]
    exact Nat.mul_le_mul
      (Nat.add_le_add_right hbodyLength 1) htokenCountValue
  have hbodyBoundarySize :
      Nat.size bodyBoundary <= boundaryBound := by
    rw [← hbodyWitness.2.2.1]
    exact hbodyWitness.2.2.2.trans hbodyArea
  have hbodyCountSize : Nat.size body.length <= inputWeight :=
    natSize_le_of_le hbodyLength
  have hbodyBoundarySizeSize :
      Nat.size bodyBoundarySize <= boundaryBound :=
    (natSize_le_of_le hbodyWitness.2.2.2).trans hbodyArea
  have htagWeight :
      compactAdditiveValueWeight tag <= inputWeight :=
    compactAdditiveValueWeight_nat_mem_le
      (show tag ∈ input from by simp [input])
  have htagSize : Nat.size tag <= inputWeight := by
    simpa only [compactAdditiveValueWeight_nat] using
      (Nat.le_trans (Nat.le_add_right (Nat.size tag) 1) htagWeight)
  let rootBound :=
    compactProofRootSequentFailureRootCoordinateBound inputWeight
  have htoRootBoundary : boundaryBound <= rootBound := by
    simpa only [boundaryBound, rootBound] using
      compactProofRootSequentFailureBoundary_le_root inputWeight
  have htoRootInput : inputWeight <= rootBound := by
    simpa only [rootBound] using
      compactProofRootSequentFailureInput_le_root inputWeight
  have hsequentBoundSize :
      Nat.size (2 ^ arithmeticBound) <= rootBound := by
    simpa only [arithmeticBound, rootBound] using
      compactProofRootSequentFailureArithmeticPow_size_le_root
        inputWeight
  have hrootSize :
      CompactProofRootSequentFailureEndpointCoordinateSizeBounds
        rootCoordinates rootBound := by
    exact
      { inputBoundary :=
          hinputBoundarySize.trans htoRootBoundary
        inputCount :=
          hinputCountSize.trans htoRootInput
        inputBoundarySize :=
          hinputBoundarySizeSize.trans htoRootBoundary
        bodyBoundary :=
          hbodyBoundarySize.trans htoRootBoundary
        bodyCount :=
          hbodyCountSize.trans htoRootInput
        bodyBoundarySize :=
          hbodyBoundarySizeSize.trans htoRootBoundary
        tag :=
          htagSize.trans htoRootInput
        sequentBound := hsequentBoundSize }
  refine
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, rootCoordinates,
      by simpa only [input] using hinputLayout,
      harithmeticPublic, hrootGraph, hrootSize⟩

set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootSequentFailureEndpointBoundedCore_of_cons_body_none_with_publicBounds
    (tag count : Nat) (inputTail : List Nat) (htag : tag <= 9)
    (hparser :
      compactSequentTokenValueParser (count :: inputTail) = none) :
    let input := tag :: count :: inputTail
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSequentFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish
            (2 ^
              compactProofRootSequentFailureRootCoordinateBound
                inputWeight) ∧
        CompactProofRootSequentFailureArithmeticPublicBounds
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish inputWeight := by
  let input := tag :: count :: inputTail
  let inputWeight := compactAdditiveValueWeight input
  let rootBound :=
    compactProofRootSequentFailureRootCoordinateBound inputWeight
  rcases
      exists_compactProofRootSequentFailureEndpointSizePackage_of_cons_body_none_with_publicBounds
        tag count inputTail htag hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, hinputLayout,
      harithmeticPublic, hrootGraph, hrootSize⟩
  refine
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish,
      by simpa only [input] using hinputLayout, ?_,
      harithmeticPublic⟩
  simpa only [rootBound] using
    rootEndpoint_bounded_of_sizeBounds hrootGraph hrootSize

set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootSequentFailureEndpointBoundedGraph_of_cons_body_none_with_publicBounds
    (tag count : Nat) (inputTail : List Nat) (htag : tag <= 9)
    (hparser :
      compactSequentTokenValueParser (count :: inputTail) = none) :
    let input := tag :: count :: inputTail
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSequentFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound ∧
        CompactProofRootSequentFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound
            (compactProofRootSequentFailurePublicCoordinateSizeBound
              inputWeight) := by
  let input := tag :: count :: inputTail
  let inputWeight := compactAdditiveValueWeight input
  let sharedBound :=
    compactProofRootSequentFailureSharedCoordinateBound inputWeight
  let rootBound :=
    compactProofRootSequentFailureRootCoordinateBound inputWeight
  let endpointBound := 2 ^ rootBound
  rcases
      exists_compactProofRootSequentFailureEndpointBoundedCore_of_cons_body_none_with_publicBounds
        tag count inputTail htag hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, hinputLayout,
      hrootBoundedRaw, harithmeticPublic⟩
  have hrootBounded :
      CompactProofRootSequentFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
    simpa only [endpointBound, rootBound] using hrootBoundedRaw
  let publicBound :=
    compactProofRootSequentFailurePublicCoordinateSizeBound inputWeight
  have hsharedToPublic : sharedBound <= publicBound := by
    simpa only [sharedBound, publicBound] using
      compactProofRootSequentFailureShared_le_public inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound :=
    (show Nat.size tokenTable <= sharedBound from by
      simpa only [sharedBound] using
        harithmeticPublic.tokenTable).trans hsharedToPublic
  have hwidthPublic : Nat.size width <= publicBound :=
    (show Nat.size width <= sharedBound from by
      simpa only [sharedBound] using
        harithmeticPublic.width_size).trans hsharedToPublic
  have htokenCountPublic : Nat.size tokenCount <= publicBound :=
    (show Nat.size tokenCount <= sharedBound from by
      simpa only [sharedBound] using
        harithmeticPublic.tokenCount_size).trans hsharedToPublic
  have hinputStartPublic : Nat.size inputStart <= publicBound :=
    (show Nat.size inputStart <= sharedBound from by
      simpa only [sharedBound] using
        harithmeticPublic.inputStart).trans hsharedToPublic
  have hinputFinishPublic : Nat.size inputFinish <= publicBound :=
    (show Nat.size inputFinish <= sharedBound from by
      simpa only [sharedBound] using
        harithmeticPublic.inputFinish).trans hsharedToPublic
  have hbodyStartPublic : Nat.size bodyStart <= publicBound :=
    (show Nat.size bodyStart <= sharedBound from by
      simpa only [sharedBound] using
        harithmeticPublic.bodyStart).trans hsharedToPublic
  have hbodyFinishPublic : Nat.size bodyFinish <= publicBound :=
    (show Nat.size bodyFinish <= sharedBound from by
      simpa only [sharedBound] using
        harithmeticPublic.bodyFinish).trans hsharedToPublic
  have hendpointPublic : Nat.size endpointBound <= publicBound := by
    simpa only [endpointBound, rootBound, publicBound] using
      compactProofRootSequentFailureRootPow_size_le_public
        inputWeight
  refine ⟨tokenTable, width, tokenCount,
    inputStart, inputFinish, bodyStart, bodyFinish, endpointBound,
    by simpa only [input] using hinputLayout,
    hrootBounded, ?_⟩
  exact
    { tokenTable := htablePublic
      width := hwidthPublic
      tokenCount := htokenCountPublic
      inputStart := hinputStartPublic
      inputFinish := hinputFinishPublic
      bodyStart := hbodyStartPublic
      bodyFinish := hbodyFinishPublic
      endpointBound := hendpointPublic }

set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootSequentFailureEndpointBoundedGraph_of_empty_body_with_publicBounds
    (tag : Nat) (htag : tag <= 9) :
    let input := [tag]
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSequentFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound ∧
        CompactProofRootSequentFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound
            (compactProofRootSequentFailurePublicCoordinateSizeBound
              inputWeight) := by
  let input := [tag]
  let body := ([] : List Nat)
  let prefixInput := ([] : List Nat)
  let suffixes := ([] : List (List Nat))
  let formulaValues := ([] : List (List Nat))
  let parserTraces :=
    ([] : List CompactFormulaTokenParserDirectTrace)
  let failureStates := ([] : CompactFormulaTokenParserDirectTrace)
  let inputWeight := compactAdditiveValueWeight input
  have hbodyWeight :
      compactAdditiveValueWeight body <= inputWeight :=
    compactAdditiveValueWeight_suffix_le
      (show body <:+ input from by simp [body, input])
  have hinputPositive : 1 <= inputWeight := by
    simpa only [inputWeight] using
      compactAdditiveValueWeight_list_pos input
  have hinputSquare : inputWeight <= inputWeight * inputWeight := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right inputWeight hinputPositive
  have hprefixWeight :
      compactAdditiveValueWeight prefixInput <=
        compactProofRootSequentFailurePrefixInputWeightBound
          inputWeight := by
    have hempty :
        compactAdditiveValueWeight prefixInput = 1 := by
      simp [prefixInput]
    rw [hempty]
    unfold compactProofRootSequentFailurePrefixInputWeightBound
    omega
  have hsuffixWeight :
      compactAdditiveValueWeight suffixes <=
        compactSequentFormulaCanonicalSuffixesWeightBound
          (compactProofRootSequentFailurePrefixInputWeightBound
            inputWeight) := by
    simp [suffixes,
      compactSequentFormulaCanonicalSuffixesWeightBound]
    omega
  have hformulaValuesWeight :
      compactAdditiveValueWeight formulaValues <=
        compactNumericNestedListWeightBound inputWeight := by
    simp [formulaValues, compactNumericNestedListWeightBound]
    omega
  have hparserWeight :
      compactAdditiveValueWeight parserTraces <=
        compactSequentFormulaCanonicalParserTracesWeightBound
          (compactProofRootSequentFailurePrefixInputWeightBound
            inputWeight) := by
    simp [parserTraces,
      compactSequentFormulaCanonicalParserTracesWeightBound,
      compactNumericRootSyntaxParserTraceWeightBound,
      compactNumericFormulaParserTraceWeightBound]
    omega
  have hfailureWeight :
      compactAdditiveValueWeight failureStates <=
        compactNumericRootSyntaxParserTraceWeightBound inputWeight := by
    simp [failureStates,
      compactNumericRootSyntaxParserTraceWeightBound,
      compactNumericFormulaParserTraceWeightBound]
    omega
  rcases
      exists_compactProofRootSequentFailureSharedRows_with_publicBounds
        input body prefixInput suffixes formulaValues
          parserTraces failureStates with
    ⟨tokenTable, width, tokenCount,
      inputStart, inputFinish, bodyStart, bodyFinish,
      _prefixInputStart, _prefixInputFinish,
      _valueStart, _valueFinish,
      _failureStateStart, _failureStateFinish,
      _suffixBoundary, _valueBoundary, _failureStateBoundary,
      hshared, hsharedPublic⟩
  have hsharedDataWeight :
      compactProofRootSequentFailureSharedDataWeight
          input body prefixInput suffixes formulaValues
            parserTraces failureStates <=
        compactProofRootSequentFailureSharedDataWeightBound
          inputWeight := by
    unfold compactProofRootSequentFailureSharedDataWeight
      compactProofRootSequentFailureSharedDataWeightBound
    omega
  have hsharedCoordinate :
      compactProofRootSequentFailureSharedCoordinateSizeBound
          (compactProofRootSequentFailureSharedDataWeight
            input body prefixInput suffixes formulaValues
              parserTraces failureStates) <=
        compactProofRootSequentFailureSharedCoordinateBound
          inputWeight := by
    unfold compactProofRootSequentFailureSharedCoordinateBound
    exact
      compactProofRootSequentFailureSharedCoordinateSizeBound_mono
        hsharedDataWeight
  let sharedBound :=
    compactProofRootSequentFailureSharedCoordinateBound inputWeight
  let boundaryBound :=
    compactProofRootSequentFailureBoundarySizeBound inputWeight
  let arithmeticBound :=
    compactProofRootSequentFailureArithmeticCoordinateBound inputWeight
  let rootBound :=
    compactProofRootSequentFailureRootCoordinateBound inputWeight
  let endpointBound := 2 ^ rootBound
  let publicBound :=
    compactProofRootSequentFailurePublicCoordinateSizeBound inputWeight
  have htokenCountValue : tokenCount <= sharedBound :=
    hsharedPublic.tokenCount_value.trans (by
      simpa only [sharedBound] using hsharedCoordinate)
  have harithmeticPublic :
      CompactProofRootSequentFailureArithmeticPublicBounds
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish inputWeight := by
    exact
      { tokenTable := hsharedPublic.tokenTable.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        width_size := hsharedPublic.width_size.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        width_value := hsharedPublic.width_value.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        tokenCount_size := hsharedPublic.tokenCount_size.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        tokenCount_value := htokenCountValue
        inputStart := hsharedPublic.rootInputStart.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        inputFinish := hsharedPublic.rootInputFinish.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        bodyStart := hsharedPublic.bodyStart.trans (by
          simpa only [sharedBound] using hsharedCoordinate)
        bodyFinish := hsharedPublic.bodyFinish.trans (by
          simpa only [sharedBound] using hsharedCoordinate) }
  rcases
      CompactAdditiveNatListDirectLayout.exists_witnessRows
        hshared.bodyLayout with
    ⟨bodyBoundary, bodyBoundarySize, hbodyWitness⟩
  rcases hbodyWitness.realize with
    ⟨bodyFromRows, _hbodyCount, hbodyFromRowsLayout, hbodyRows⟩
  have hbodyFromRowsEq : bodyFromRows = body :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hshared.bodyLayout hbodyFromRowsLayout).1
  subst bodyFromRows
  rcases
      CompactAdditiveNatListDirectLayout.exists_witnessRows
        hshared.rootInputLayout with
    ⟨inputBoundary, inputBoundarySize, hinputWitness⟩
  rcases hinputWitness.realize with
    ⟨inputFromRows, _hinputCount, hinputFromRowsLayout, hinputRows⟩
  have hinputFromRowsEq : inputFromRows = input :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hshared.rootInputLayout hinputFromRowsLayout).1
  subst inputFromRows
  have hrootEq : input = tag :: body := by
    simp [input, body]
  have hrootCons : CompactAdditiveNatListConsRows
      tokenTable width tokenCount bodyBoundary body.length
        inputBoundary input.length tag :=
    CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hbodyRows hinputRows hrootEq
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have hbodyLength : body.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le body).trans
      hbodyWeight
  have hinputArea :
      (input.length + 1) * tokenCount <= boundaryBound := by
    dsimp only [boundaryBound,
      compactProofRootSequentFailureBoundarySizeBound, sharedBound]
    exact Nat.mul_le_mul
      (Nat.add_le_add_right hinputLength 1) htokenCountValue
  have hbodyArea :
      (body.length + 1) * tokenCount <= boundaryBound := by
    dsimp only [boundaryBound,
      compactProofRootSequentFailureBoundarySizeBound, sharedBound]
    exact Nat.mul_le_mul
      (Nat.add_le_add_right hbodyLength 1) htokenCountValue
  have hinputBoundarySize :
      Nat.size inputBoundary <= boundaryBound := by
    rw [← hinputWitness.2.2.1]
    exact hinputWitness.2.2.2.trans hinputArea
  have hinputBoundarySizeSize :
      Nat.size inputBoundarySize <= boundaryBound :=
    (natSize_le_of_le hinputWitness.2.2.2).trans hinputArea
  have hbodyBoundarySize :
      Nat.size bodyBoundary <= boundaryBound := by
    rw [← hbodyWitness.2.2.1]
    exact hbodyWitness.2.2.2.trans hbodyArea
  have hbodyBoundarySizeSize :
      Nat.size bodyBoundarySize <= boundaryBound :=
    (natSize_le_of_le hbodyWitness.2.2.2).trans hbodyArea
  have hboundaryToArithmetic : boundaryBound <= arithmeticBound := by
    simpa only [boundaryBound, arithmeticBound] using
      compactProofRootSequentFailureBoundary_le_arithmetic
        inputWeight
  have hsequent :
      CompactSequentFormulaNoOutputEndpointBoundedGraph
        tokenTable width tokenCount bodyStart bodyFinish
          (2 ^ arithmeticBound) := by
    apply Or.inl
    refine
      ⟨bodyBoundary,
        nat_le_two_pow_of_size_le
          (hbodyBoundarySize.trans hboundaryToArithmetic),
        bodyBoundarySize,
        nat_le_two_pow_of_size_le
          (hbodyBoundarySizeSize.trans hboundaryToArithmetic), ?_⟩
    simpa [body] using hbodyWitness
  let rootCoordinates :
      CompactProofRootSequentFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := inputBoundarySize
      bodyBoundary := bodyBoundary
      bodyCount := body.length
      bodyBoundarySize := bodyBoundarySize
      tag := tag
      sequentBound := 2 ^ arithmeticBound }
  have hrootGraph :
      CompactProofRootSequentFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish rootCoordinates := by
    unfold CompactProofRootSequentFailureEndpointGraph
    dsimp only [rootCoordinates]
    exact ⟨hinputWitness, hbodyWitness, htag, hrootCons, hsequent⟩
  have hinputCountSize : Nat.size input.length <= inputWeight :=
    natSize_le_of_le hinputLength
  have hbodyCountSize : Nat.size body.length <= inputWeight :=
    natSize_le_of_le hbodyLength
  have htagWeight :
      compactAdditiveValueWeight tag <= inputWeight :=
    compactAdditiveValueWeight_nat_mem_le
      (show tag ∈ input from by simp [input])
  have htagSize : Nat.size tag <= inputWeight := by
    simpa only [compactAdditiveValueWeight_nat] using
      (Nat.le_trans (Nat.le_add_right (Nat.size tag) 1) htagWeight)
  have htoRootBoundary : boundaryBound <= rootBound := by
    simpa only [boundaryBound, rootBound] using
      compactProofRootSequentFailureBoundary_le_root inputWeight
  have htoRootInput : inputWeight <= rootBound := by
    simpa only [rootBound] using
      compactProofRootSequentFailureInput_le_root inputWeight
  have hsequentBoundSize :
      Nat.size (2 ^ arithmeticBound) <= rootBound := by
    simpa only [arithmeticBound, rootBound] using
      compactProofRootSequentFailureArithmeticPow_size_le_root
        inputWeight
  have hrootSize :
      CompactProofRootSequentFailureEndpointCoordinateSizeBounds
        rootCoordinates rootBound := by
    exact
      { inputBoundary :=
          hinputBoundarySize.trans htoRootBoundary
        inputCount :=
          hinputCountSize.trans htoRootInput
        inputBoundarySize :=
          hinputBoundarySizeSize.trans htoRootBoundary
        bodyBoundary :=
          hbodyBoundarySize.trans htoRootBoundary
        bodyCount :=
          hbodyCountSize.trans htoRootInput
        bodyBoundarySize :=
          hbodyBoundarySizeSize.trans htoRootBoundary
        tag :=
          htagSize.trans htoRootInput
        sequentBound := hsequentBoundSize }
  have hrootBounded :
      CompactProofRootSequentFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
    simpa only [endpointBound] using
      rootEndpoint_bounded_of_sizeBounds hrootGraph hrootSize
  have hsharedToPublic : sharedBound <= publicBound := by
    simpa only [sharedBound, publicBound] using
      compactProofRootSequentFailureShared_le_public inputWeight
  have hendpointPublic : Nat.size endpointBound <= publicBound := by
    simpa only [endpointBound, rootBound, publicBound] using
      compactProofRootSequentFailureRootPow_size_le_public
        inputWeight
  refine
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, endpointBound,
      by simpa only [input] using hshared.rootInputLayout,
      hrootBounded, ?_⟩
  exact
    { tokenTable :=
        (show Nat.size tokenTable <= sharedBound from by
          simpa only [sharedBound] using
            harithmeticPublic.tokenTable).trans hsharedToPublic
      width :=
        (show Nat.size width <= sharedBound from by
          simpa only [sharedBound] using
            harithmeticPublic.width_size).trans hsharedToPublic
      tokenCount :=
        (show Nat.size tokenCount <= sharedBound from by
          simpa only [sharedBound] using
            harithmeticPublic.tokenCount_size).trans hsharedToPublic
      inputStart :=
        (show Nat.size inputStart <= sharedBound from by
          simpa only [sharedBound] using
            harithmeticPublic.inputStart).trans hsharedToPublic
      inputFinish :=
        (show Nat.size inputFinish <= sharedBound from by
          simpa only [sharedBound] using
            harithmeticPublic.inputFinish).trans hsharedToPublic
      bodyStart :=
        (show Nat.size bodyStart <= sharedBound from by
          simpa only [sharedBound] using
            harithmeticPublic.bodyStart).trans hsharedToPublic
      bodyFinish :=
        (show Nat.size bodyFinish <= sharedBound from by
          simpa only [sharedBound] using
            harithmeticPublic.bodyFinish).trans hsharedToPublic
      endpointBound := hendpointPublic }

theorem
    exists_compactProofRootSequentFailureEndpointBoundedGraph_of_none_with_publicBounds
    (tag : Nat) (body : List Nat) (htag : tag <= 9)
    (hparser : compactSequentTokenValueParser body = none) :
    let input := tag :: body
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSequentFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound ∧
        CompactProofRootSequentFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound
            (compactProofRootSequentFailurePublicCoordinateSizeBound
              inputWeight) := by
  cases body with
  | nil =>
      simpa using
        exists_compactProofRootSequentFailureEndpointBoundedGraph_of_empty_body_with_publicBounds
          tag htag
  | cons count inputTail =>
      exact
        exists_compactProofRootSequentFailureEndpointBoundedGraph_of_cons_body_none_with_publicBounds
          tag count inputTail htag hparser

#print axioms
  exists_compactProofRootSequentFailureEndpointBoundedGraph_of_cons_body_none_with_publicBounds
#print axioms
  exists_compactProofRootSequentFailureEndpointBoundedGraph_of_empty_body_with_publicBounds
#print axioms
  exists_compactProofRootSequentFailureEndpointBoundedGraph_of_none_with_publicBounds

end FoundationCompactNumericListedDirectProofRootSequentFailurePublicBounds
