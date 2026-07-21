import integration.FoundationCompactNumericListedDirectProofRootFormulaTermFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootFormulaTermFailureCompleteness
import integration.FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds

/-!
# Public bounds for trailing-term proof-root failure

Tag `6` parses a sequent, a binder-one formula, and a closed term.  This module
joins the successful formula trace and the complete no-output term trace in one
canonical table, with every exposed coordinate bounded from the original
root-input weight.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootFormulaTermFailurePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectProofRootFormulaTermFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootCanonicalSharedRowsPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData
open FoundationCompactNumericListedDirectSequentFormulaCanonicalDataPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectProofRootFormulaTermFailureCompleteness
open FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedStateBounds

private theorem nat_le_two_pow_of_size_le
    {value sizeBound : Nat} (hsize : Nat.size value <= sizeBound) :
    value <= 2 ^ sizeBound :=
  (Nat.size_le.mp hsize).le

private theorem compactTermParserNoOutputLocalTrace_weight_le_rootBound
    {binderArity : Nat}
    {tokens : List Nat} {states : CompactTermTokenParserDirectTrace}
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound tokens)
      (compactTermParserInitialState binderArity tokens) none states)
    {streamWeight : Nat}
    (hstream : compactAdditiveValueWeight tokens <= streamWeight)
    (hbinder : binderArity <= 1) :
    compactAdditiveValueWeight states <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight := by
  have hlocal := hvalid.1
  have hrows := compactAdditiveValueWeight_list_le states
    (compactNumericFormulaParserStateWeightBound
      (compactAdditiveValueWeight tokens)
      (binderArity + compactSyntaxRunFuelBound tokens)
      (compactSyntaxRunFuelBound tokens))
    (fun state hstate =>
      compactTermParserLocalTrace_member_state_weight_le
        hlocal hstate)
  have hraw :
      compactAdditiveValueWeight states <=
        compactNumericFormulaParserTraceWeightBound
          (compactAdditiveValueWeight tokens) binderArity
            (compactSyntaxRunFuelBound tokens) := by
    unfold compactNumericFormulaParserTraceWeightBound
    rw [hlocal.1] at hrows
    exact hrows
  have hfuel := compactSyntaxRunFuelBound_le_weightBound hstream
  unfold compactNumericRootSyntaxParserTraceWeightBound
  exact hraw.trans
    (compactNumericFormulaParserTraceWeightBound_mono
      hstream hbinder hfuel)

private theorem sequentEndpoint_bounded_of_public
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
      (hvalue :
        value ∈
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
      by simpa only [compactSequentFormulaEndpointCoordinatesOfValues]
        using hgraph⟩

private theorem exactEndpoint_bounded_of_public
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity
      taskRepeatCount : Nat}
    {coordinates : CompactParserSyntaxExactEndpointCoordinates}
    {bound : Nat}
    (hgraph : CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish taskKind taskBinderArity
        taskRepeatCount coordinates)
    (hpublic : CompactParserSyntaxExactEndpointPublicBounds
      coordinates bound) :
    CompactParserSyntaxExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish taskKind taskBinderArity
        taskRepeatCount (2 ^ bound) := by
  unfold CompactParserSyntaxExactEndpointBoundedGraph
  have hsmall
      {value : Nat}
      (hvalue :
        value ∈
          compactParserSyntaxExactEndpointCoordinateValues coordinates) :
      value <= 2 ^ bound :=
    nat_le_two_pow_of_size_le (hpublic.value_size_le value hvalue)
  refine
    ⟨coordinates.inputBoundary,
        hsmall (by
          simp [compactParserSyntaxExactEndpointCoordinateValues]),
      coordinates.inputCount,
        hsmall (by
          simp [compactParserSyntaxExactEndpointCoordinateValues]),
      coordinates.inputBoundarySize,
        hsmall (by
          simp [compactParserSyntaxExactEndpointCoordinateValues]),
      coordinates.expectedBoundary,
        hsmall (by
          simp [compactParserSyntaxExactEndpointCoordinateValues]),
      coordinates.expectedCount,
        hsmall (by
          simp [compactParserSyntaxExactEndpointCoordinateValues]),
      coordinates.expectedBoundarySize,
        hsmall (by
          simp [compactParserSyntaxExactEndpointCoordinateValues]),
      coordinates.stateBoundary,
        hsmall (by
          simp [compactParserSyntaxExactEndpointCoordinateValues]),
      coordinates.stateCount,
        hsmall (by
          simp [compactParserSyntaxExactEndpointCoordinateValues]),
      coordinates.tableWidth,
        hsmall (by
          simp [compactParserSyntaxExactEndpointCoordinateValues]),
      coordinates.valueBound,
        hsmall (by
          simp [compactParserSyntaxExactEndpointCoordinateValues]),
      by simpa only [compactParserSyntaxExactEndpointCoordinatesOfValues]
        using hgraph⟩

private theorem failureEndpoint_bounded_of_public
    {tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat}
    {coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates}
    {bound : Nat}
    (hgraph : CompactParserSyntaxNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount coordinates)
    (hpublic : CompactParserSyntaxNoOutputExactEndpointPublicBounds
      coordinates bound) :
    CompactParserSyntaxNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount (2 ^ bound) := by
  unfold CompactParserSyntaxNoOutputExactEndpointBoundedGraph
  have hsmall
      {value : Nat}
      (hvalue :
        value ∈
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

def compactProofRootFormulaTermExtraParserWeightBound
    (inputWeight : Nat) : Nat :=
  compactNumericRootSyntaxParserTraceWeightBound inputWeight +
    compactNumericRootSyntaxParserTraceWeightBound inputWeight + 3

def compactProofRootFormulaTermIntermediateSuffixWeightBound
    (inputWeight : Nat) : Nat :=
  inputWeight + 2

def compactProofRootFormulaTermSharedDataWeightBound
    (inputWeight : Nat) : Nat :=
  inputWeight +
    compactNumericVerifierTaskWeightBound inputWeight +
    inputWeight +
    compactSequentFormulaCanonicalSuffixesWeightBound inputWeight +
    compactSequentFormulaCanonicalParserTracesWeightBound inputWeight +
    compactProofRootFormulaTermIntermediateSuffixWeightBound inputWeight +
    compactProofRootFormulaTermExtraParserWeightBound inputWeight

def compactProofRootFormulaTermSharedCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootCanonicalSharedCoordinateSizeBound
    (compactProofRootFormulaTermSharedDataWeightBound inputWeight)

def compactProofRootFormulaTermSequentCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootFormulaTermSharedCoordinateSizeBound inputWeight
  compactSequentFormulaEndpointPublicCoordinateSizeBound
    sharedBound sharedBound

def compactProofRootFormulaTermParserCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootFormulaTermSharedCoordinateSizeBound inputWeight
  compactParserSyntaxExactEndpointPublicCoordinateSizeBound
    sharedBound sharedBound

def compactProofRootFormulaTermLocalCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootFormulaTermSharedCoordinateSizeBound inputWeight
  sharedBound +
    (sharedBound + 1) * sharedBound +
    (inputWeight + 1) * sharedBound +
    compactProofRootFormulaTermSequentCoordinateSizeBound inputWeight +
    compactProofRootFormulaTermParserCoordinateSizeBound inputWeight +
    compactProofRootFormulaTermParserCoordinateSizeBound inputWeight +
    inputWeight + 10

def compactProofRootFormulaTermFailurePublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootFormulaTermLocalCoordinateSizeBound inputWeight + 1

structure CompactProofRootFormulaTermFailurePublicCoordinateBounds
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

/-- A trailing-term failure constructs its complete bounded endpoint with no
hidden coordinate inputs. -/
theorem
    exists_compactProofRootFormulaTermFailureEndpointBoundedGraph_of_results_with_publicBounds
    (body : List Nat) (values : List (List Nat))
    (afterSequent middle : List Nat)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hfirst : compactFormulaTokenParser 1 afterSequent = some middle)
    (hsecond : compactTermTokenParser 0 middle = none) :
    let input := 6 :: body
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFormulaTermFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound ∧
        CompactProofRootFormulaTermFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound
            (compactProofRootFormulaTermFailurePublicCoordinateSizeBound
              inputWeight) := by
  let input := 6 :: body
  let root : CompactNumericProofRoot :=
    (6, (values, ([], ([], ([], [])))))
  let inputWeight := compactAdditiveValueWeight input
  have hrootTag : root.1 <= 10 := by
    simp [root]
  have hbodyWeight :
      compactAdditiveValueWeight body <= inputWeight :=
    compactAdditiveValueWeight_suffix_le
      (show body <:+ input from by simp [input])
  have hvaluesWeight :
      compactAdditiveValueWeight values <=
        compactNumericNestedListWeightBound inputWeight :=
    (compactSequentTokenValueParser_values_weight_le hsequent).trans
      (compactNumericNestedListWeightBound_mono hbodyWeight)
  have hemptyWeight :
      compactAdditiveValueWeight ([] : List Nat) <= inputWeight := by
    change 1 <= compactAdditiveValueWeight input
    exact compactAdditiveValueWeight_list_pos input
  have hrootWeight :
      compactAdditiveValueWeight root <=
        compactNumericVerifierTaskWeightBound inputWeight := by
    apply CompactNumericVerifierTaskWithin.weight_le
    refine ⟨hrootTag, ?_⟩
    dsimp only [root]
    exact
      ⟨hvaluesWeight, hemptyWeight, hemptyWeight,
        hemptyWeight, hemptyWeight⟩
  rcases compactSequentTokenValueParser_sound hsequent with
    ⟨Gamma, hbody, hvalues⟩
  subst body
  subst values
  have hafterWeight :
      compactAdditiveValueWeight afterSequent <= inputWeight := by
    have hafterSuffix :
        afterSequent <:+ compactSequentListTokens Gamma ++ afterSequent :=
      ⟨compactSequentListTokens Gamma, rfl⟩
    exact
      (compactAdditiveValueWeight_suffix_le hafterSuffix).trans
        hbodyWeight
  have hmiddleWeight :
      compactAdditiveValueWeight middle <= inputWeight := by
    have hmiddleSuffix : middle <:+ afterSequent :=
      compactFormulaTokenParser_suffix_of_success hfirst
    exact
      (compactAdditiveValueWeight_suffix_le hmiddleSuffix).trans
        hafterWeight
  rcases
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        1 afterSequent middle).mp hfirst with
    ⟨firstStates, hfirstValid⟩
  have hsecondOutput : compactSyntaxParserStateOutput
      ((compactSyntaxParserStep^[compactSyntaxRunFuelBound middle])
        (compactTermParserInitialState 0 middle)) = none := by
    simpa [compactTermTokenParser,
      compactTermTokenParserRun] using hsecond
  rcases
      (compactParserOutput_eq_iff_exists_localTrace
        compactSyntaxParserStep (compactSyntaxRunFuelBound middle)
        (compactTermParserInitialState 0 middle) none).mp
          hsecondOutput with
    ⟨secondStates, hsecondValid⟩
  have hfirstStatesWeight :
      compactAdditiveValueWeight firstStates <=
        compactNumericRootSyntaxParserTraceWeightBound inputWeight :=
    compactFormulaTokenParserDirectTraceValid_weight_le_rootBound
      hfirstValid hafterWeight (by omega)
  have hsecondStatesWeight :
      compactAdditiveValueWeight secondStates <=
        compactNumericRootSyntaxParserTraceWeightBound inputWeight :=
    compactTermParserNoOutputLocalTrace_weight_le_rootBound
      hsecondValid hmiddleWeight (by omega)
  have hintermediateSuffixWeight :
      compactAdditiveValueWeight [middle] <=
        compactProofRootFormulaTermIntermediateSuffixWeightBound
          inputWeight := by
    unfold compactProofRootFormulaTermIntermediateSuffixWeightBound
    rw [compactAdditiveValueWeight_list]
    simp only [List.length_cons, List.length_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.size_one, zero_add]
    omega
  have hextraParserWeight :
      compactAdditiveValueWeight [firstStates, secondStates] <=
        compactProofRootFormulaTermExtraParserWeightBound inputWeight := by
    have hlist :=
      compactAdditiveValueWeight_list_le
        [firstStates, secondStates]
        (compactNumericRootSyntaxParserTraceWeightBound inputWeight)
        (by
          intro states hstates
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hstates
          rcases hstates with rfl | rfl
          · exact hfirstStatesWeight
          · exact hsecondStatesWeight)
    refine hlist.trans ?_
    unfold compactProofRootFormulaTermExtraParserWeightBound
    have hsizeTwo : Nat.size 2 = 2 := by decide
    simp only [List.length_cons, List.length_nil]
    rw [hsizeTwo]
    omega
  rcases
      exists_compactSequentFormulaCanonicalDirectData_with_publicBounds
        Gamma afterSequent with
    ⟨sequentSuffixes, sequentParserTraces,
      hsequentSuffixCount, hsequentParserCount,
      hsequentFirst, hsequentFinal, hsequentSteps,
      hsequentSuffixWeight, hsequentParserWeight⟩
  have hsequentSuffixWeightPublic :
      compactAdditiveValueWeight sequentSuffixes <=
        compactSequentFormulaCanonicalSuffixesWeightBound inputWeight :=
    hsequentSuffixWeight.trans
      (compactSequentFormulaCanonicalSuffixesWeightBound_mono
        hbodyWeight)
  have hsequentParserWeightPublic :
      compactAdditiveValueWeight sequentParserTraces <=
        compactSequentFormulaCanonicalParserTracesWeightBound
          inputWeight :=
    hsequentParserWeight.trans
      (compactSequentFormulaCanonicalParserTracesWeightBound_mono
        hbodyWeight)
  rcases
      exists_compactProofRootCanonicalSharedRows_with_publicBounds
        input root (compactSequentListTokens Gamma ++ afterSequent)
        sequentSuffixes sequentParserTraces [middle]
          [firstStates, secondStates] with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish,
      _sequentSuffixBoundary, _intermediateSuffixBoundary,
      hshared, hsharedPublic⟩
  have hsharedDataWeight :
      compactProofRootCanonicalSharedDataWeight
          input root (compactSequentListTokens Gamma ++ afterSequent)
          sequentSuffixes sequentParserTraces [middle]
            [firstStates, secondStates] <=
        compactProofRootFormulaTermSharedDataWeightBound
          inputWeight := by
    unfold compactProofRootCanonicalSharedDataWeight
      compactProofRootFormulaTermSharedDataWeightBound
    omega
  have hsharedCoordinateBound :
      compactProofRootCanonicalSharedCoordinateSizeBound
          (compactProofRootCanonicalSharedDataWeight
            input root (compactSequentListTokens Gamma ++ afterSequent)
              sequentSuffixes sequentParserTraces [middle]
                [firstStates, secondStates]) <=
        compactProofRootFormulaTermSharedCoordinateSizeBound
          inputWeight := by
    unfold compactProofRootFormulaTermSharedCoordinateSizeBound
    exact
      compactProofRootCanonicalSharedCoordinateSizeBound_mono
        hsharedDataWeight
  let sharedBound :=
    compactProofRootFormulaTermSharedCoordinateSizeBound inputWeight
  have hwidthValue : width <= sharedBound :=
    hsharedPublic.width_value.trans (by
      simpa only [sharedBound] using hsharedCoordinateBound)
  have htokenCountValue : tokenCount <= sharedBound :=
    hsharedPublic.tokenCount_value.trans (by
      simpa only [sharedBound] using hsharedCoordinateBound)
  rcases
      CompactNumericVerifierTaskDirectLayout.toCoreGraph
        hshared.rootLayout with
    ⟨rootCoordinates, rootSize, hrootStart, hrootFinish,
      hrootTagCoordinate, hrootCore⟩
  rcases
      CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaCount, hfirstLayout, hfirstCount,
      hsecondLayout, hsecondCount, _hwitnessLayout, hwitnessCount,
      hsuffixLayout, hsuffixCount⟩
  have hrealizedEq : realizedRoot = root :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hrootCore
        (by simpa [hrootStart, hrootFinish] using hshared.rootLayout)
        hrealizedRoot
  subst realizedRoot
  have hgammaStructure := hrootCore.2.1
  rw [← hgammaCount] at hgammaStructure
  have hgammaSize :
      Nat.size rootCoordinates.gammaBoundary <=
        (root.2.1.length + 1) * tokenCount := by
    rw [hgammaCount]
    exact hrootCore.bounds.gammaBoundary_size_le
  have hsequentParserRows :
      ∀ index < (Gamma.map compactArithmeticFormulaTokens).length,
        ∃ parserStateBoundary,
          FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
              tokenTable width tokenCount parserStateBoundary
                (sequentParserTraces.getI index) ∧
            Nat.size parserStateBoundary <=
              ((sequentParserTraces.getI index).length + 1) *
                tokenCount := by
    intro index hindex
    apply hshared.sequentParserRows index
    rw [hsequentParserCount]
    simpa using hindex
  have hsequentSteps' :
      ∀ index < (Gamma.map compactArithmeticFormulaTokens).length,
        CompactFormulaTokenParserDirectTraceValid
            0 (sequentSuffixes.getI index)
              (sequentSuffixes.getI (index + 1))
              (sequentParserTraces.getI index) ∧
          sequentSuffixes.getI index =
            (Gamma.map compactArithmeticFormulaTokens).getI index ++
              sequentSuffixes.getI (index + 1) := by
    intro index hindex
    apply hsequentSteps index
    simpa using hindex
  have hsequentSuffixCount' :
      sequentSuffixes.length =
        (Gamma.map compactArithmeticFormulaTokens).length + 1 := by
    simpa using hsequentSuffixCount
  have hsequentParserCount' :
      sequentParserTraces.length =
        (Gamma.map compactArithmeticFormulaTokens).length := by
    simpa using hsequentParserCount
  have hbodyFirst :
      compactSequentListTokens Gamma ++ afterSequent =
        (Gamma.map compactArithmeticFormulaTokens).length ::
          sequentSuffixes.getI 0 := by
    rw [hsequentFirst]
    simp [compactSequentListTokens]
  have hsequentFinal' :
      sequentSuffixes.getI root.2.1.length = afterSequent := by
    simpa [root] using hsequentFinal
  rcases
      exists_compactSequentFormulaEndpointGraph_of_rows_with_publicBounds
        hshared.bodyLayout hshared.sequentSuffixRows
        hshared.sequentSuffixBoundary_size_le
        hgammaStructure hgammaRows hgammaSize
        hsequentParserRows hsequentSuffixCount'
        hsequentParserCount' hsequentSteps'
        hbodyFirst hsequentFinal' with
    ⟨finalStart, finalFinish, sequentCoordinates,
      hsequentGraph, hsequentPublic⟩
  rcases
      CompactAdditiveNatListDirectLayout.exists_witnessRows
        hshared.inputLayout with
    ⟨inputBoundary, inputBoundarySize, hinputWitness⟩
  rcases hinputWitness.realize with
    ⟨witnessInput, hwitnessInputCount, hwitnessInputLayout,
      hwitnessInputRows⟩
  have hwitnessInputEq : witnessInput = input :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hshared.inputLayout hwitnessInputLayout).1
  subst witnessInput
  rcases hsequentGraph.1.realize with
    ⟨witnessBody, hwitnessBodyCount, hwitnessBodyLayout,
      hwitnessBodyRows⟩
  have hwitnessBodyEq : witnessBody =
      compactSequentListTokens Gamma ++ afterSequent :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hshared.bodyLayout hwitnessBodyLayout).1
  subst witnessBody
  have hcons :
      CompactAdditiveNatListConsRows
        tokenTable width tokenCount sequentCoordinates.inputBoundary
          sequentCoordinates.inputCount inputBoundary input.length 6 := by
    have hraw :=
      CompactAdditiveStructuredListElementRowLayouts.natConsRows
        hwitnessBodyRows hwitnessInputRows
          (show input =
            6 :: (compactSequentListTokens Gamma ++ afterSequent) by rfl)
    simpa only [hwitnessBodyCount, hwitnessInputCount] using hraw
  rcases hsequentGraph.sound with
    ⟨endpointBody, endpointValues, endpointSuffix,
      hendpointBodyLayout, _hendpointValuesLayout,
      hendpointSuffixLayout, hendpointParser⟩
  have hendpointBodyEq : endpointBody =
      compactSequentListTokens Gamma ++ afterSequent :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hshared.bodyLayout hendpointBodyLayout).1
  subst endpointBody
  have hendpointResult :
      (endpointValues, endpointSuffix) =
        (Gamma.map compactArithmeticFormulaTokens, afterSequent) :=
    Option.some.inj
      (hendpointParser.symm.trans hsequent)
  have hendpointSuffixEq : endpointSuffix = afterSequent :=
    congrArg Prod.snd hendpointResult
  subst endpointSuffix
  rcases hshared.intermediateSuffixRows 0 (by simp) with
    ⟨middleStart, hmiddleStartBound, middleFinish, hmiddleFinishBound,
      _hmiddleStartEntry, _hmiddleFinishEntry, hmiddleLayoutRaw⟩
  have hmiddleLayout :
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount middleStart middleFinish middle := by
    simpa using hmiddleLayoutRaw
  rcases hshared.extraParserRows 0 (by simp) with
    ⟨firstStateBoundary, hfirstStateRowsRaw,
      hfirstStateBoundarySizeRaw⟩
  have hfirstStateRows :
      FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount firstStateBoundary firstStates := by
    simpa using hfirstStateRowsRaw
  have hfirstStateBoundarySize :
      Nat.size firstStateBoundary <=
        (firstStates.length + 1) * tokenCount := by
    simpa using hfirstStateBoundarySizeRaw
  rcases hshared.extraParserRows 1 (by simp) with
    ⟨secondStateBoundary, hsecondStateRowsRaw,
      hsecondStateBoundarySizeRaw⟩
  have hsecondStateRows :
      FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount secondStateBoundary secondStates := by
    simpa using hsecondStateRowsRaw
  have hsecondStateBoundarySize :
      Nat.size secondStateBoundary <=
        (secondStates.length + 1) * tokenCount := by
    simpa using hsecondStateBoundarySizeRaw
  have hformulaStartWell :
      CompactSyntaxTaskStackFieldsWellFormed
        [(1, 1, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  have htermStartWell :
      CompactSyntaxTaskStackFieldsWellFormed
        [(0, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  have hfirstLocal :
      CompactParserOutputLocalTraceValid compactSyntaxParserStep
        (compactSyntaxRunFuelBound afterSequent)
        (afterSequent, [(1, 1, 0)], none)
        (some middle) firstStates := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using
        hfirstValid
  have hsecondLocal :
      CompactParserOutputLocalTraceValid compactSyntaxParserStep
        (compactSyntaxRunFuelBound middle)
        (middle, [(0, 0, 0)], none)
        none secondStates := by
    simpa [compactTermParserInitialState,
      compactTermTask] using hsecondValid
  rcases
      exists_compactParserSyntaxExactEndpointGraph_of_rows_with_publicBounds
        hendpointSuffixLayout hmiddleLayout hfirstStateRows
        hfirstStateBoundarySize hformulaStartWell hfirstLocal with
    ⟨firstCoordinates, hfirstResult⟩
  have hfirstGraph := hfirstResult.1
  have hfirstPublic := hfirstResult.2.1
  rcases
      exists_compactParserSyntaxNoOutputExactEndpointGraph_of_rows_with_publicBounds
        hmiddleLayout hsecondStateRows
        hsecondStateBoundarySize htermStartWell hsecondLocal with
    ⟨failureCoordinates, hfailureGraph,
      hfailurePublic, _hfailureBoundaryEq⟩
  let sequentActualBound :=
    compactSequentFormulaEndpointPublicCoordinateSizeBound
      width tokenCount
  have hsequentBounded :
      CompactSequentFormulaEndpointBoundedGraph
        tokenTable width tokenCount bodyStart bodyFinish
          (rootCoordinates.start + 1) rootCoordinates.gammaFinish
          finalStart finalFinish (2 ^ sequentActualBound) := by
    simpa only [sequentActualBound] using
      sequentEndpoint_bounded_of_public hsequentGraph hsequentPublic
  let firstActualBound :=
    compactParserSyntaxExactEndpointPublicCoordinateSizeBound
      width tokenCount
  have hfirstBounded :
      CompactParserSyntaxExactEndpointBoundedGraph
        tokenTable width tokenCount finalStart finalFinish
          middleStart middleFinish 1 1 0 (2 ^ firstActualBound) := by
    simpa only [firstActualBound] using
      exactEndpoint_bounded_of_public hfirstGraph hfirstPublic
  let failureActualBound :=
    compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
      width tokenCount
  have hfailureBounded :
      CompactParserSyntaxNoOutputExactEndpointBoundedGraph
        tokenTable width tokenCount middleStart middleFinish
          0 0 0 (2 ^ failureActualBound) := by
    simpa only [failureActualBound] using
      failureEndpoint_bounded_of_public hfailureGraph hfailurePublic
  have hcoordinateTag : rootCoordinates.tag = 6 := by
    simpa [root] using hrootTagCoordinate
  have hconsCoordinateTag :
      CompactAdditiveNatListConsRows
        tokenTable width tokenCount sequentCoordinates.inputBoundary
          sequentCoordinates.inputCount inputBoundary input.length
          rootCoordinates.tag := by
    simpa only [hcoordinateTag] using hcons
  let coordinates : CompactProofRootFormulaTermFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := inputBoundarySize
      bodyBoundary := sequentCoordinates.inputBoundary
      bodyCount := sequentCoordinates.inputCount
      bodyBoundarySize := sequentCoordinates.inputBoundarySize
      tag := rootCoordinates.tag
      valueStart := rootCoordinates.start + 1
      valueFinish := rootCoordinates.gammaFinish
      firstStart := finalStart
      firstFinish := finalFinish
      secondStart := middleStart
      secondFinish := middleFinish
      sequentBound := 2 ^ sequentActualBound
      firstBound := 2 ^ firstActualBound
      failureBound := 2 ^ failureActualBound }
  have hgraph :
      CompactProofRootFormulaTermFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
    unfold CompactProofRootFormulaTermFailureEndpointGraph
    dsimp only [coordinates]
    exact ⟨hinputWitness, hsequentGraph.1,
      hcoordinateTag, hconsCoordinateTag,
      hsequentBounded, hfirstBounded, hfailureBounded⟩
  let sequentCoordinateBound :=
    compactProofRootFormulaTermSequentCoordinateSizeBound inputWeight
  have hsequentCoordinateBound :
      compactSequentFormulaEndpointPublicCoordinateSizeBound
          width tokenCount <= sequentCoordinateBound := by
    dsimp only [sequentCoordinateBound,
      compactProofRootFormulaTermSequentCoordinateSizeBound]
    exact
      compactSequentFormulaEndpointPublicCoordinateSizeBound_mono
        hwidthValue htokenCountValue
  let formulaCoordinateBound :=
    compactProofRootFormulaTermParserCoordinateSizeBound inputWeight
  have hformulaCoordinateBound :
      compactParserSyntaxExactEndpointPublicCoordinateSizeBound
          width tokenCount <= formulaCoordinateBound := by
    dsimp only [formulaCoordinateBound,
      compactProofRootFormulaTermParserCoordinateSizeBound,
      compactParserSyntaxExactEndpointPublicCoordinateSizeBound]
    exact
      compactSequentFormulaStepPublicCoordinateSizeBound_mono
        hwidthValue htokenCountValue
  have hfailureCoordinateBound :
      compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
          width tokenCount <= formulaCoordinateBound := by
    dsimp only [formulaCoordinateBound,
      compactProofRootFormulaTermParserCoordinateSizeBound,
      compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound,
      compactParserSyntaxExactEndpointPublicCoordinateSizeBound]
    exact
      compactSequentFormulaStepPublicCoordinateSizeBound_mono
        hwidthValue htokenCountValue
  let localBound :=
    compactProofRootFormulaTermLocalCoordinateSizeBound inputWeight
  have hsharedToLocal : sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootFormulaTermLocalCoordinateSizeBound]
    omega
  have hsharedSuccToLocal : sharedBound + 1 <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootFormulaTermLocalCoordinateSizeBound]
    omega
  have hinputAreaToLocal :
      (inputWeight + 1) * sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootFormulaTermLocalCoordinateSizeBound]
    omega
  have hsequentToLocal : sequentCoordinateBound <= localBound := by
    dsimp only [sequentCoordinateBound, localBound,
      compactProofRootFormulaTermLocalCoordinateSizeBound]
    omega
  have hformulaToLocal : formulaCoordinateBound <= localBound := by
    dsimp only [formulaCoordinateBound, localBound,
      compactProofRootFormulaTermLocalCoordinateSizeBound]
    omega
  have hinputWeightToLocal : inputWeight <= localBound := by
    dsimp only [localBound,
      compactProofRootFormulaTermLocalCoordinateSizeBound]
    omega
  have hrootBounds := hrootCore.bounds
  have hrootSmall
      {value : Nat} (hvalue : value <= tokenCount) :
      Nat.size value <= localBound :=
    (natSize_le_of_le hvalue).trans
      (htokenCountValue.trans hsharedToLocal)
  have hrootTagSize :
      Nat.size rootCoordinates.tag <= localBound :=
    hrootBounds.tag_size_le.trans
      (hwidthValue.trans hsharedToLocal)
  have hvalueStartSize :
      Nat.size (rootCoordinates.start + 1) <= localBound := by
    have hvalue :
        rootCoordinates.start + 1 <= sharedBound + 1 :=
      Nat.add_le_add_right
        (hrootBounds.start_le.trans htokenCountValue) 1
    exact (natSize_le_of_le hvalue).trans hsharedSuccToLocal
  have hvalueFinishSize :
      Nat.size rootCoordinates.gammaFinish <= localBound :=
    hrootSmall hrootBounds.gammaFinish_le
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have hinputArea :
      (input.length + 1) * tokenCount <=
        (inputWeight + 1) * sharedBound :=
    Nat.mul_le_mul
      (Nat.add_le_add_right hinputLength 1) htokenCountValue
  have hinputBoundarySizeRaw :
      Nat.size inputBoundary <=
        (input.length + 1) * tokenCount := by
    rw [← hinputWitness.2.2.1]
    exact hinputWitness.2.2.2
  have hinputBoundarySize :
      Nat.size inputBoundary <= localBound :=
    hinputBoundarySizeRaw.trans
      (hinputArea.trans hinputAreaToLocal)
  have hinputCountSize :
      Nat.size input.length <= localBound :=
    (natSize_le_of_le hinputLength).trans hinputWeightToLocal
  have hinputBoundarySizeWitness :
      Nat.size inputBoundarySize <= localBound :=
    (natSize_le_of_le hinputWitness.2.2.2).trans
      (hinputArea.trans hinputAreaToLocal)
  have hsequentSize
      {value : Nat}
      (hvalue :
        value ∈
          compactSequentFormulaEndpointCoordinateValues
            sequentCoordinates) :
      Nat.size value <= localBound :=
    (hsequentPublic.value_size_le value hvalue).trans
      (hsequentCoordinateBound.trans hsequentToLocal)
  have hfinalStartSize : Nat.size finalStart <= localBound :=
    hsequentPublic.finalStart_size_le.trans
      (hsequentCoordinateBound.trans hsequentToLocal)
  have hfinalFinishSize : Nat.size finalFinish <= localBound :=
    hsequentPublic.finalFinish_size_le.trans
      (hsequentCoordinateBound.trans hsequentToLocal)
  have hmiddleStartSize : Nat.size middleStart <= localBound :=
    hrootSmall hmiddleStartBound
  have hmiddleFinishSize : Nat.size middleFinish <= localBound :=
    hrootSmall hmiddleFinishBound
  have hsequentBoundSize :
      Nat.size (2 ^ sequentActualBound) <= localBound := by
    rw [Nat.size_pow]
    have hactual :
        sequentActualBound <= sequentCoordinateBound := by
      simpa only [sequentActualBound] using hsequentCoordinateBound
    exact (Nat.add_le_add_right hactual 1).trans (by
      dsimp only [sequentCoordinateBound, localBound,
        compactProofRootFormulaTermLocalCoordinateSizeBound]
      omega)
  have hfirstBoundSize :
      Nat.size (2 ^ firstActualBound) <= localBound := by
    rw [Nat.size_pow]
    have hactual :
        firstActualBound <= formulaCoordinateBound := by
      simpa only [firstActualBound] using hformulaCoordinateBound
    exact (Nat.add_le_add_right hactual 1).trans (by
      dsimp only [formulaCoordinateBound, localBound,
        compactProofRootFormulaTermLocalCoordinateSizeBound]
      omega)
  have hfailureBoundSize :
      Nat.size (2 ^ failureActualBound) <= localBound := by
    rw [Nat.size_pow]
    have hactual :
        failureActualBound <= formulaCoordinateBound := by
      simpa only [failureActualBound] using hfailureCoordinateBound
    exact (Nat.add_le_add_right hactual 1).trans (by
      dsimp only [formulaCoordinateBound, localBound,
        compactProofRootFormulaTermLocalCoordinateSizeBound]
      omega)
  let endpointBound := 2 ^ localBound
  have hbounded :
      CompactProofRootFormulaTermFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
    unfold CompactProofRootFormulaTermFailureEndpointBoundedGraph
    refine
      ⟨inputBoundary,
          nat_le_two_pow_of_size_le hinputBoundarySize,
        input.length,
          nat_le_two_pow_of_size_le hinputCountSize,
        inputBoundarySize,
          nat_le_two_pow_of_size_le hinputBoundarySizeWitness,
        sequentCoordinates.inputBoundary,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.inputCount,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.inputBoundarySize,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        rootCoordinates.tag,
          nat_le_two_pow_of_size_le hrootTagSize,
        rootCoordinates.start + 1,
          nat_le_two_pow_of_size_le hvalueStartSize,
        rootCoordinates.gammaFinish,
          nat_le_two_pow_of_size_le hvalueFinishSize,
        finalStart,
          nat_le_two_pow_of_size_le hfinalStartSize,
        finalFinish,
          nat_le_two_pow_of_size_le hfinalFinishSize,
        middleStart,
          nat_le_two_pow_of_size_le hmiddleStartSize,
        middleFinish,
          nat_le_two_pow_of_size_le hmiddleFinishSize,
        2 ^ sequentActualBound,
          nat_le_two_pow_of_size_le hsequentBoundSize,
        2 ^ firstActualBound,
          nat_le_two_pow_of_size_le hfirstBoundSize,
        2 ^ failureActualBound,
          nat_le_two_pow_of_size_le hfailureBoundSize,
        by simpa only [coordinates,
          compactProofRootFormulaTermFailureEndpointCoordinatesOfValues]
            using hgraph⟩
  let publicBound :=
    compactProofRootFormulaTermFailurePublicCoordinateSizeBound
      inputWeight
  have hlocalToPublic : localBound <= publicBound := by
    dsimp only [localBound, publicBound,
      compactProofRootFormulaTermFailurePublicCoordinateSizeBound]
    omega
  have hsharedToPublic : sharedBound <= publicBound :=
    hsharedToLocal.trans hlocalToPublic
  have hactualSharedToShared :
      compactProofRootCanonicalSharedCoordinateSizeBound
          (compactProofRootCanonicalSharedDataWeight
            input root (compactSequentListTokens Gamma ++ afterSequent)
              sequentSuffixes sequentParserTraces [middle]
                [firstStates, secondStates]) <=
        sharedBound := by
    simpa only [sharedBound] using hsharedCoordinateBound
  have hactualSharedToPublic :
      compactProofRootCanonicalSharedCoordinateSizeBound
          (compactProofRootCanonicalSharedDataWeight
            input root (compactSequentListTokens Gamma ++ afterSequent)
              sequentSuffixes sequentParserTraces [middle]
                [firstStates, secondStates]) <=
        publicBound :=
    hactualSharedToShared.trans hsharedToPublic
  have hendpointBoundPublic :
      Nat.size endpointBound <= publicBound := by
    dsimp only [endpointBound, publicBound,
      compactProofRootFormulaTermFailurePublicCoordinateSizeBound]
    rw [Nat.size_pow]
  refine
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, endpointBound,
      by simpa only [input] using hshared.inputLayout,
      hbounded, ?_⟩
  exact
    { tokenTable :=
        hsharedPublic.tokenTable.trans hactualSharedToPublic
      width :=
        hsharedPublic.width_size.trans hactualSharedToPublic
      tokenCount :=
        hsharedPublic.tokenCount_size.trans hactualSharedToPublic
      inputStart :=
        hsharedPublic.inputStart.trans hactualSharedToPublic
      inputFinish :=
        hsharedPublic.inputFinish.trans hactualSharedToPublic
      bodyStart :=
        hsharedPublic.bodyStart.trans hactualSharedToPublic
      bodyFinish :=
        hsharedPublic.bodyFinish.trans hactualSharedToPublic
      endpointBound := hendpointBoundPublic }

#print axioms
  exists_compactProofRootFormulaTermFailureEndpointBoundedGraph_of_results_with_publicBounds

end FoundationCompactNumericListedDirectProofRootFormulaTermFailurePublicBounds
