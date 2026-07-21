import integration.FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds
import integration.FoundationCompactNumericListedDirectProofRootClosedFormulaFailureCompleteness
import integration.FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointPublicBounds

/-!
# Public bounds for closed-formula proof-root failure

After a successful sequent parse, tag one can fail on its closed-formula parse,
including the extra free-variable rejection transition.  This module installs
the successful sequent trace and the complete closed no-output trace in one
canonical table, then bounds every exposed endpoint coordinate by the original
root-input weight.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootClosedFormulaFailurePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
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
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectSequentFormulaEndpointPublicBounds
open FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointFormula
open FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds
open FoundationCompactNumericListedDirectProofRootCanonicalSharedRowsPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData
open FoundationCompactNumericListedDirectSequentFormulaCanonicalDataPublicBounds
open FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint
open FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds
open FoundationCompactNumericListedDirectProofRootClosedFormulaFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootClosedFormulaFailureCompleteness
open FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedStateBounds

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

private theorem nat_le_two_pow_of_size_le
    {value sizeBound : Nat} (hsize : Nat.size value <= sizeBound) :
    value <= 2 ^ sizeBound :=
  (Nat.size_le.mp hsize).le

private theorem compactClosedFormulaParserNoOutputLocalTrace_weight_le_rootBound
    {binderArity : Nat}
    {tokens : List Nat} {states : CompactClosedFormulaTokenParserDirectTrace}
    (hvalid : CompactParserOutputLocalTraceValid compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound tokens)
      (compactFormulaParserInitialState binderArity tokens) none states)
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
    (fun state hstate => by
      exact compactClosedFormulaParserLocalTrace_member_state_weight_le
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

private theorem failureEndpoint_bounded_of_public
    {tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat}
    {coordinates : CompactParserClosedNoOutputExactEndpointCoordinates}
    {bound : Nat}
    (hgraph : CompactParserClosedNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount coordinates)
    (hpublic : CompactParserClosedNoOutputExactEndpointPublicBounds
      coordinates bound) :
    CompactParserClosedNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount (2 ^ bound) := by
  unfold CompactParserClosedNoOutputExactEndpointBoundedGraph
  have hsmall
      {value : Nat}
      (hvalue :
        value ∈
          compactParserClosedNoOutputExactEndpointCoordinateValues
            coordinates) :
      value <= 2 ^ bound :=
    nat_le_two_pow_of_size_le (hpublic.value_size_le value hvalue)
  refine
    ⟨coordinates.inputBoundary,
        hsmall (by
          simp [compactParserClosedNoOutputExactEndpointCoordinateValues]),
      coordinates.inputCount,
        hsmall (by
          simp [compactParserClosedNoOutputExactEndpointCoordinateValues]),
      coordinates.inputBoundarySize,
        hsmall (by
          simp [compactParserClosedNoOutputExactEndpointCoordinateValues]),
      coordinates.stateBoundary,
        hsmall (by
          simp [compactParserClosedNoOutputExactEndpointCoordinateValues]),
      coordinates.stateCount,
        hsmall (by
          simp [compactParserClosedNoOutputExactEndpointCoordinateValues]),
      coordinates.tableWidth,
        hsmall (by
          simp [compactParserClosedNoOutputExactEndpointCoordinateValues]),
      coordinates.valueBound,
        hsmall (by
          simp [compactParserClosedNoOutputExactEndpointCoordinateValues]),
      by simpa only [
        compactParserClosedNoOutputExactEndpointCoordinatesOfValues]
          using hgraph⟩

def compactProofRootClosedFormulaFailureParserCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootOneFormulaSharedCoordinateSizeBound inputWeight
  compactParserClosedNoOutputExactEndpointPublicCoordinateSizeBound
    sharedBound sharedBound

def compactProofRootClosedFormulaFailureLocalCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootOneFormulaSharedCoordinateSizeBound inputWeight
  sharedBound +
    (sharedBound + 1) * sharedBound +
    (inputWeight + 1) * sharedBound +
    compactProofRootOneFormulaSequentCoordinateSizeBound inputWeight +
    compactProofRootClosedFormulaFailureParserCoordinateSizeBound inputWeight +
    inputWeight + 12

def compactProofRootClosedFormulaFailurePublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootClosedFormulaFailureLocalCoordinateSizeBound inputWeight + 1

structure CompactProofRootClosedFormulaFailurePublicCoordinateBounds
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

set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootClosedFormulaFailureEndpointBoundedGraph_of_results_with_publicBounds
    (body : List Nat) (values : List (List Nat))
    (afterSequent : List Nat)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hformula : compactClosedFormulaTokenParser 0 afterSequent = none) :
    let input := 1 :: body
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootClosedFormulaFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound ∧
        CompactProofRootClosedFormulaFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound
            (compactProofRootClosedFormulaFailurePublicCoordinateSizeBound
              inputWeight) := by
  let input := 1 :: body
  let root : CompactNumericProofRoot :=
    (1, (values, ([], ([], ([], [])))))
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
  have houtput : compactSyntaxParserStateOutput
      ((compactClosedSyntaxParserStep^[compactSyntaxRunFuelBound afterSequent])
        (compactFormulaParserInitialState 0 afterSequent)) =
      none := by
    simpa [compactClosedFormulaTokenParser,
      compactClosedFormulaTokenParserRun] using hformula
  rcases
      (compactParserOutput_eq_iff_exists_localTrace
        compactClosedSyntaxParserStep
        (compactSyntaxRunFuelBound afterSequent)
        (compactFormulaParserInitialState 0 afterSequent)
        none).mp houtput with
    ⟨formulaStates, hformulaValid⟩
  have hformulaStatesWeight :
      compactAdditiveValueWeight formulaStates <=
        compactNumericRootSyntaxParserTraceWeightBound inputWeight :=
    compactClosedFormulaParserNoOutputLocalTrace_weight_le_rootBound
      hformulaValid hafterWeight (by omega)
  have hextraParserWeight :
      compactAdditiveValueWeight [formulaStates] <=
        compactProofRootOneFormulaExtraParserWeightBound inputWeight := by
    unfold compactProofRootOneFormulaExtraParserWeightBound
    rw [compactAdditiveValueWeight_list]
    simp only [List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.size_one, zero_add]
    omega
  have hformulaLocal : CompactParserOutputLocalTraceValid
      compactClosedSyntaxParserStep (compactSyntaxRunFuelBound afterSequent)
      (afterSequent, [(1, 0, 0)], none)
      none formulaStates := by
    simpa [compactFormulaParserInitialState,
      compactFormulaTask] using hformulaValid
  have hformulaStartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
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
        sequentSuffixes sequentParserTraces [] [formulaStates] with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish,
      _sequentSuffixBoundary, _intermediateSuffixBoundary,
      hshared, hsharedPublic⟩
  have hsharedDataWeight :
      compactProofRootCanonicalSharedDataWeight
          input root (compactSequentListTokens Gamma ++ afterSequent)
          sequentSuffixes sequentParserTraces [] [formulaStates] <=
        compactProofRootOneFormulaSharedDataWeightBound
          inputWeight := by
    have hemptySuffixes :
        compactAdditiveValueWeight ([] : List (List Nat)) = 1 := by
      simp [compactAdditiveValueWeight_list]
    unfold compactProofRootCanonicalSharedDataWeight
      compactProofRootOneFormulaSharedDataWeightBound
    rw [hemptySuffixes]
    omega
  have hsharedCoordinateBound :
      compactProofRootCanonicalSharedCoordinateSizeBound
          (compactProofRootCanonicalSharedDataWeight
            input root (compactSequentListTokens Gamma ++ afterSequent)
              sequentSuffixes sequentParserTraces [] [formulaStates]) <=
        compactProofRootOneFormulaSharedCoordinateSizeBound
          inputWeight := by
    unfold compactProofRootOneFormulaSharedCoordinateSizeBound
    exact
      compactProofRootCanonicalSharedCoordinateSizeBound_mono
        hsharedDataWeight
  let sharedBound :=
    compactProofRootOneFormulaSharedCoordinateSizeBound inputWeight
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
      _hrootTagCoordinate, hrootCore⟩
  rcases
      CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaCount, _hfirstLayout, _hfirstCount,
      _hsecondLayout, _hsecondCount, _hwitnessLayout, _hwitnessCount,
      _hsuffixLayout, _hsuffixCount⟩
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
          CompactUnifiedParserStateListRowLayouts
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
          sequentCoordinates.inputCount inputBoundary input.length 1 := by
    have hraw :=
      CompactAdditiveStructuredListElementRowLayouts.natConsRows
        hwitnessBodyRows hwitnessInputRows
          (show input =
            1 :: (compactSequentListTokens Gamma ++ afterSequent) by
              rfl)
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
  rcases hshared.extraParserRows 0 (by simp) with
    ⟨formulaStateBoundary, hformulaStateRowsRaw,
      hformulaStateBoundarySizeRaw⟩
  have hformulaStateRows :
      CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount formulaStateBoundary
          formulaStates := by
    simpa using hformulaStateRowsRaw
  have hformulaStateBoundarySize :
      Nat.size formulaStateBoundary <=
        (formulaStates.length + 1) * tokenCount := by
    simpa using hformulaStateBoundarySizeRaw
  rcases
      exists_compactParserClosedNoOutputExactEndpointGraph_of_rows_with_publicBounds
        hendpointSuffixLayout hformulaStateRows
        hformulaStateBoundarySize hformulaStartWell hformulaLocal with
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
  let failureActualBound :=
    compactParserClosedNoOutputExactEndpointPublicCoordinateSizeBound
      width tokenCount
  have hfailureBounded :
      CompactParserClosedNoOutputExactEndpointBoundedGraph
        tokenTable width tokenCount finalStart finalFinish
          1 0 0 (2 ^ failureActualBound) := by
    simpa only [failureActualBound] using
      failureEndpoint_bounded_of_public hfailureGraph hfailurePublic
  let coordinates :
      CompactProofRootClosedFormulaFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := inputBoundarySize
      bodyBoundary := sequentCoordinates.inputBoundary
      bodyCount := sequentCoordinates.inputCount
      bodyBoundarySize := sequentCoordinates.inputBoundarySize
      valueStart := rootCoordinates.start + 1
      valueFinish := rootCoordinates.gammaFinish
      finalStart := finalStart
      finalFinish := finalFinish
      sequentBound := 2 ^ sequentActualBound
      failureBound := 2 ^ failureActualBound }
  have hgraph :
      CompactProofRootClosedFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
    unfold CompactProofRootClosedFormulaFailureEndpointGraph
    dsimp only [coordinates]
    exact
      ⟨hinputWitness, hsequentGraph.1, hcons,
        hsequentBounded, hfailureBounded⟩
  let sequentCoordinateBound :=
    compactProofRootOneFormulaSequentCoordinateSizeBound inputWeight
  have hsequentCoordinateBound :
      compactSequentFormulaEndpointPublicCoordinateSizeBound
          width tokenCount <= sequentCoordinateBound := by
    dsimp only [sequentCoordinateBound,
      compactProofRootOneFormulaSequentCoordinateSizeBound]
    exact
      compactSequentFormulaEndpointPublicCoordinateSizeBound_mono
        hwidthValue htokenCountValue
  let failureCoordinateBound :=
    compactProofRootClosedFormulaFailureParserCoordinateSizeBound
      inputWeight
  have hfailureCoordinateBound :
      compactParserClosedNoOutputExactEndpointPublicCoordinateSizeBound
          width tokenCount <= failureCoordinateBound := by
    dsimp only [failureCoordinateBound,
      compactProofRootClosedFormulaFailureParserCoordinateSizeBound,
      compactParserClosedNoOutputExactEndpointPublicCoordinateSizeBound,
      compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound,
      compactParserSyntaxExactEndpointPublicCoordinateSizeBound]
    exact
      compactSequentFormulaStepPublicCoordinateSizeBound_mono
        hwidthValue htokenCountValue
  let localBound :=
    compactProofRootClosedFormulaFailureLocalCoordinateSizeBound
      inputWeight
  have hsharedToLocal : sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootClosedFormulaFailureLocalCoordinateSizeBound]
    omega
  have hsharedSuccToLocal : sharedBound + 1 <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootClosedFormulaFailureLocalCoordinateSizeBound]
    omega
  have hinputAreaToLocal :
      (inputWeight + 1) * sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootClosedFormulaFailureLocalCoordinateSizeBound]
    omega
  have hsequentToLocal : sequentCoordinateBound <= localBound := by
    dsimp only [sequentCoordinateBound, localBound,
      compactProofRootClosedFormulaFailureLocalCoordinateSizeBound]
    omega
  have hfailureToLocal : failureCoordinateBound <= localBound := by
    dsimp only [failureCoordinateBound, localBound,
      compactProofRootClosedFormulaFailureLocalCoordinateSizeBound]
    omega
  have hinputWeightToLocal : inputWeight <= localBound := by
    dsimp only [localBound,
      compactProofRootClosedFormulaFailureLocalCoordinateSizeBound]
    omega
  have hrootBounds := hrootCore.bounds
  have hrootSmall
      {value : Nat} (hvalue : value <= tokenCount) :
      Nat.size value <= localBound :=
    (natSize_le_of_le hvalue).trans
      (htokenCountValue.trans hsharedToLocal)
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
  have hsequentBoundSize :
      Nat.size (2 ^ sequentActualBound) <= localBound := by
    rw [Nat.size_pow]
    have hactual :
        sequentActualBound <= sequentCoordinateBound := by
      simpa only [sequentActualBound] using hsequentCoordinateBound
    exact (Nat.add_le_add_right hactual 1).trans (by
      dsimp only [sequentCoordinateBound, localBound,
        compactProofRootClosedFormulaFailureLocalCoordinateSizeBound]
      omega)
  have hfailureBoundSize :
      Nat.size (2 ^ failureActualBound) <= localBound := by
    rw [Nat.size_pow]
    have hactual :
        failureActualBound <= failureCoordinateBound := by
      simpa only [failureActualBound] using hfailureCoordinateBound
    exact (Nat.add_le_add_right hactual 1).trans (by
      dsimp only [failureCoordinateBound, localBound,
        compactProofRootClosedFormulaFailureLocalCoordinateSizeBound]
      omega)
  let endpointBound := 2 ^ localBound
  have hbounded :
      CompactProofRootClosedFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
    unfold CompactProofRootClosedFormulaFailureEndpointBoundedGraph
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
        rootCoordinates.start + 1,
          nat_le_two_pow_of_size_le hvalueStartSize,
        rootCoordinates.gammaFinish,
          nat_le_two_pow_of_size_le hvalueFinishSize,
        finalStart,
          nat_le_two_pow_of_size_le hfinalStartSize,
        finalFinish,
          nat_le_two_pow_of_size_le hfinalFinishSize,
        2 ^ sequentActualBound,
          nat_le_two_pow_of_size_le hsequentBoundSize,
        2 ^ failureActualBound,
          nat_le_two_pow_of_size_le hfailureBoundSize,
        by simpa only [coordinates,
          compactProofRootClosedFormulaFailureEndpointCoordinatesOfValues]
            using hgraph⟩
  let publicBound :=
    compactProofRootClosedFormulaFailurePublicCoordinateSizeBound
      inputWeight
  have hlocalToPublic : localBound <= publicBound := by
    dsimp only [localBound, publicBound,
      compactProofRootClosedFormulaFailurePublicCoordinateSizeBound]
    omega
  have hsharedToPublic : sharedBound <= publicBound :=
    hsharedToLocal.trans hlocalToPublic
  have hactualSharedToShared :
      compactProofRootCanonicalSharedCoordinateSizeBound
          (compactProofRootCanonicalSharedDataWeight
            input root (compactSequentListTokens Gamma ++ afterSequent)
              sequentSuffixes sequentParserTraces [] [formulaStates]) <=
        sharedBound := by
    simpa only [sharedBound] using hsharedCoordinateBound
  have hactualSharedToPublic :
      compactProofRootCanonicalSharedCoordinateSizeBound
          (compactProofRootCanonicalSharedDataWeight
            input root (compactSequentListTokens Gamma ++ afterSequent)
              sequentSuffixes sequentParserTraces [] [formulaStates]) <=
        publicBound :=
    hactualSharedToShared.trans hsharedToPublic
  have hendpointBoundPublic :
      Nat.size endpointBound <= publicBound := by
    dsimp only [endpointBound, publicBound,
      compactProofRootClosedFormulaFailurePublicCoordinateSizeBound]
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
  exists_compactProofRootClosedFormulaFailureEndpointBoundedGraph_of_results_with_publicBounds

end FoundationCompactNumericListedDirectProofRootClosedFormulaFailurePublicBounds
