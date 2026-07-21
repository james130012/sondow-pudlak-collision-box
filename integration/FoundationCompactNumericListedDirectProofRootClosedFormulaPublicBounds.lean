import integration.FoundationCompactNumericListedDirectProofRootClosedFormulaBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
import integration.FoundationCompactNumericListedDirectParserClosedEndpointPublicBounds

/-!
# Public bounds for closed-formula proof-root success

Tag `1` parses a sequent followed by one closed formula.  The complete sequent
trace and the complete closed-parser trace are placed in the same canonical
table.  Every local coordinate is bounded explicitly from the public input
weight, including the closed-parser safety relation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds

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
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint
open FoundationCompactNumericListedDirectProofRootClosedFormulaEndpoint
open FoundationCompactNumericListedDirectProofRootClosedFormulaBoundedFormula
open FoundationCompactNumericListedDirectProofRootCanonicalSharedRowsPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData
open FoundationCompactNumericListedDirectSequentFormulaCanonicalDataPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
open FoundationCompactNumericListedDirectParserClosedEndpointCompleteness
open FoundationCompactNumericListedDirectParserClosedEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedStateBounds

private theorem nat_le_two_pow_of_size_le
    {value sizeBound : Nat} (hsize : Nat.size value <= sizeBound) :
    value <= 2 ^ sizeBound :=
  (Nat.size_le.mp hsize).le

def compactProofRootOneFormulaExtraParserWeightBound
    (inputWeight : Nat) : Nat :=
  compactNumericRootSyntaxParserTraceWeightBound inputWeight + 2

def compactProofRootOneFormulaSharedDataWeightBound
    (inputWeight : Nat) : Nat :=
  inputWeight +
    compactNumericVerifierTaskWeightBound inputWeight +
    inputWeight +
    compactSequentFormulaCanonicalSuffixesWeightBound inputWeight +
    compactSequentFormulaCanonicalParserTracesWeightBound inputWeight +
    1 +
    compactProofRootOneFormulaExtraParserWeightBound inputWeight

def compactProofRootOneFormulaSharedCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootCanonicalSharedCoordinateSizeBound
    (compactProofRootOneFormulaSharedDataWeightBound inputWeight)

def compactProofRootOneFormulaSequentCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootOneFormulaSharedCoordinateSizeBound inputWeight
  compactSequentFormulaEndpointPublicCoordinateSizeBound
    sharedBound sharedBound

def compactProofRootOneFormulaParserCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootOneFormulaSharedCoordinateSizeBound inputWeight
  compactParserSyntaxExactEndpointPublicCoordinateSizeBound
    sharedBound sharedBound

def compactProofRootOneFormulaLocalCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootOneFormulaSharedCoordinateSizeBound inputWeight
  sharedBound +
    (sharedBound + 1) * sharedBound +
    (inputWeight + 1) * sharedBound +
    compactProofRootOneFormulaSequentCoordinateSizeBound inputWeight +
    compactProofRootOneFormulaParserCoordinateSizeBound inputWeight +
    inputWeight + 10

def compactProofRootOneFormulaPublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootOneFormulaLocalCoordinateSizeBound inputWeight + 1

theorem compactProofRootClosedFormulaPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactProofRootOneFormulaPublicCoordinateSizeBound left <=
      compactProofRootOneFormulaPublicCoordinateSizeBound right := by
  have htask := compactNumericVerifierTaskWeightBound_mono h
  have hsuffixes :=
    compactSequentFormulaCanonicalSuffixesWeightBound_mono h
  have htraces :=
    compactSequentFormulaCanonicalParserTracesWeightBound_mono h
  have hparserTrace := compactNumericRootSyntaxParserTraceWeightBound_mono h
  have hextra :
      compactProofRootOneFormulaExtraParserWeightBound left <=
        compactProofRootOneFormulaExtraParserWeightBound right := by
    unfold compactProofRootOneFormulaExtraParserWeightBound
    omega
  have hdata :
      compactProofRootOneFormulaSharedDataWeightBound left <=
        compactProofRootOneFormulaSharedDataWeightBound right := by
    unfold compactProofRootOneFormulaSharedDataWeightBound
    omega
  have hshared :
      compactProofRootOneFormulaSharedCoordinateSizeBound left <=
        compactProofRootOneFormulaSharedCoordinateSizeBound right := by
    unfold compactProofRootOneFormulaSharedCoordinateSizeBound
    exact compactProofRootCanonicalSharedCoordinateSizeBound_mono hdata
  have hsequent :
      compactProofRootOneFormulaSequentCoordinateSizeBound left <=
        compactProofRootOneFormulaSequentCoordinateSizeBound right := by
    unfold compactProofRootOneFormulaSequentCoordinateSizeBound
    exact compactSequentFormulaEndpointPublicCoordinateSizeBound_mono
      hshared hshared
  have hparser :
      compactProofRootOneFormulaParserCoordinateSizeBound left <=
        compactProofRootOneFormulaParserCoordinateSizeBound right := by
    unfold compactProofRootOneFormulaParserCoordinateSizeBound
      compactParserSyntaxExactEndpointPublicCoordinateSizeBound
    exact compactSequentFormulaStepPublicCoordinateSizeBound_mono
      hshared hshared
  have hsharedArea :
      (compactProofRootOneFormulaSharedCoordinateSizeBound left + 1) *
          compactProofRootOneFormulaSharedCoordinateSizeBound left <=
        (compactProofRootOneFormulaSharedCoordinateSizeBound right + 1) *
          compactProofRootOneFormulaSharedCoordinateSizeBound right :=
    Nat.mul_le_mul (Nat.add_le_add_right hshared 1) hshared
  have hmixed :
      (left + 1) * compactProofRootOneFormulaSharedCoordinateSizeBound left <=
        (right + 1) *
          compactProofRootOneFormulaSharedCoordinateSizeBound right :=
    Nat.mul_le_mul (Nat.add_le_add_right h 1) hshared
  simp only [compactProofRootOneFormulaPublicCoordinateSizeBound,
    compactProofRootOneFormulaLocalCoordinateSizeBound]
  omega

structure CompactProofRootOneFormulaPublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound bound : Nat) :
    Prop where
  tokenTable : Nat.size tokenTable <= bound
  width_value : width <= bound
  width : Nat.size width <= bound
  tokenCount_value : tokenCount <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  rootStart : Nat.size rootStart <= bound
  rootFinish : Nat.size rootFinish <= bound
  bodyStart : Nat.size bodyStart <= bound
  bodyFinish : Nat.size bodyFinish <= bound
  endpointBound : Nat.size endpointBound <= bound

/-- A successful closed-formula branch constructs its complete bounded endpoint
with a public coordinate budget. -/
theorem
    exists_compactProofRootClosedFormulaEndpointBoundedGraph_of_results_with_publicBounds
    (body : List Nat)
    (values : List (List Nat))
    (afterSequent first suffix : List Nat)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hclosed : compactClosedFormulaTokenParser 0 afterSequent =
      some suffix)
    (hsplit : afterSequent = first ++ suffix) :
    let input := 1 :: body
    let root : CompactNumericProofRoot :=
      (1, (values, (first, ([], ([], suffix)))))
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootClosedFormulaEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound ∧
        CompactProofRootOneFormulaPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound
            (compactProofRootOneFormulaPublicCoordinateSizeBound
              inputWeight) := by
  let input := 1 :: body
  let root : CompactNumericProofRoot :=
    (1, (values, (first, ([], ([], suffix)))))
  let inputWeight := compactAdditiveValueWeight input
  have hformulaValue :
      compactClosedFormulaTokenValueParser afterSequent =
        some (first, suffix) := by
    unfold compactClosedFormulaTokenValueParser
    rw [hclosed]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    simpa [hsplit] using consumedTokenPrefix_append first suffix
  have hrootParser :
      compactListedProofNodeFieldsParser input = some root := by
    simp [input, root, compactListedProofNodeFieldsParser,
      compactTagNumericNodeFields, compactNodeSequentClosedFormulaFields,
      hsequent, hformulaValue]
  have hrootTag : root.1 <= 10 := by
    simp [root]
  have hrootWeight :
      compactAdditiveValueWeight root <=
        compactNumericVerifierTaskWeightBound inputWeight := by
    exact (show CompactNumericVerifierTaskWithin inputWeight root from
      ⟨hrootTag,
        compactListedProofNodeFieldsParser_componentsWithin
          hrootParser⟩).weight_le
  have hbodyWeight :
      compactAdditiveValueWeight body <= inputWeight :=
    compactAdditiveValueWeight_suffix_le
      (show body <:+ input from ⟨[1], by simp [input]⟩)
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
  rcases
      (compactClosedFormulaTokenParser_eq_some_iff_exists_directTrace
        0 afterSequent suffix).mp hclosed with
    ⟨formulaStates, hformulaValid⟩
  have hformulaStatesWeight :
      compactAdditiveValueWeight formulaStates <=
        compactNumericRootSyntaxParserTraceWeightBound inputWeight :=
    compactClosedFormulaTokenParserDirectTraceValid_weight_le_rootBound
      hformulaValid hafterWeight (by omega)
  have hextraParserWeight :
      compactAdditiveValueWeight [formulaStates] <=
        compactProofRootOneFormulaExtraParserWeightBound inputWeight := by
    unfold compactProofRootOneFormulaExtraParserWeightBound
    rw [compactAdditiveValueWeight_list]
    simp only [List.length_cons,
      List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.size_one, zero_add]
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
      hrootTagCoordinate, hrootCore⟩
  rcases
      CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaCount, hfirstLayout, hfirstCount,
      _hsecondLayout, hsecondCount, _hwitnessLayout, hwitnessCount,
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
          sequentCoordinates.inputCount inputBoundary input.length 1 := by
    have hraw :=
      CompactAdditiveStructuredListElementRowLayouts.natConsRows
        hwitnessBodyRows hwitnessInputRows
          (show input =
            1 :: (compactSequentListTokens Gamma ++ afterSequent) by rfl)
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
      (hendpointParser.symm.trans (by simpa using hsequent))
  have hendpointSuffixEq : endpointSuffix = afterSequent :=
    congrArg Prod.snd hendpointResult
  subst endpointSuffix
  rcases hshared.extraParserRows 0 (by simp) with
    ⟨formulaStateBoundary, hformulaStateRowsRaw,
      hformulaStateBoundarySizeRaw⟩
  have hformulaStateRows :
      FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount formulaStateBoundary formulaStates := by
    simpa using hformulaStateRowsRaw
  have hformulaStateBoundarySize :
      Nat.size formulaStateBoundary <=
        (formulaStates.length + 1) * tokenCount := by
    simpa using hformulaStateBoundarySizeRaw
  have hformulaStartWell :
      CompactSyntaxTaskStackFieldsWellFormed
        [(1, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  have hformulaLocal :
      CompactParserOutputLocalTraceValid compactClosedSyntaxParserStep
        (compactSyntaxRunFuelBound afterSequent)
        (afterSequent, [(1, 0, 0)], none)
        (some suffix) formulaStates := by
    simpa [CompactClosedFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using
        hformulaValid
  rcases
      exists_compactParserClosedEndpointGraph_of_rows_with_publicBounds
        hendpointSuffixLayout hsuffixLayout hformulaStateRows
        hformulaStateBoundarySize hformulaStartWell hformulaLocal with
    ⟨formulaCoordinates, hformulaResult⟩
  have hformulaGraph := hformulaResult.1
  have hformulaPublic := hformulaResult.2
  rcases hformulaGraph.1.realize with
    ⟨formulaInput, hformulaInputCount,
      hformulaInputLayout, _hformulaInputRows⟩
  have hformulaInputEq : formulaInput = afterSequent :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hendpointSuffixLayout hformulaInputLayout).1
  have hafterCount :
      afterSequent.length = formulaCoordinates.inputCount := by
    rw [← hformulaInputEq]
    exact hformulaInputCount
  have happendTyped :
      CompactAdditiveNatListAppendSlices
        tokenTable width tokenCount
          rootCoordinates.gammaFinish rootCoordinates.firstFinish
            root.2.2.1.length
          rootCoordinates.witnessFinish rootCoordinates.finish
            root.2.2.2.2.2.length
          finalStart finalFinish afterSequent.length :=
    (compactAdditiveNatListAppendSlices_iff_append
      hfirstLayout hsuffixLayout hendpointSuffixLayout).2 hsplit
  have happendGraph :
      CompactAdditiveNatListAppendSlices
        tokenTable width tokenCount
          rootCoordinates.gammaFinish rootCoordinates.firstFinish
            rootCoordinates.firstCount
          rootCoordinates.witnessFinish rootCoordinates.finish
            rootCoordinates.suffixCount
          finalStart finalFinish formulaCoordinates.inputCount := by
    simpa only [hfirstCount, hsuffixCount, hafterCount] using happendTyped
  have hsecondZero : rootCoordinates.secondCount = 0 := by
    simpa [root] using hsecondCount.symm
  have hwitnessZero : rootCoordinates.witnessCount = 0 := by
    simpa [root] using hwitnessCount.symm
  have hcoordinateTag : rootCoordinates.tag = 1 := by
    simpa [root] using hrootTagCoordinate
  have hconsCoordinateTag :
      CompactAdditiveNatListConsRows
        tokenTable width tokenCount sequentCoordinates.inputBoundary
          sequentCoordinates.inputCount inputBoundary input.length
          rootCoordinates.tag := by
    simpa only [hcoordinateTag] using hcons
  let coordinates : CompactProofRootOneFormulaEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := inputBoundarySize
      root := rootCoordinates
      rootSize := rootSize
      finalStart := finalStart
      finalFinish := finalFinish
      binderArity := 0
      sequent := sequentCoordinates
      formula := formulaCoordinates }
  have hgraph :
      CompactProofRootClosedFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
    unfold CompactProofRootClosedFormulaEndpointGraph
    dsimp only [coordinates]
    exact ⟨hinputWitness, hrootStart, hrootFinish, hrootCore,
      hcoordinateTag, rfl, hsecondZero, hwitnessZero,
      hconsCoordinateTag, hsequentGraph, hformulaGraph, happendGraph⟩
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
  let formulaCoordinateBound :=
    compactProofRootOneFormulaParserCoordinateSizeBound inputWeight
  have hformulaCoordinateBound :
      compactParserSyntaxExactEndpointPublicCoordinateSizeBound
          width tokenCount <= formulaCoordinateBound := by
    dsimp only [formulaCoordinateBound,
      compactProofRootOneFormulaParserCoordinateSizeBound,
      compactParserSyntaxExactEndpointPublicCoordinateSizeBound]
    exact
      compactSequentFormulaStepPublicCoordinateSizeBound_mono
        hwidthValue htokenCountValue
  let localBound :=
    compactProofRootOneFormulaLocalCoordinateSizeBound inputWeight
  have hsharedToLocal : sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootOneFormulaLocalCoordinateSizeBound]
    omega
  have hrootAreaToLocal :
      (sharedBound + 1) * sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootOneFormulaLocalCoordinateSizeBound]
    omega
  have hinputAreaToLocal :
      (inputWeight + 1) * sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootOneFormulaLocalCoordinateSizeBound]
    omega
  have hsequentToLocal : sequentCoordinateBound <= localBound := by
    dsimp only [sequentCoordinateBound, localBound,
      compactProofRootOneFormulaLocalCoordinateSizeBound]
    omega
  have hformulaToLocal : formulaCoordinateBound <= localBound := by
    dsimp only [formulaCoordinateBound, localBound,
      compactProofRootOneFormulaLocalCoordinateSizeBound]
    omega
  have hinputWeightToLocal : inputWeight <= localBound := by
    dsimp only [localBound,
      compactProofRootOneFormulaLocalCoordinateSizeBound]
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
  have hrootGammaArea :
      (rootCoordinates.gammaCount + 1) * tokenCount <=
        (sharedBound + 1) * sharedBound :=
    Nat.mul_le_mul
      (Nat.add_le_add_right
        (hrootBounds.gammaCount_le.trans htokenCountValue) 1)
      htokenCountValue
  have hrootGammaBoundarySize :
      Nat.size rootCoordinates.gammaBoundary <= localBound :=
    hrootBounds.gammaBoundary_size_le.trans
      (hrootGammaArea.trans hrootAreaToLocal)
  have hrootGammaBoundarySizeWitness :
      Nat.size rootSize.gammaBoundarySize <= localBound :=
    (natSize_le_of_le hrootBounds.gammaBoundarySize_le).trans
      (hrootGammaArea.trans hrootAreaToLocal)
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have hinputArea :
      (input.length + 1) * tokenCount <=
        (inputWeight + 1) * sharedBound :=
    Nat.mul_le_mul (Nat.add_le_add_right hinputLength 1)
      htokenCountValue
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
  have hfinalStartSize : Nat.size finalStart <= localBound :=
    hsequentPublic.finalStart_size_le.trans
      (hsequentCoordinateBound.trans hsequentToLocal)
  have hfinalFinishSize : Nat.size finalFinish <= localBound :=
    hsequentPublic.finalFinish_size_le.trans
      (hsequentCoordinateBound.trans hsequentToLocal)
  have hsequentSize
      {value : Nat}
      (hvalue :
        value ∈
          compactSequentFormulaEndpointCoordinateValues
            sequentCoordinates) :
      Nat.size value <= localBound :=
    (hsequentPublic.value_size_le value hvalue).trans
      (hsequentCoordinateBound.trans hsequentToLocal)
  have hformulaSize
      {value : Nat}
      (hvalue :
        value ∈
          compactParserSyntaxExactEndpointCoordinateValues
            formulaCoordinates) :
      Nat.size value <= localBound :=
    (hformulaPublic.value_size_le value hvalue).trans
      (hformulaCoordinateBound.trans hformulaToLocal)
  have hbinderAritySize : Nat.size 0 <= localBound := by
    simp
  let endpointBound := 2 ^ localBound
  have hbounded :
      CompactProofRootClosedFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
    unfold CompactProofRootClosedFormulaEndpointBoundedGraph
    refine
      ⟨inputBoundary, nat_le_two_pow_of_size_le hinputBoundarySize,
        input.length, nat_le_two_pow_of_size_le hinputCountSize,
        inputBoundarySize,
          nat_le_two_pow_of_size_le hinputBoundarySizeWitness,
        rootCoordinates.start,
          nat_le_two_pow_of_size_le (hrootSmall hrootBounds.start_le),
        rootCoordinates.finish,
          nat_le_two_pow_of_size_le (hrootSmall hrootBounds.finish_le),
        rootCoordinates.tag,
          nat_le_two_pow_of_size_le hrootTagSize,
        rootCoordinates.gammaFinish,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.gammaFinish_le),
        rootCoordinates.gammaCount,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.gammaCount_le),
        rootCoordinates.gammaBoundary,
          nat_le_two_pow_of_size_le hrootGammaBoundarySize,
        rootCoordinates.firstFinish,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.firstFinish_le),
        rootCoordinates.firstCount,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.firstCount_le),
        rootCoordinates.secondFinish,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.secondFinish_le),
        rootCoordinates.secondCount,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.secondCount_le),
        rootCoordinates.witnessFinish,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.witnessFinish_le),
        rootCoordinates.witnessCount,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.witnessCount_le),
        rootCoordinates.suffixCount,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.suffixCount_le),
        rootSize.gammaBoundarySize,
          nat_le_two_pow_of_size_le hrootGammaBoundarySizeWitness,
        finalStart, nat_le_two_pow_of_size_le hfinalStartSize,
        finalFinish, nat_le_two_pow_of_size_le hfinalFinishSize,
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
        sequentCoordinates.firstStart,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.firstFinish,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.firstBoundary,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.firstCount,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.firstBoundarySize,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.suffixBoundary,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.suffixCount,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.valueBoundary,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.valueCount,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.valueBoundarySize,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.finalBoundary,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.finalCount,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.finalBoundarySize,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.traceTableWidth,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.traceValueBound,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        0, nat_le_two_pow_of_size_le hbinderAritySize,
        formulaCoordinates.inputBoundary,
          nat_le_two_pow_of_size_le
            (hformulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        formulaCoordinates.inputCount,
          nat_le_two_pow_of_size_le
            (hformulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        formulaCoordinates.inputBoundarySize,
          nat_le_two_pow_of_size_le
            (hformulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        formulaCoordinates.expectedBoundary,
          nat_le_two_pow_of_size_le
            (hformulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        formulaCoordinates.expectedCount,
          nat_le_two_pow_of_size_le
            (hformulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        formulaCoordinates.expectedBoundarySize,
          nat_le_two_pow_of_size_le
            (hformulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        formulaCoordinates.stateBoundary,
          nat_le_two_pow_of_size_le
            (hformulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        formulaCoordinates.stateCount,
          nat_le_two_pow_of_size_le
            (hformulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        formulaCoordinates.tableWidth,
          nat_le_two_pow_of_size_le
            (hformulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        formulaCoordinates.valueBound,
          nat_le_two_pow_of_size_le
            (hformulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        ?_⟩
    simpa only [coordinates,
      compactProofRootClosedFormulaEndpointCoordinatesOfValues] using hgraph
  let publicBound :=
    compactProofRootOneFormulaPublicCoordinateSizeBound inputWeight
  have hlocalToPublic : localBound <= publicBound := by
    dsimp only [localBound, publicBound,
      compactProofRootOneFormulaPublicCoordinateSizeBound]
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
  have hendpointBoundPublic : Nat.size endpointBound <= publicBound := by
    dsimp only [endpointBound, publicBound,
      compactProofRootOneFormulaPublicCoordinateSizeBound]
    rw [Nat.size_pow]
  refine
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, endpointBound,
      ?_, hbounded, ?_⟩
  · simpa only [input] using hshared.inputLayout
  · exact
      { tokenTable :=
          hsharedPublic.tokenTable.trans hactualSharedToPublic
        width :=
          hsharedPublic.width_size.trans hactualSharedToPublic
        width_value := hwidthValue.trans hsharedToPublic
        tokenCount :=
          hsharedPublic.tokenCount_size.trans hactualSharedToPublic
        tokenCount_value := htokenCountValue.trans hsharedToPublic
        inputStart :=
          hsharedPublic.inputStart.trans hactualSharedToPublic
        inputFinish :=
          hsharedPublic.inputFinish.trans hactualSharedToPublic
        rootStart :=
          hsharedPublic.rootStart.trans hactualSharedToPublic
        rootFinish :=
          hsharedPublic.rootFinish.trans hactualSharedToPublic
        bodyStart :=
          hsharedPublic.bodyStart.trans hactualSharedToPublic
        bodyFinish :=
          hsharedPublic.bodyFinish.trans hactualSharedToPublic
        endpointBound := hendpointBoundPublic }

private theorem compactClosedParser_of_valueParser
    {tokens value suffix : List Nat}
    (hvalue : compactClosedFormulaTokenValueParser tokens =
      some (value, suffix)) :
    compactClosedFormulaTokenParser 0 tokens = some suffix := by
  unfold compactClosedFormulaTokenValueParser at hvalue
  cases hraw : compactClosedFormulaTokenParser 0 tokens with
  | none =>
      simp [hraw] at hvalue
  | some rawSuffix =>
      simp [hraw] at hvalue
      rcases hvalue with ⟨_hvalue, hsuffix⟩
      simpa [hsuffix] using hraw

/-- Every public root-parser success in tag `1` constructs the same bounded
closed-formula endpoint with no hidden coordinate inputs. -/
theorem
    exists_compactProofRootClosedFormulaEndpointBoundedGraph_of_success_with_publicBounds
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 1) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootClosedFormulaEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound ∧
        CompactProofRootOneFormulaPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound
            (compactProofRootOneFormulaPublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  rw [compactListedProofNodeFieldsParser_eq_some_iff_branchValid] at hparser
  cases input with
  | nil =>
      simp [CompactNumericProofRootBranchValid] at hparser
  | cons inputTag body =>
      have hinputTag : inputTag = 1 := by
        by_contra hne
        simp [CompactNumericProofRootBranchValid, hne, htag] at hparser
      subst inputTag
      have hfields : compactNodeSequentClosedFormulaFields body =
          some root.2 := by
        simpa [CompactNumericProofRootBranchValid, htag] using hparser
      cases hsequent : compactSequentTokenValueParser body with
      | none =>
          simp [compactNodeSequentClosedFormulaFields, hsequent] at hfields
      | some parsedSequent =>
          rcases parsedSequent with ⟨values, afterSequent⟩
          cases hclosedValue :
              compactClosedFormulaTokenValueParser afterSequent with
          | none =>
              simp [compactNodeSequentClosedFormulaFields, hsequent,
                hclosedValue] at hfields
          | some parsedFormula =>
              rcases parsedFormula with ⟨first, suffix⟩
              have hroot : root =
                  (1, (values, (first, ([], ([], suffix))))) := by
                simp [compactNodeSequentClosedFormulaFields, hsequent,
                  hclosedValue] at hfields
                exact Prod.ext htag (by simpa using hfields.symm)
              have hclosed := compactClosedParser_of_valueParser
                hclosedValue
              rcases
                  (compactClosedFormulaTokenParser_success_iff
                    0 afterSequent suffix).mp hclosed with
                ⟨formula, _hfree, hafterSequent⟩
              have hconsumed :
                  consumedTokenPrefix afterSequent suffix = first := by
                simpa [compactClosedFormulaTokenValueParser,
                  hclosed] using hclosedValue
              have hcanonical :
                  consumedTokenPrefix afterSequent suffix =
                    compactArithmeticFormulaTokens formula := by
                rw [hafterSequent]
                simp
              have hfirst : first =
                  compactArithmeticFormulaTokens formula :=
                hconsumed.symm.trans hcanonical
              have hsplit : afterSequent = first ++ suffix := by
                calc
                  afterSequent =
                      compactArithmeticFormulaTokens formula ++ suffix :=
                    hafterSequent
                  _ = first ++ suffix := by rw [hfirst]
              subst root
              simpa using
                exists_compactProofRootClosedFormulaEndpointBoundedGraph_of_results_with_publicBounds
                  body values afterSequent first suffix
                    hsequent hclosed hsplit

#print axioms
  exists_compactProofRootClosedFormulaEndpointBoundedGraph_of_results_with_publicBounds
#print axioms
  exists_compactProofRootClosedFormulaEndpointBoundedGraph_of_success_with_publicBounds

end FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds
