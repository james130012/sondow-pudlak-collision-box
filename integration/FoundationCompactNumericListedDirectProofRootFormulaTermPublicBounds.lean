import integration.FoundationCompactNumericListedDirectProofRootFormulaTermBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds

/-!
# Public bounds for formula-term proof-root success

Tag `6` parses a sequent followed by one formula and one term.  The intermediate
suffix and both complete parser traces are placed in the same canonical table.
Every local coordinate is bounded explicitly from the public input weight.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootFormulaTermPublicBounds

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
open FoundationCompactNumericListedDirectProofRootFormulaTermEndpoint
open FoundationCompactNumericListedDirectProofRootFormulaTermBoundedFormula
open FoundationCompactNumericListedDirectProofRootCanonicalSharedRowsPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData
open FoundationCompactNumericListedDirectSequentFormulaCanonicalDataPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedStateBounds

private theorem nat_le_two_pow_of_size_le
    {value sizeBound : Nat} (hsize : Nat.size value <= sizeBound) :
    value <= 2 ^ sizeBound :=
  (Nat.size_le.mp hsize).le

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

def compactProofRootFormulaTermPublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootFormulaTermLocalCoordinateSizeBound inputWeight + 1

theorem compactProofRootFormulaTermPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactProofRootFormulaTermPublicCoordinateSizeBound left <=
      compactProofRootFormulaTermPublicCoordinateSizeBound right := by
  have htask := compactNumericVerifierTaskWeightBound_mono h
  have hsuffixes :=
    compactSequentFormulaCanonicalSuffixesWeightBound_mono h
  have htraces :=
    compactSequentFormulaCanonicalParserTracesWeightBound_mono h
  have hparserTrace := compactNumericRootSyntaxParserTraceWeightBound_mono h
  have hextra :
      compactProofRootFormulaTermExtraParserWeightBound left <=
        compactProofRootFormulaTermExtraParserWeightBound right := by
    unfold compactProofRootFormulaTermExtraParserWeightBound
    omega
  have hintermediate :
      compactProofRootFormulaTermIntermediateSuffixWeightBound left <=
        compactProofRootFormulaTermIntermediateSuffixWeightBound right := by
    unfold compactProofRootFormulaTermIntermediateSuffixWeightBound
    omega
  have hdata :
      compactProofRootFormulaTermSharedDataWeightBound left <=
        compactProofRootFormulaTermSharedDataWeightBound right := by
    unfold compactProofRootFormulaTermSharedDataWeightBound
    omega
  have hshared :
      compactProofRootFormulaTermSharedCoordinateSizeBound left <=
        compactProofRootFormulaTermSharedCoordinateSizeBound right := by
    unfold compactProofRootFormulaTermSharedCoordinateSizeBound
    exact compactProofRootCanonicalSharedCoordinateSizeBound_mono hdata
  have hsequent :
      compactProofRootFormulaTermSequentCoordinateSizeBound left <=
        compactProofRootFormulaTermSequentCoordinateSizeBound right := by
    unfold compactProofRootFormulaTermSequentCoordinateSizeBound
    exact compactSequentFormulaEndpointPublicCoordinateSizeBound_mono
      hshared hshared
  have hparser :
      compactProofRootFormulaTermParserCoordinateSizeBound left <=
        compactProofRootFormulaTermParserCoordinateSizeBound right := by
    unfold compactProofRootFormulaTermParserCoordinateSizeBound
      compactParserSyntaxExactEndpointPublicCoordinateSizeBound
    exact compactSequentFormulaStepPublicCoordinateSizeBound_mono
      hshared hshared
  have hsharedArea :
      (compactProofRootFormulaTermSharedCoordinateSizeBound left + 1) *
          compactProofRootFormulaTermSharedCoordinateSizeBound left <=
        (compactProofRootFormulaTermSharedCoordinateSizeBound right + 1) *
          compactProofRootFormulaTermSharedCoordinateSizeBound right :=
    Nat.mul_le_mul (Nat.add_le_add_right hshared 1) hshared
  have hmixed :
      (left + 1) * compactProofRootFormulaTermSharedCoordinateSizeBound left <=
        (right + 1) *
          compactProofRootFormulaTermSharedCoordinateSizeBound right :=
    Nat.mul_le_mul (Nat.add_le_add_right h 1) hshared
  simp only [compactProofRootFormulaTermPublicCoordinateSizeBound,
    compactProofRootFormulaTermLocalCoordinateSizeBound]
  omega

structure CompactProofRootFormulaTermPublicCoordinateBounds
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

/-- A successful formula-term branch constructs its complete bounded endpoint
with a public coordinate budget. -/
theorem
    exists_compactProofRootFormulaTermEndpointBoundedGraph_of_results_with_publicBounds
    (body : List Nat) (values : List (List Nat))
    (afterSequent formula middle term suffix : List Nat)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hformula : compactFormulaTokenParser 1 afterSequent = some middle)
    (hterm : compactTermTokenParser 0 middle = some suffix)
    (hformulaSplit : afterSequent = formula ++ middle)
    (htermSplit : middle = term ++ suffix) :
    let input := 6 :: body
    let root : CompactNumericProofRoot :=
      (6, (values, (formula, ([], (term, suffix)))))
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFormulaTermEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound ∧
        CompactProofRootFormulaTermPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound
            (compactProofRootFormulaTermPublicCoordinateSizeBound
              inputWeight) := by
  let input := 6 :: body
  let root : CompactNumericProofRoot :=
    (6, (values, (formula, ([], (term, suffix)))))
  let inputWeight := compactAdditiveValueWeight input
  have hfirstValue :
      compactFormulaTokenValueParser 1 afterSequent =
        some (formula, middle) := by
    unfold compactFormulaTokenValueParser
    rw [hformula]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    simpa [hformulaSplit] using
      consumedTokenPrefix_append formula middle
  have hsecondValue :
      compactTermTokenValueParser 0 middle =
        some (term, suffix) := by
    unfold compactTermTokenValueParser
    rw [hterm]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    simpa [htermSplit] using consumedTokenPrefix_append term suffix
  have hfields :
      compactNodeSequentFormulaTermFields 1 0 body = some root.2 := by
    simp [root, compactNodeSequentFormulaTermFields,
      compactNodeSequentFormulaFields, compactNumericNodeFieldsSuffix,
      hsequent, hfirstValue, hsecondValue]
  have hrootParser :
      compactListedProofNodeFieldsParser input = some root := by
    apply (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).2
    simpa [input, root, CompactNumericProofRootBranchValid] using
      (And.intro (show root.1 = 6 by simp [root]) hfields)
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
      (show body <:+ input from ⟨[6], by simp [input]⟩)
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
      ⟨formula, hformulaSplit.symm⟩
    exact
      (compactAdditiveValueWeight_suffix_le hmiddleSuffix).trans
        hafterWeight
  rcases
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        1 afterSequent middle).mp hformula with
    ⟨firstStates, hfirstValid⟩
  rcases
      (compactTermTokenParser_eq_some_iff_exists_directTrace
        0 middle suffix).mp hterm with
    ⟨secondStates, hsecondValid⟩
  have hfirstStatesWeight :
      compactAdditiveValueWeight firstStates <=
        compactNumericRootSyntaxParserTraceWeightBound inputWeight :=
    compactFormulaTokenParserDirectTraceValid_weight_le_rootBound
      hfirstValid hafterWeight (by omega)
  have hsecondStatesWeight :
      compactAdditiveValueWeight secondStates <=
        compactNumericRootSyntaxParserTraceWeightBound inputWeight :=
    compactTermTokenParserDirectTraceValid_weight_le_rootBound
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
      _hsecondLayout, hsecondCount, hwitnessLayout, hwitnessCount,
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
      (hendpointParser.symm.trans (by simpa using hsequent))
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
        (some suffix) secondStates := by
    simpa [CompactTermTokenParserDirectTraceValid,
      compactTermParserInitialState, compactTermTask] using
        hsecondValid
  rcases
      exists_compactParserSyntaxExactEndpointGraph_of_rows_with_publicBounds
        hendpointSuffixLayout hmiddleLayout hfirstStateRows
        hfirstStateBoundarySize hformulaStartWell hfirstLocal with
    ⟨firstCoordinates, hfirstResult⟩
  have hfirstGraph := hfirstResult.1
  have hfirstPublic := hfirstResult.2.1
  rcases
      exists_compactParserSyntaxExactEndpointGraph_of_rows_with_publicBounds
        hmiddleLayout hsuffixLayout hsecondStateRows
        hsecondStateBoundarySize htermStartWell hsecondLocal with
    ⟨secondCoordinates, hsecondResult⟩
  have hsecondGraph := hsecondResult.1
  have hsecondPublic := hsecondResult.2.1
  rcases hfirstGraph.1.realize with
    ⟨firstInput, hfirstInputCount,
      hfirstInputLayout, _hfirstInputRows⟩
  rcases hfirstGraph.2.1.realize with
    ⟨firstExpected, hfirstExpectedCount,
      hfirstExpectedLayout, _hfirstExpectedRows⟩
  rcases hsecondGraph.1.realize with
    ⟨secondInput, hsecondInputCount,
      hsecondInputLayout, _hsecondInputRows⟩
  have hfirstInputEq : firstInput = afterSequent :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hendpointSuffixLayout hfirstInputLayout).1
  have hfirstExpectedEq : firstExpected = middle :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hmiddleLayout hfirstExpectedLayout).1
  have hsecondInputEq : secondInput = middle :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hmiddleLayout hsecondInputLayout).1
  have hafterCount :
      afterSequent.length = firstCoordinates.inputCount := by
    rw [← hfirstInputEq]
    exact hfirstInputCount
  have hmiddleFirstCount :
      middle.length = firstCoordinates.expectedCount := by
    rw [← hfirstExpectedEq]
    exact hfirstExpectedCount
  have hmiddleSecondCount :
      middle.length = secondCoordinates.inputCount := by
    rw [← hsecondInputEq]
    exact hsecondInputCount
  have hfirstAppendTyped :
      CompactAdditiveNatListAppendSlices
        tokenTable width tokenCount
          rootCoordinates.gammaFinish rootCoordinates.firstFinish
            root.2.2.1.length
          middleStart middleFinish middle.length
          finalStart finalFinish afterSequent.length :=
    (compactAdditiveNatListAppendSlices_iff_append
      hfirstLayout hmiddleLayout hendpointSuffixLayout).2 hformulaSplit
  have hfirstAppendGraph :
      CompactAdditiveNatListAppendSlices
        tokenTable width tokenCount
          rootCoordinates.gammaFinish rootCoordinates.firstFinish
            rootCoordinates.firstCount
          middleStart middleFinish firstCoordinates.expectedCount
          finalStart finalFinish firstCoordinates.inputCount := by
    simpa only [hfirstCount, hmiddleFirstCount, hafterCount] using
      hfirstAppendTyped
  have hsecondAppendTyped :
      CompactAdditiveNatListAppendSlices
        tokenTable width tokenCount
          rootCoordinates.secondFinish rootCoordinates.witnessFinish
            root.2.2.2.2.1.length
          rootCoordinates.witnessFinish rootCoordinates.finish
            root.2.2.2.2.2.length
          middleStart middleFinish middle.length :=
    (compactAdditiveNatListAppendSlices_iff_append
      hwitnessLayout hsuffixLayout hmiddleLayout).2 htermSplit
  have hsecondAppendGraph :
      CompactAdditiveNatListAppendSlices
        tokenTable width tokenCount
          rootCoordinates.secondFinish rootCoordinates.witnessFinish
            rootCoordinates.witnessCount
          rootCoordinates.witnessFinish rootCoordinates.finish
            rootCoordinates.suffixCount
          middleStart middleFinish secondCoordinates.inputCount := by
    simpa only [hwitnessCount, hsuffixCount, hmiddleSecondCount] using
      hsecondAppendTyped
  have hsecondZero : rootCoordinates.secondCount = 0 := by
    simpa [root] using hsecondCount.symm
  have hcoordinateTag : rootCoordinates.tag = 6 := by
    simpa [root] using hrootTagCoordinate
  have hconsCoordinateTag :
      CompactAdditiveNatListConsRows
        tokenTable width tokenCount sequentCoordinates.inputBoundary
          sequentCoordinates.inputCount inputBoundary input.length
          rootCoordinates.tag := by
    simpa only [hcoordinateTag] using hcons
  let coordinates : CompactProofRootFormulaTermEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := inputBoundarySize
      root := rootCoordinates
      rootSize := rootSize
      finalStart := finalStart
      finalFinish := finalFinish
      middleStart := middleStart
      middleFinish := middleFinish
      sequent := sequentCoordinates
      formula := firstCoordinates
      term := secondCoordinates }
  have hgraph :
      CompactProofRootFormulaTermEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
    unfold CompactProofRootFormulaTermEndpointGraph
    dsimp only [coordinates]
    exact ⟨hinputWitness, hrootStart, hrootFinish, hrootCore,
      hcoordinateTag, hsecondZero, hconsCoordinateTag,
      hsequentGraph, hfirstGraph, hsecondGraph,
      hfirstAppendGraph, hsecondAppendGraph⟩
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
  let localBound :=
    compactProofRootFormulaTermLocalCoordinateSizeBound inputWeight
  have hsharedToLocal : sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootFormulaTermLocalCoordinateSizeBound]
    omega
  have hrootAreaToLocal :
      (sharedBound + 1) * sharedBound <= localBound := by
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
  have hfirstFormulaSize
      {value : Nat}
      (hvalue :
        value ∈
          compactParserSyntaxExactEndpointCoordinateValues
            firstCoordinates) :
      Nat.size value <= localBound :=
    (hfirstPublic.value_size_le value hvalue).trans
      (hformulaCoordinateBound.trans hformulaToLocal)
  have hsecondFormulaSize
      {value : Nat}
      (hvalue :
        value ∈
          compactParserSyntaxExactEndpointCoordinateValues
            secondCoordinates) :
      Nat.size value <= localBound :=
    (hsecondPublic.value_size_le value hvalue).trans
      (hformulaCoordinateBound.trans hformulaToLocal)
  have hmiddleStartSize : Nat.size middleStart <= localBound :=
    hrootSmall hmiddleStartBound
  have hmiddleFinishSize : Nat.size middleFinish <= localBound :=
    hrootSmall hmiddleFinishBound
  let endpointBound := 2 ^ localBound
  have hbounded :
      CompactProofRootFormulaTermEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
    unfold CompactProofRootFormulaTermEndpointBoundedGraph
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
        firstCoordinates.inputBoundary,
          nat_le_two_pow_of_size_le
            (hfirstFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        firstCoordinates.inputCount,
          nat_le_two_pow_of_size_le
            (hfirstFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        firstCoordinates.inputBoundarySize,
          nat_le_two_pow_of_size_le
            (hfirstFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        firstCoordinates.expectedBoundary,
          nat_le_two_pow_of_size_le
            (hfirstFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        firstCoordinates.expectedCount,
          nat_le_two_pow_of_size_le
            (hfirstFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        firstCoordinates.expectedBoundarySize,
          nat_le_two_pow_of_size_le
            (hfirstFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        firstCoordinates.stateBoundary,
          nat_le_two_pow_of_size_le
            (hfirstFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        firstCoordinates.stateCount,
          nat_le_two_pow_of_size_le
            (hfirstFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        firstCoordinates.tableWidth,
          nat_le_two_pow_of_size_le
            (hfirstFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        firstCoordinates.valueBound,
          nat_le_two_pow_of_size_le
            (hfirstFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        middleStart, nat_le_two_pow_of_size_le hmiddleStartSize,
        middleFinish, nat_le_two_pow_of_size_le hmiddleFinishSize,
        secondCoordinates.inputBoundary,
          nat_le_two_pow_of_size_le
            (hsecondFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        secondCoordinates.inputCount,
          nat_le_two_pow_of_size_le
            (hsecondFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        secondCoordinates.inputBoundarySize,
          nat_le_two_pow_of_size_le
            (hsecondFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        secondCoordinates.expectedBoundary,
          nat_le_two_pow_of_size_le
            (hsecondFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        secondCoordinates.expectedCount,
          nat_le_two_pow_of_size_le
            (hsecondFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        secondCoordinates.expectedBoundarySize,
          nat_le_two_pow_of_size_le
            (hsecondFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        secondCoordinates.stateBoundary,
          nat_le_two_pow_of_size_le
            (hsecondFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        secondCoordinates.stateCount,
          nat_le_two_pow_of_size_le
            (hsecondFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        secondCoordinates.tableWidth,
          nat_le_two_pow_of_size_le
            (hsecondFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        secondCoordinates.valueBound,
          nat_le_two_pow_of_size_le
            (hsecondFormulaSize (by
              simp [compactParserSyntaxExactEndpointCoordinateValues])),
        ?_⟩
    simpa only [coordinates,
      compactProofRootFormulaTermEndpointCoordinatesOfValues] using hgraph
  let publicBound :=
    compactProofRootFormulaTermPublicCoordinateSizeBound inputWeight
  have hlocalToPublic : localBound <= publicBound := by
    dsimp only [localBound, publicBound,
      compactProofRootFormulaTermPublicCoordinateSizeBound]
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
  have hendpointBoundPublic : Nat.size endpointBound <= publicBound := by
    dsimp only [endpointBound, publicBound,
      compactProofRootFormulaTermPublicCoordinateSizeBound]
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

private theorem compactFormulaParser_of_valueParser
    {binderArity : Nat} {tokens value suffix : List Nat}
    (hvalue : compactFormulaTokenValueParser binderArity tokens =
      some (value, suffix)) :
    compactFormulaTokenParser binderArity tokens = some suffix := by
  unfold compactFormulaTokenValueParser at hvalue
  cases hraw : compactFormulaTokenParser binderArity tokens with
  | none =>
      simp [hraw] at hvalue
  | some rawSuffix =>
      simp [hraw] at hvalue
      rcases hvalue with ⟨_hvalue, hsuffix⟩
      simpa [hsuffix] using hraw

private theorem compactTermParser_of_valueParser
    {tokens value suffix : List Nat}
    (hvalue : compactTermTokenValueParser 0 tokens =
      some (value, suffix)) :
    compactTermTokenParser 0 tokens = some suffix := by
  unfold compactTermTokenValueParser at hvalue
  cases hraw : compactTermTokenParser 0 tokens with
  | none =>
      simp [hraw] at hvalue
  | some rawSuffix =>
      simp [hraw] at hvalue
      rcases hvalue with ⟨_hvalue, hsuffix⟩
      simpa [hsuffix] using hraw

private theorem
    exists_compactProofRootFormulaTermEndpointBoundedGraph_of_fields_with_publicBounds
    (body : List Nat) (root : CompactNumericProofRoot)
    (hrootTag : root.1 = 6)
    (hfields : compactNodeSequentFormulaTermFields 1 0 body = some root.2) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (6 :: body) ∧
        CompactProofRootFormulaTermEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound ∧
        CompactProofRootFormulaTermPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound
            (compactProofRootFormulaTermPublicCoordinateSizeBound
              (compactAdditiveValueWeight (6 :: body))) := by
  cases hsequent : compactSequentTokenValueParser body with
  | none =>
      simp [compactNodeSequentFormulaTermFields,
        compactNodeSequentFormulaFields, hsequent] at hfields
  | some parsedSequent =>
      rcases parsedSequent with ⟨values, afterSequent⟩
      cases hformulaValue :
          compactFormulaTokenValueParser 1 afterSequent with
      | none =>
          simp [compactNodeSequentFormulaTermFields,
            compactNodeSequentFormulaFields, hsequent,
            hformulaValue] at hfields
      | some parsedFormula =>
          rcases parsedFormula with ⟨formula, middle⟩
          cases htermValue : compactTermTokenValueParser 0 middle with
          | none =>
              simp [compactNodeSequentFormulaTermFields,
                compactNodeSequentFormulaFields,
                compactNumericNodeFieldsSuffix, hsequent,
                hformulaValue, htermValue] at hfields
          | some parsedTerm =>
              rcases parsedTerm with ⟨term, suffix⟩
              have hroot : root =
                  (6, (values, (formula, ([], (term, suffix))))) := by
                simp [compactNodeSequentFormulaTermFields,
                  compactNodeSequentFormulaFields,
                  compactNumericNodeFieldsSuffix, hsequent,
                  hformulaValue, htermValue] at hfields
                exact Prod.ext hrootTag (by simpa using hfields.symm)
              rcases compactFormulaTokenValueParser_sound
                  hformulaValue with
                ⟨_parsedFormula, hafterSequent, hformulaTokens⟩
              rcases compactTermTokenValueParser_sound htermValue with
                ⟨_parsedTerm, hmiddle, htermTokens⟩
              have hformulaSplit :
                  afterSequent = formula ++ middle := by
                rw [hafterSequent, hformulaTokens]
              have htermSplit : middle = term ++ suffix := by
                rw [hmiddle, htermTokens]
              have hformulaParser :=
                compactFormulaParser_of_valueParser hformulaValue
              have htermParser :=
                compactTermParser_of_valueParser htermValue
              subst root
              simpa using
                exists_compactProofRootFormulaTermEndpointBoundedGraph_of_results_with_publicBounds
                  body values afterSequent formula middle term suffix
                    hsequent hformulaParser htermParser
                      hformulaSplit htermSplit

/-- Every public root-parser success in tag `6` constructs the same
bounded formula-term endpoint with no hidden coordinate inputs. -/
theorem
    exists_compactProofRootFormulaTermEndpointBoundedGraph_of_success_with_publicBounds
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 6) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFormulaTermEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound ∧
        CompactProofRootFormulaTermPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound
            (compactProofRootFormulaTermPublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  rw [compactListedProofNodeFieldsParser_eq_some_iff_branchValid] at hparser
  cases input with
  | nil =>
      simp [CompactNumericProofRootBranchValid] at hparser
  | cons inputTag body =>
      have hinputTag : inputTag = 6 := by
        by_contra hne
        simp [CompactNumericProofRootBranchValid, hne, htag] at hparser
      subst inputTag
      have hfields : compactNodeSequentFormulaTermFields 1 0 body =
          some root.2 := by
        simpa [CompactNumericProofRootBranchValid, htag] using hparser
      exact
        exists_compactProofRootFormulaTermEndpointBoundedGraph_of_fields_with_publicBounds
          body root htag hfields

#print axioms
  exists_compactProofRootFormulaTermEndpointBoundedGraph_of_results_with_publicBounds
#print axioms
  exists_compactProofRootFormulaTermEndpointBoundedGraph_of_success_with_publicBounds

end FoundationCompactNumericListedDirectProofRootFormulaTermPublicBounds
