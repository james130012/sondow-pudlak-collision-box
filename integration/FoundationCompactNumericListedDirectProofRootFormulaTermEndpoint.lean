import integration.FoundationCompactNumericListedDirectProofRootCanonicalSharedRows
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
import integration.FoundationCompactNumericListedDirectNatListAppendSlices

/-!
# Exact endpoint for the formula-term proof-root branch

Tag 6 parses a sequent, one formula of binder arity one, and one closed term.
Both parser traces and the unique intermediate suffix share one token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootFormulaTermEndpoint

open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData
open FoundationCompactNumericListedDirectProofRootCanonicalSharedRows

structure CompactProofRootFormulaTermEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  root : CompactNumericVerifierTaskRowCoordinates
  rootSize : CompactNumericVerifierTaskSizeWitness
  finalStart : Nat
  finalFinish : Nat
  middleStart : Nat
  middleFinish : Nat
  sequent : CompactSequentFormulaEndpointCoordinates
  formula : CompactParserSyntaxExactEndpointCoordinates
  term : CompactParserSyntaxExactEndpointCoordinates

def CompactProofRootFormulaTermEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootFormulaTermEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount
        inputFinish coordinates.inputBoundary coordinates.inputBoundarySize ∧
    coordinates.root.start = rootStart ∧
    coordinates.root.finish = rootFinish ∧
    CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates.root coordinates.rootSize ∧
    coordinates.root.tag = 6 ∧
    coordinates.root.secondCount = 0 ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.sequent.inputBoundary coordinates.sequent.inputCount
        coordinates.inputBoundary coordinates.inputCount coordinates.root.tag ∧
    CompactSequentFormulaEndpointGraph
      tokenTable width tokenCount bodyStart bodyFinish
        (coordinates.root.start + 1) coordinates.root.gammaFinish
        coordinates.finalStart coordinates.finalFinish coordinates.sequent ∧
    CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount coordinates.finalStart coordinates.finalFinish
        coordinates.middleStart coordinates.middleFinish 1 1 0
        coordinates.formula ∧
    CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount coordinates.middleStart coordinates.middleFinish
        coordinates.root.witnessFinish coordinates.root.finish 0 0 0
        coordinates.term ∧
    CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.gammaFinish coordinates.root.firstFinish
          coordinates.root.firstCount
        coordinates.middleStart coordinates.middleFinish
          coordinates.formula.expectedCount
        coordinates.finalStart coordinates.finalFinish
          coordinates.formula.inputCount ∧
    CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.secondFinish coordinates.root.witnessFinish
          coordinates.root.witnessCount
        coordinates.root.witnessFinish coordinates.root.finish
          coordinates.root.suffixCount
        coordinates.middleStart coordinates.middleFinish
          coordinates.term.inputCount

theorem CompactProofRootFormulaTermEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootFormulaTermEndpointCoordinates}
    (hgraph : CompactProofRootFormulaTermEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish coordinates) :
    ∃ input : List Nat,
    ∃ root : CompactNumericProofRoot,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount rootStart rootFinish root ∧
      compactListedProofNodeFieldsParser input = some root := by
  rcases hgraph with
    ⟨hinputWitness, hrootStart, hrootFinish, hrootCore, htag,
      hsecondZero, hcons, hsequent, hformula, hterm,
      hformulaAppend, htermAppend⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨root, hrootLayout, hrootTag, hgammaRows, hgammaCount,
      hfirstLayout, hfirstCount, _hsecondLayout, hsecondCount,
      hwitnessLayout, hwitnessCount, hsuffixLayout, hsuffixCount⟩
  rw [hrootStart, hrootFinish] at hrootLayout
  rcases hsequent.sound with
    ⟨body, values, finalSuffix, hbodyLayout, hvaluesLayout,
      hfinalLayout, hsequentParser⟩
  rcases hsequent.1.realize with
    ⟨bodyRowsValue, hbodyCount, hbodyRowsLayout, hbodyRows⟩
  have hbodyEq : body = bodyRowsValue :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hbodyRowsLayout hbodyLayout).1
  subst body
  have hconsTyped : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.sequent.inputBoundary
        bodyRowsValue.length coordinates.inputBoundary input.length
        coordinates.root.tag := by
    simpa only [hbodyCount, hinputCount] using hcons
  have hinputEq : input = coordinates.root.tag :: bodyRowsValue :=
    CompactAdditiveNatListConsRows.eq_cons_of_rows
      hconsTyped hbodyRows hinputRows
  have hrootGammaLayout : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount (coordinates.root.start + 1)
        coordinates.root.gammaFinish root.2.1 := by
    have hgammaStructure := hrootCore.2.1
    rw [← hgammaCount] at hgammaStructure
    refine ⟨coordinates.root.gammaBoundary, hgammaStructure,
      hgammaRows, ?_⟩
    rw [hgammaCount]
    exact hrootCore.bounds.gammaBoundary_size_le
  have hgammaStartFinish :
      coordinates.root.start + 1 ≤ coordinates.root.gammaFinish := by
    rcases hrootGammaLayout with
      ⟨_gammaBoundary, hgammaStructure, _hgammaRows, _hgammaSize⟩
    rcases hgammaStructure with
      ⟨gammaBodyStart, _hgammaBodyStart, hgammaHeader, hgammaBoundary⟩
    have hbodyFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.start_le_finish
        hgammaBoundary
    have hbodyStart : gammaBodyStart = coordinates.root.start + 1 + 1 :=
      hgammaHeader.1.2.1
    omega
  have hgammaSlices : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
        (coordinates.root.start + 1) coordinates.root.gammaFinish
        (coordinates.root.start + 1) coordinates.root.gammaFinish :=
    CompactFixedWidthTokenSlicesEq.refl hgammaStartFinish
      hrootCore.bounds.gammaFinish_le
  have hvaluesEq : values = root.2.1 :=
    CompactFixedWidthTokenSlicesEq.natListListValues_eq
      hgammaSlices hrootGammaLayout hvaluesLayout
  rcases hformula.sound_formula with
    ⟨formulaInput, formulaSuffix, hformulaInputLayout,
      hformulaSuffixLayout, hformulaParser⟩
  rcases hterm.sound_term with
    ⟨termInput, termSuffix, htermInputLayout,
      htermSuffixLayout, htermParser⟩
  have hformulaInputEq : formulaInput = finalSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaInputLayout hfinalLayout).1.symm
  have hmiddleEq : formulaSuffix = termInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaSuffixLayout htermInputLayout).1.symm
  have htermSuffixEq : termSuffix = root.2.2.2.2.2 :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      htermSuffixLayout hsuffixLayout).1.symm
  rcases hformula.1.realize with
    ⟨formulaRowsInput, hformulaRowsInputCount,
      hformulaRowsInputLayout, _hformulaRowsInputRows⟩
  rcases hformula.2.1.realize with
    ⟨formulaRowsExpected, hformulaRowsExpectedCount,
      hformulaRowsExpectedLayout, _hformulaRowsExpectedRows⟩
  rcases hterm.1.realize with
    ⟨termRowsInput, htermRowsInputCount,
      htermRowsInputLayout, _htermRowsInputRows⟩
  have hformulaRowsInputEq : formulaRowsInput = formulaInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaRowsInputLayout hformulaInputLayout).1.symm
  have hformulaRowsExpectedEq : formulaRowsExpected = formulaSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaRowsExpectedLayout hformulaSuffixLayout).1.symm
  have htermRowsInputEq : termRowsInput = termInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      htermRowsInputLayout htermInputLayout).1.symm
  have hfinalCount : finalSuffix.length = coordinates.formula.inputCount := by
    rw [← hformulaInputEq, ← hformulaRowsInputEq]
    exact hformulaRowsInputCount
  have hformulaMiddleCount : formulaSuffix.length =
      coordinates.formula.expectedCount := by
    rw [← hformulaRowsExpectedEq]
    exact hformulaRowsExpectedCount
  have htermMiddleCount : termInput.length = coordinates.term.inputCount := by
    rw [← htermRowsInputEq]
    exact htermRowsInputCount
  have hformulaAppendTyped : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.gammaFinish coordinates.root.firstFinish
          root.2.2.1.length
        coordinates.middleStart coordinates.middleFinish formulaSuffix.length
        coordinates.finalStart coordinates.finalFinish finalSuffix.length := by
    simpa only [hfirstCount, hformulaMiddleCount, hfinalCount] using
      hformulaAppend
  have htermAppendTyped : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.secondFinish coordinates.root.witnessFinish
          root.2.2.2.2.1.length
        coordinates.root.witnessFinish coordinates.root.finish
          root.2.2.2.2.2.length
        coordinates.middleStart coordinates.middleFinish termInput.length := by
    simpa only [hwitnessCount, hsuffixCount, htermMiddleCount] using
      htermAppend
  have hformulaSplit : finalSuffix = root.2.2.1 ++ formulaSuffix :=
    (compactAdditiveNatListAppendSlices_iff_append
      hfirstLayout hformulaSuffixLayout hfinalLayout).mp hformulaAppendTyped
  have htermSplit : termInput =
      root.2.2.2.2.1 ++ root.2.2.2.2.2 :=
    (compactAdditiveNatListAppendSlices_iff_append
      hwitnessLayout hsuffixLayout htermInputLayout).mp htermAppendTyped
  have hformulaParser' : compactFormulaTokenParser 1 finalSuffix =
      some formulaSuffix := by
    simpa only [hformulaInputEq, hmiddleEq] using hformulaParser
  have htermParser' : compactTermTokenParser 0 termInput =
      some root.2.2.2.2.2 := by
    simpa only [htermSuffixEq] using htermParser
  have hformulaValueParser : compactFormulaTokenValueParser 1 finalSuffix =
      some (root.2.2.1, formulaSuffix) := by
    unfold compactFormulaTokenValueParser
    rw [hformulaParser']
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    simpa [hformulaSplit] using
      (consumedTokenPrefix_append root.2.2.1 formulaSuffix)
  have htermValueParser : compactTermTokenValueParser 0 termInput =
      some (root.2.2.2.2.1, root.2.2.2.2.2) := by
    unfold compactTermTokenValueParser
    rw [htermParser']
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    simpa [htermSplit] using
      (consumedTokenPrefix_append root.2.2.2.2.1 root.2.2.2.2.2)
  have hsecondEmpty : root.2.2.2.1 = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [hsecondCount, hsecondZero]
  have hfieldsEq : root.2 =
      (root.2.1, (root.2.2.1,
        (([] : List Nat), (root.2.2.2.2.1, root.2.2.2.2.2)))) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact hsecondEmpty
        · apply Prod.ext <;> rfl
  have hfields : compactNodeSequentFormulaTermFields 1 0 bodyRowsValue =
      some root.2 := by
    simp [compactNodeSequentFormulaTermFields,
      compactNodeSequentFormulaFields, compactNumericNodeFieldsSuffix,
      hsequentParser, hformulaValueParser, hmiddleEq,
      htermValueParser, hvaluesEq, ← hfieldsEq]
  have hrootParser : compactListedProofNodeFieldsParser input = some root := by
    apply (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).2
    rw [hinputEq]
    have hrootTag6 : root.1 = 6 := hrootTag.trans htag
    simpa [CompactNumericProofRootBranchValid, htag] using
      (And.intro hrootTag6 hfields)
  exact ⟨input, root, hinputLayout, hrootLayout, hrootParser⟩

theorem exists_compactProofRootFormulaTermEndpointGraph_of_results_with_inputLayout
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
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootFormulaTermEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFormulaTermEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  let input := 6 :: body
  let root : CompactNumericProofRoot :=
    (6, (values, (formula, ([], (term, suffix)))))
  rcases compactSequentTokenValueParser_sound hsequent with
    ⟨Gamma, hbody, hvalues⟩
  subst body
  subst values
  rcases
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        1 afterSequent middle).mp hformula with
    ⟨formulaStates, hformulaValid⟩
  rcases
      (compactTermTokenParser_eq_some_iff_exists_directTrace
        0 middle suffix).mp hterm with
    ⟨termStates, htermValid⟩
  rcases exists_compactSequentFormulaCanonicalDirectData Gamma afterSequent with
    ⟨sequentSuffixes, sequentParserTraces,
      hsequentSuffixCount, hsequentParserCount,
      hsequentFirst, hsequentFinal, hsequentSteps⟩
  rcases exists_compactProofRootCanonicalSharedRows
      input root (compactSequentListTokens Gamma ++ afterSequent)
        sequentSuffixes sequentParserTraces [middle]
          [formulaStates, termStates] with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish,
      sequentSuffixBoundary, _intermediateSuffixBoundary,
      hinputLayout, hrootLayout, hbodyLayout, hsequentSuffixRows,
      hsequentParserRows, hintermediateSuffixRows, hextraParserRows⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskDirectLayout.toCoreGraph
        hrootLayout with
    ⟨rootCoordinates, rootSize, hrootStart, hrootFinish,
      hrootTag, hrootCore⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaCount, hfirstLayout, hfirstCount,
      _hsecondLayout, hsecondCount, hwitnessLayout, hwitnessCount,
      hsuffixLayout, hsuffixCount⟩
  have hrealizedEq : realizedRoot = root :=
    FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hrootCore (by simpa [hrootStart, hrootFinish] using hrootLayout)
        hrealizedRoot
  subst realizedRoot
  have hgammaStructure := hrootCore.2.1
  rw [← hgammaCount] at hgammaStructure
  have hgammaSize : Nat.size rootCoordinates.gammaBoundary ≤
      (root.2.1.length + 1) * tokenCount := by
    rw [hgammaCount]
    exact hrootCore.bounds.gammaBoundary_size_le
  have hsequentParserRows' : ∀ index <
      (Gamma.map compactArithmeticFormulaTokens).length,
      ∃ parserStateBoundary,
        FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
          tokenTable width tokenCount parserStateBoundary
            (sequentParserTraces.getI index) := by
    intro index hindex
    apply hsequentParserRows index
    rw [hsequentParserCount]
    simpa using hindex
  have hsequentSteps' : ∀ index <
      (Gamma.map compactArithmeticFormulaTokens).length,
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
  have hsequentSuffixCount' : sequentSuffixes.length =
      (Gamma.map compactArithmeticFormulaTokens).length + 1 := by
    simpa using hsequentSuffixCount
  have hsequentParserCount' : sequentParserTraces.length =
      (Gamma.map compactArithmeticFormulaTokens).length := by
    simpa using hsequentParserCount
  have hbodyFirst : compactSequentListTokens Gamma ++ afterSequent =
      (Gamma.map compactArithmeticFormulaTokens).length ::
        sequentSuffixes.getI 0 := by
    rw [hsequentFirst]
    simp [compactSequentListTokens]
  have hsequentFinal' :
      sequentSuffixes.getI root.2.1.length = afterSequent := by
    simpa [root] using hsequentFinal
  rcases exists_compactSequentFormulaEndpointGraph_of_rows
      hbodyLayout hsequentSuffixRows hgammaStructure hgammaRows hgammaSize
      hsequentParserRows' hsequentSuffixCount' hsequentParserCount'
      hsequentSteps' hbodyFirst hsequentFinal' with
    ⟨finalStart, finalFinish, sequentCoordinates, hsequentGraph⟩
  rcases
      FoundationCompactNumericListedDirectNatListWitnessRows.CompactAdditiveNatListDirectLayout.exists_witnessRows
        hinputLayout with
    ⟨inputBoundary, inputBoundarySize, hinputWitness⟩
  rcases hinputWitness.realize with
    ⟨witnessInput, hwitnessInputCount, hwitnessInputLayout,
      hwitnessInputRows⟩
  have hwitnessInputEq : witnessInput = input :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hinputLayout hwitnessInputLayout).1
  subst witnessInput
  rcases hsequentGraph.1.realize with
    ⟨witnessBody, hwitnessBodyCount, hwitnessBodyLayout,
      hwitnessBodyRows⟩
  have hwitnessBodyEq : witnessBody =
      compactSequentListTokens Gamma ++ afterSequent :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hbodyLayout hwitnessBodyLayout).1
  subst witnessBody
  have hcons : CompactAdditiveNatListConsRows
      tokenTable width tokenCount sequentCoordinates.inputBoundary
        sequentCoordinates.inputCount inputBoundary input.length 6 := by
    have hraw :=
      CompactAdditiveStructuredListElementRowLayouts.natConsRows
        hwitnessBodyRows hwitnessInputRows
          (show input = 6 ::
            (compactSequentListTokens Gamma ++ afterSequent) by rfl)
    simpa only [hwitnessBodyCount, hwitnessInputCount] using hraw
  rcases hsequentGraph.sound with
    ⟨endpointBody, endpointValues, endpointSuffix,
      hendpointBodyLayout, _hendpointValuesLayout,
      hendpointSuffixLayout, hendpointParser⟩
  have hendpointBodyEq : endpointBody =
      compactSequentListTokens Gamma ++ afterSequent :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hbodyLayout hendpointBodyLayout).1
  subst endpointBody
  have hendpointResult :
      (endpointValues, endpointSuffix) =
        (Gamma.map compactArithmeticFormulaTokens, afterSequent) :=
    Option.some.inj (hendpointParser.symm.trans (by simpa using hsequent))
  have hendpointSuffixEq : endpointSuffix = afterSequent :=
    congrArg Prod.snd hendpointResult
  subst endpointSuffix
  rcases hintermediateSuffixRows 0 (by simp) with
    ⟨middleStart, _hmiddleStartBound, middleFinish, _hmiddleFinishBound,
      _hmiddleStartEntry, _hmiddleFinishEntry, hmiddleLayoutRaw⟩
  have hmiddleLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount middleStart middleFinish middle := by
    simpa using hmiddleLayoutRaw
  rcases hextraParserRows 0 (by simp) with
    ⟨formulaStateBoundary, hformulaStateRowsRaw⟩
  have hformulaStateRows :
      FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount formulaStateBoundary formulaStates := by
    simpa using hformulaStateRowsRaw
  rcases hextraParserRows 1 (by simp) with
    ⟨termStateBoundary, htermStateRowsRaw⟩
  have htermStateRows :
      FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount termStateBoundary termStates := by
    simpa using htermStateRowsRaw
  have hformulaStartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 1, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  have htermStartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(0, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  have hformulaLocal : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound afterSequent)
      (afterSequent, [(1, 1, 0)], none)
      (some middle) formulaStates := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hformulaValid
  have htermLocal : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound middle)
      (middle, [(0, 0, 0)], none) (some suffix) termStates := by
    simpa [CompactTermTokenParserDirectTraceValid,
      compactTermParserInitialState, compactTermTask] using htermValid
  rcases exists_compactParserSyntaxExactEndpointGraph_of_rows
      hendpointSuffixLayout hmiddleLayout hformulaStateRows
      hformulaStartWell hformulaLocal with
    ⟨formulaCoordinates, hformulaGraph⟩
  rcases exists_compactParserSyntaxExactEndpointGraph_of_rows
      hmiddleLayout hsuffixLayout htermStateRows
      htermStartWell htermLocal with
    ⟨termCoordinates, htermGraph⟩
  rcases hformulaGraph.1.realize with
    ⟨formulaInput, hformulaInputCount,
      hformulaInputLayout, _hformulaInputRows⟩
  rcases hformulaGraph.2.1.realize with
    ⟨formulaExpected, hformulaExpectedCount,
      hformulaExpectedLayout, _hformulaExpectedRows⟩
  rcases htermGraph.1.realize with
    ⟨termInput, htermInputCount,
      htermInputLayout, _htermInputRows⟩
  have hformulaInputEq : formulaInput = afterSequent :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hendpointSuffixLayout hformulaInputLayout).1
  have hformulaExpectedEq : formulaExpected = middle :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hmiddleLayout hformulaExpectedLayout).1
  have htermInputEq : termInput = middle :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hmiddleLayout htermInputLayout).1
  have hafterCount : afterSequent.length = formulaCoordinates.inputCount := by
    rw [← hformulaInputEq]
    exact hformulaInputCount
  have hmiddleFormulaCount : middle.length =
      formulaCoordinates.expectedCount := by
    rw [← hformulaExpectedEq]
    exact hformulaExpectedCount
  have hmiddleTermCount : middle.length = termCoordinates.inputCount := by
    rw [← htermInputEq]
    exact htermInputCount
  have hformulaAppendTyped : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        rootCoordinates.gammaFinish rootCoordinates.firstFinish
          root.2.2.1.length
        middleStart middleFinish middle.length
        finalStart finalFinish afterSequent.length :=
    (compactAdditiveNatListAppendSlices_iff_append
      hfirstLayout hmiddleLayout hendpointSuffixLayout).2 hformulaSplit
  have hformulaAppendGraph : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        rootCoordinates.gammaFinish rootCoordinates.firstFinish
          rootCoordinates.firstCount
        middleStart middleFinish formulaCoordinates.expectedCount
        finalStart finalFinish formulaCoordinates.inputCount := by
    simpa only [hfirstCount, hmiddleFormulaCount, hafterCount] using
      hformulaAppendTyped
  have htermAppendTyped : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        rootCoordinates.secondFinish rootCoordinates.witnessFinish
          root.2.2.2.2.1.length
        rootCoordinates.witnessFinish rootCoordinates.finish
          root.2.2.2.2.2.length
        middleStart middleFinish middle.length :=
    (compactAdditiveNatListAppendSlices_iff_append
      hwitnessLayout hsuffixLayout hmiddleLayout).2 htermSplit
  have htermAppendGraph : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        rootCoordinates.secondFinish rootCoordinates.witnessFinish
          rootCoordinates.witnessCount
        rootCoordinates.witnessFinish rootCoordinates.finish
          rootCoordinates.suffixCount
        middleStart middleFinish termCoordinates.inputCount := by
    simpa only [hwitnessCount, hsuffixCount, hmiddleTermCount] using
      htermAppendTyped
  have hsecondZero : rootCoordinates.secondCount = 0 := by
    simpa [root] using hsecondCount.symm
  have hcoordinateTag : rootCoordinates.tag = 6 := by
    simpa [root] using hrootTag
  have hconsCoordinateTag : CompactAdditiveNatListConsRows
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
      formula := formulaCoordinates
      term := termCoordinates }
  refine ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
    hinputLayout, ?_⟩
  unfold CompactProofRootFormulaTermEndpointGraph
  dsimp only [coordinates]
  exact ⟨hinputWitness, hrootStart, hrootFinish, hrootCore,
    hcoordinateTag, hsecondZero, hconsCoordinateTag, hsequentGraph,
    hformulaGraph, htermGraph, hformulaAppendGraph, htermAppendGraph⟩

theorem exists_compactProofRootFormulaTermEndpointGraph_of_results
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
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootFormulaTermEndpointCoordinates,
      CompactProofRootFormulaTermEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootFormulaTermEndpointGraph_of_results_with_inputLayout
        body values afterSequent formula middle term suffix hsequent
          hformula hterm hformulaSplit htermSplit with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates, hgraph⟩

private theorem compactFormulaParser_of_valueParser
    {tokens value suffix : List Nat}
    (hvalue : compactFormulaTokenValueParser 1 tokens =
      some (value, suffix)) :
    compactFormulaTokenParser 1 tokens = some suffix := by
  unfold compactFormulaTokenValueParser at hvalue
  cases hraw : compactFormulaTokenParser 1 tokens with
  | none => simp [hraw] at hvalue
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
  | none => simp [hraw] at hvalue
  | some rawSuffix =>
      simp [hraw] at hvalue
      rcases hvalue with ⟨_hvalue, hsuffix⟩
      simpa [hsuffix] using hraw

theorem exists_compactProofRootFormulaTermEndpointGraph_of_success_with_inputLayout
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 6) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootFormulaTermEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFormulaTermEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  rw [compactListedProofNodeFieldsParser_eq_some_iff_branchValid] at hparser
  cases input with
  | nil => simp [CompactNumericProofRootBranchValid] at hparser
  | cons inputTag body =>
      have hinputTag : inputTag = 6 := by
        by_contra hne
        simp [CompactNumericProofRootBranchValid, hne, htag] at hparser
      subst inputTag
      have hfields : compactNodeSequentFormulaTermFields 1 0 body =
          some root.2 := by
        simpa [CompactNumericProofRootBranchValid, htag] using hparser
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
                    exact Prod.ext htag (by simpa using hfields.symm)
                  rcases compactFormulaTokenValueParser_sound
                      hformulaValue with
                    ⟨parsed, hafterSequent, hformulaTokens⟩
                  rcases compactTermTokenValueParser_sound htermValue with
                    ⟨parsedTermValue, hmiddle, htermTokens⟩
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
                    exists_compactProofRootFormulaTermEndpointGraph_of_results_with_inputLayout
                      body values afterSequent formula middle term suffix
                        hsequent hformulaParser htermParser
                          hformulaSplit htermSplit

theorem exists_compactProofRootFormulaTermEndpointGraph_of_success
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 6) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootFormulaTermEndpointCoordinates,
      CompactProofRootFormulaTermEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootFormulaTermEndpointGraph_of_success_with_inputLayout
        hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates, hgraph⟩

#print axioms CompactProofRootFormulaTermEndpointGraph.sound
#print axioms exists_compactProofRootFormulaTermEndpointGraph_of_results
#print axioms exists_compactProofRootFormulaTermEndpointGraph_of_success

end FoundationCompactNumericListedDirectProofRootFormulaTermEndpoint
