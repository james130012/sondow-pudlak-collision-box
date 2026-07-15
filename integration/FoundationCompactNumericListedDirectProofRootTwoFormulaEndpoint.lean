import integration.FoundationCompactNumericListedDirectProofRootCanonicalSharedRows
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
import integration.FoundationCompactNumericListedDirectNatListAppendSlices

/-!
# Exact endpoint for two-formula proof-root branches

Tags 3 and 4 parse a sequent followed by two formulas. Both parser traces, the
intermediate suffix, and both exact append decompositions share one token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootTwoFormulaEndpoint

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

structure CompactProofRootTwoFormulaEndpointCoordinates where
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
  firstFormula : CompactParserSyntaxExactEndpointCoordinates
  secondFormula : CompactParserSyntaxExactEndpointCoordinates

def CompactProofRootTwoFormulaEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootTwoFormulaEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount
        inputFinish coordinates.inputBoundary coordinates.inputBoundarySize ∧
    coordinates.root.start = rootStart ∧
    coordinates.root.finish = rootFinish ∧
    CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates.root coordinates.rootSize ∧
    (coordinates.root.tag = 3 ∨ coordinates.root.tag = 4) ∧
    coordinates.root.witnessCount = 0 ∧
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
        coordinates.middleStart coordinates.middleFinish 1 0 0
        coordinates.firstFormula ∧
    CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount coordinates.middleStart coordinates.middleFinish
        coordinates.root.witnessFinish coordinates.root.finish 1 0 0
        coordinates.secondFormula ∧
    CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.gammaFinish coordinates.root.firstFinish
          coordinates.root.firstCount
        coordinates.middleStart coordinates.middleFinish
          coordinates.firstFormula.expectedCount
        coordinates.finalStart coordinates.finalFinish
          coordinates.firstFormula.inputCount ∧
    CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.firstFinish coordinates.root.secondFinish
          coordinates.root.secondCount
        coordinates.root.witnessFinish coordinates.root.finish
          coordinates.root.suffixCount
        coordinates.middleStart coordinates.middleFinish
          coordinates.secondFormula.inputCount

theorem CompactProofRootTwoFormulaEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootTwoFormulaEndpointCoordinates}
    (hgraph : CompactProofRootTwoFormulaEndpointGraph
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
      hwitnessZero, hcons, hsequent, hfirstFormula, hsecondFormula,
      hfirstAppend, hsecondAppend⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨root, hrootLayout, hrootTag, hgammaRows, hgammaCount,
      hfirstLayout, hfirstCount, hsecondLayout, hsecondCount,
      _hwitnessLayout, hwitnessCount, hsuffixLayout, hsuffixCount⟩
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
  rcases hfirstFormula.sound_formula with
    ⟨firstInput, firstSuffix, hfirstInputLayout,
      hfirstSuffixLayout, hfirstParser⟩
  rcases hsecondFormula.sound_formula with
    ⟨secondInput, secondSuffix, hsecondInputLayout,
      hsecondSuffixLayout, hsecondParser⟩
  have hfirstInputEq : firstInput = finalSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfirstInputLayout hfinalLayout).1.symm
  have hmiddleEq : firstSuffix = secondInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfirstSuffixLayout hsecondInputLayout).1.symm
  have hsecondSuffixEq : secondSuffix = root.2.2.2.2.2 :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hsecondSuffixLayout hsuffixLayout).1.symm
  rcases hfirstFormula.1.realize with
    ⟨firstRowsInput, hfirstRowsInputCount,
      hfirstRowsInputLayout, _hfirstRowsInputRows⟩
  rcases hfirstFormula.2.1.realize with
    ⟨firstRowsExpected, hfirstRowsExpectedCount,
      hfirstRowsExpectedLayout, _hfirstRowsExpectedRows⟩
  rcases hsecondFormula.1.realize with
    ⟨secondRowsInput, hsecondRowsInputCount,
      hsecondRowsInputLayout, _hsecondRowsInputRows⟩
  have hfirstRowsInputEq : firstRowsInput = firstInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfirstRowsInputLayout hfirstInputLayout).1.symm
  have hfirstRowsExpectedEq : firstRowsExpected = firstSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfirstRowsExpectedLayout hfirstSuffixLayout).1.symm
  have hsecondRowsInputEq : secondRowsInput = secondInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hsecondRowsInputLayout hsecondInputLayout).1.symm
  have hfinalCount : finalSuffix.length =
      coordinates.firstFormula.inputCount := by
    rw [← hfirstInputEq, ← hfirstRowsInputEq]
    exact hfirstRowsInputCount
  have hfirstMiddleCount : firstSuffix.length =
      coordinates.firstFormula.expectedCount := by
    rw [← hfirstRowsExpectedEq]
    exact hfirstRowsExpectedCount
  have hsecondMiddleCount : secondInput.length =
      coordinates.secondFormula.inputCount := by
    rw [← hsecondRowsInputEq]
    exact hsecondRowsInputCount
  have hfirstAppendTyped : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.gammaFinish coordinates.root.firstFinish
          root.2.2.1.length
        coordinates.middleStart coordinates.middleFinish firstSuffix.length
        coordinates.finalStart coordinates.finalFinish finalSuffix.length := by
    simpa only [hfirstCount, hfirstMiddleCount, hfinalCount] using
      hfirstAppend
  have hsecondAppendTyped : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.firstFinish coordinates.root.secondFinish
          root.2.2.2.1.length
        coordinates.root.witnessFinish coordinates.root.finish
          root.2.2.2.2.2.length
        coordinates.middleStart coordinates.middleFinish secondInput.length := by
    simpa only [hsecondCount, hsuffixCount, hsecondMiddleCount] using
      hsecondAppend
  have hfirstSplit : finalSuffix = root.2.2.1 ++ firstSuffix :=
    (compactAdditiveNatListAppendSlices_iff_append
      hfirstLayout hfirstSuffixLayout hfinalLayout).mp hfirstAppendTyped
  have hsecondSplit : secondInput =
      root.2.2.2.1 ++ root.2.2.2.2.2 :=
    (compactAdditiveNatListAppendSlices_iff_append
      hsecondLayout hsuffixLayout hsecondInputLayout).mp hsecondAppendTyped
  have hfirstParser' : compactFormulaTokenParser 0 finalSuffix =
      some firstSuffix := by
    simpa only [hfirstInputEq, hmiddleEq] using hfirstParser
  have hsecondParser' : compactFormulaTokenParser 0 secondInput =
      some root.2.2.2.2.2 := by
    simpa only [hsecondSuffixEq] using hsecondParser
  have hfirstValueParser : compactFormulaTokenValueParser 0 finalSuffix =
      some (root.2.2.1, firstSuffix) := by
    unfold compactFormulaTokenValueParser
    rw [hfirstParser']
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    simpa [hfirstSplit] using
      (consumedTokenPrefix_append root.2.2.1 firstSuffix)
  have hsecondValueParser : compactFormulaTokenValueParser 0 secondInput =
      some (root.2.2.2.1, root.2.2.2.2.2) := by
    unfold compactFormulaTokenValueParser
    rw [hsecondParser']
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    simpa [hsecondSplit] using
      (consumedTokenPrefix_append root.2.2.2.1 root.2.2.2.2.2)
  have hwitnessEmpty : root.2.2.2.2.1 = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [hwitnessCount, hwitnessZero]
  have hfieldsEq : root.2 =
      (root.2.1, (root.2.2.1,
        (root.2.2.2.1, (([] : List Nat), root.2.2.2.2.2)))) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact hwitnessEmpty
          · rfl
  have hfields : compactNodeSequentTwoFormulaFields 0 bodyRowsValue =
      some root.2 := by
    simp [compactNodeSequentTwoFormulaFields,
      compactNodeSequentFormulaFields, compactNumericNodeFieldsSuffix,
      hsequentParser, hfirstValueParser, hmiddleEq,
      hsecondValueParser, hvaluesEq, ← hfieldsEq]
  have hrootParser : compactListedProofNodeFieldsParser input = some root := by
    apply (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).2
    rw [hinputEq]
    rcases htag with htag3 | htag4
    · have hrootTag3 : root.1 = 3 := hrootTag.trans htag3
      simpa [CompactNumericProofRootBranchValid, htag3] using
        (And.intro hrootTag3 hfields)
    · have hrootTag4 : root.1 = 4 := hrootTag.trans htag4
      simpa [CompactNumericProofRootBranchValid, htag4] using
        (And.intro hrootTag4 hfields)
  exact ⟨input, root, hinputLayout, hrootLayout, hrootParser⟩

theorem exists_compactProofRootTwoFormulaEndpointGraph_of_results_with_inputLayout
    (tag : Nat) (body : List Nat) (values : List (List Nat))
    (afterSequent first middle second suffix : List Nat)
    (htag : tag = 3 ∨ tag = 4)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hfirst : compactFormulaTokenParser 0 afterSequent = some middle)
    (hsecond : compactFormulaTokenParser 0 middle = some suffix)
    (hfirstSplit : afterSequent = first ++ middle)
    (hsecondSplit : middle = second ++ suffix) :
    let input := tag :: body
    let root : CompactNumericProofRoot :=
      (tag, (values, (first, (second, ([], suffix)))))
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootTwoFormulaEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootTwoFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  let input := tag :: body
  let root : CompactNumericProofRoot :=
    (tag, (values, (first, (second, ([], suffix)))))
  rcases compactSequentTokenValueParser_sound hsequent with
    ⟨Gamma, hbody, hvalues⟩
  subst body
  subst values
  rcases
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        0 afterSequent middle).mp hfirst with
    ⟨firstStates, hfirstValid⟩
  rcases
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        0 middle suffix).mp hsecond with
    ⟨secondStates, hsecondValid⟩
  rcases exists_compactSequentFormulaCanonicalDirectData Gamma afterSequent with
    ⟨sequentSuffixes, sequentParserTraces,
      hsequentSuffixCount, hsequentParserCount,
      hsequentFirst, hsequentFinal, hsequentSteps⟩
  rcases exists_compactProofRootCanonicalSharedRows
      input root (compactSequentListTokens Gamma ++ afterSequent)
        sequentSuffixes sequentParserTraces [middle]
          [firstStates, secondStates] with
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
      hsecondLayout, hsecondCount, _hwitnessLayout, hwitnessCount,
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
        sequentCoordinates.inputCount inputBoundary input.length tag := by
    have hraw :=
      CompactAdditiveStructuredListElementRowLayouts.natConsRows
        hwitnessBodyRows hwitnessInputRows
          (show input = tag ::
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
    ⟨firstStateBoundary, hfirstStateRowsRaw⟩
  have hfirstStateRows :
      FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount firstStateBoundary firstStates := by
    simpa using hfirstStateRowsRaw
  rcases hextraParserRows 1 (by simp) with
    ⟨secondStateBoundary, hsecondStateRowsRaw⟩
  have hsecondStateRows :
      FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount secondStateBoundary secondStates := by
    simpa using hsecondStateRowsRaw
  have hformulaStartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  have hfirstLocal : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound afterSequent)
      (afterSequent, [(1, 0, 0)], none) (some middle) firstStates := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hfirstValid
  have hsecondLocal : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound middle)
      (middle, [(1, 0, 0)], none) (some suffix) secondStates := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hsecondValid
  rcases exists_compactParserSyntaxExactEndpointGraph_of_rows
      hendpointSuffixLayout hmiddleLayout hfirstStateRows
      hformulaStartWell hfirstLocal with
    ⟨firstCoordinates, hfirstGraph⟩
  rcases exists_compactParserSyntaxExactEndpointGraph_of_rows
      hmiddleLayout hsuffixLayout hsecondStateRows
      hformulaStartWell hsecondLocal with
    ⟨secondCoordinates, hsecondGraph⟩
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
  have hafterCount : afterSequent.length = firstCoordinates.inputCount := by
    rw [← hfirstInputEq]
    exact hfirstInputCount
  have hmiddleFirstCount : middle.length =
      firstCoordinates.expectedCount := by
    rw [← hfirstExpectedEq]
    exact hfirstExpectedCount
  have hmiddleSecondCount : middle.length =
      secondCoordinates.inputCount := by
    rw [← hsecondInputEq]
    exact hsecondInputCount
  have hfirstAppendTyped : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        rootCoordinates.gammaFinish rootCoordinates.firstFinish
          root.2.2.1.length
        middleStart middleFinish middle.length
        finalStart finalFinish afterSequent.length :=
    (compactAdditiveNatListAppendSlices_iff_append
      hfirstLayout hmiddleLayout hendpointSuffixLayout).2 hfirstSplit
  have hfirstAppendGraph : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        rootCoordinates.gammaFinish rootCoordinates.firstFinish
          rootCoordinates.firstCount
        middleStart middleFinish firstCoordinates.expectedCount
        finalStart finalFinish firstCoordinates.inputCount := by
    simpa only [hfirstCount, hmiddleFirstCount, hafterCount] using
      hfirstAppendTyped
  have hsecondAppendTyped : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        rootCoordinates.firstFinish rootCoordinates.secondFinish
          root.2.2.2.1.length
        rootCoordinates.witnessFinish rootCoordinates.finish
          root.2.2.2.2.2.length
        middleStart middleFinish middle.length :=
    (compactAdditiveNatListAppendSlices_iff_append
      hsecondLayout hsuffixLayout hmiddleLayout).2 hsecondSplit
  have hsecondAppendGraph : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        rootCoordinates.firstFinish rootCoordinates.secondFinish
          rootCoordinates.secondCount
        rootCoordinates.witnessFinish rootCoordinates.finish
          rootCoordinates.suffixCount
        middleStart middleFinish secondCoordinates.inputCount := by
    simpa only [hsecondCount, hsuffixCount, hmiddleSecondCount] using
      hsecondAppendTyped
  have hwitnessZero : rootCoordinates.witnessCount = 0 := by
    simpa [root] using hwitnessCount.symm
  have hcoordinateTag : rootCoordinates.tag = tag := by
    simpa [root] using hrootTag
  have hcoordinateTagValid :
      rootCoordinates.tag = 3 ∨ rootCoordinates.tag = 4 := by
    simpa only [hcoordinateTag] using htag
  have hconsCoordinateTag : CompactAdditiveNatListConsRows
      tokenTable width tokenCount sequentCoordinates.inputBoundary
        sequentCoordinates.inputCount inputBoundary input.length
        rootCoordinates.tag := by
    simpa only [hcoordinateTag] using hcons
  let coordinates : CompactProofRootTwoFormulaEndpointCoordinates :=
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
      firstFormula := firstCoordinates
      secondFormula := secondCoordinates }
  refine ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
    hinputLayout, ?_⟩
  unfold CompactProofRootTwoFormulaEndpointGraph
  dsimp only [coordinates]
  exact ⟨hinputWitness, hrootStart, hrootFinish, hrootCore,
    hcoordinateTagValid, hwitnessZero, hconsCoordinateTag, hsequentGraph,
    hfirstGraph, hsecondGraph, hfirstAppendGraph, hsecondAppendGraph⟩

theorem exists_compactProofRootTwoFormulaEndpointGraph_of_results
    (tag : Nat) (body : List Nat) (values : List (List Nat))
    (afterSequent first middle second suffix : List Nat)
    (htag : tag = 3 ∨ tag = 4)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hfirst : compactFormulaTokenParser 0 afterSequent = some middle)
    (hsecond : compactFormulaTokenParser 0 middle = some suffix)
    (hfirstSplit : afterSequent = first ++ middle)
    (hsecondSplit : middle = second ++ suffix) :
    let input := tag :: body
    let root : CompactNumericProofRoot :=
      (tag, (values, (first, (second, ([], suffix)))))
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootTwoFormulaEndpointCoordinates,
      CompactProofRootTwoFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootTwoFormulaEndpointGraph_of_results_with_inputLayout
        tag body values afterSequent first middle second suffix htag
          hsequent hfirst hsecond hfirstSplit hsecondSplit with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates, hgraph⟩

private theorem compactFormulaParser_of_valueParser
    {binderArity : Nat} {tokens value suffix : List Nat}
    (hvalue : compactFormulaTokenValueParser binderArity tokens =
      some (value, suffix)) :
    compactFormulaTokenParser binderArity tokens = some suffix := by
  unfold compactFormulaTokenValueParser at hvalue
  cases hraw : compactFormulaTokenParser binderArity tokens with
  | none => simp [hraw] at hvalue
  | some rawSuffix =>
      simp [hraw] at hvalue
      rcases hvalue with ⟨_hvalue, hsuffix⟩
      simpa [hsuffix] using hraw

private theorem exists_compactProofRootTwoFormulaEndpointGraph_of_fields_with_inputLayout
    (tag : Nat) (body : List Nat) (root : CompactNumericProofRoot)
    (hrootTag : root.1 = tag) (htag : tag = 3 ∨ tag = 4)
    (hfields : compactNodeSequentTwoFormulaFields 0 body = some root.2) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootTwoFormulaEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: body) ∧
        CompactProofRootTwoFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  cases hsequent : compactSequentTokenValueParser body with
  | none =>
      simp [compactNodeSequentTwoFormulaFields,
        compactNodeSequentFormulaFields, hsequent] at hfields
  | some parsedSequent =>
      rcases parsedSequent with ⟨values, afterSequent⟩
      cases hfirstValue : compactFormulaTokenValueParser 0 afterSequent with
      | none =>
          simp [compactNodeSequentTwoFormulaFields,
            compactNodeSequentFormulaFields, hsequent, hfirstValue] at hfields
      | some parsedFirst =>
          rcases parsedFirst with ⟨first, middle⟩
          cases hsecondValue : compactFormulaTokenValueParser 0 middle with
          | none =>
              simp [compactNodeSequentTwoFormulaFields,
                compactNodeSequentFormulaFields, compactNumericNodeFieldsSuffix,
                hsequent, hfirstValue, hsecondValue] at hfields
          | some parsedSecond =>
              rcases parsedSecond with ⟨second, suffix⟩
              have hroot : root =
                  (tag, (values, (first, (second, ([], suffix))))) := by
                simp [compactNodeSequentTwoFormulaFields,
                  compactNodeSequentFormulaFields,
                  compactNumericNodeFieldsSuffix, hsequent,
                  hfirstValue, hsecondValue] at hfields
                exact Prod.ext hrootTag (by simpa using hfields.symm)
              rcases compactFormulaTokenValueParser_sound hfirstValue with
                ⟨firstFormula, hafterSequent, hfirstTokens⟩
              rcases compactFormulaTokenValueParser_sound hsecondValue with
                ⟨secondFormula, hmiddle, hsecondTokens⟩
              have hfirstSplit : afterSequent = first ++ middle := by
                rw [hafterSequent, hfirstTokens]
              have hsecondSplit : middle = second ++ suffix := by
                rw [hmiddle, hsecondTokens]
              have hfirstParser := compactFormulaParser_of_valueParser
                hfirstValue
              have hsecondParser := compactFormulaParser_of_valueParser
                hsecondValue
              subst root
              simpa using
                exists_compactProofRootTwoFormulaEndpointGraph_of_results_with_inputLayout
                  tag body values afterSequent first middle second suffix
                    htag hsequent hfirstParser hsecondParser
                      hfirstSplit hsecondSplit

theorem exists_compactProofRootTwoFormulaEndpointGraph_of_success_with_inputLayout
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 3 ∨ root.1 = 4) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootTwoFormulaEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootTwoFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  rw [compactListedProofNodeFieldsParser_eq_some_iff_branchValid] at hparser
  cases input with
  | nil => simp [CompactNumericProofRootBranchValid] at hparser
  | cons inputTag body =>
      rcases htag with htag3 | htag4
      · have hinputTag : inputTag = 3 := by
          by_contra hne
          simp [CompactNumericProofRootBranchValid, hne, htag3] at hparser
        subst inputTag
        have hfields : compactNodeSequentTwoFormulaFields 0 body =
            some root.2 := by
          simpa [CompactNumericProofRootBranchValid, htag3] using hparser
        exact exists_compactProofRootTwoFormulaEndpointGraph_of_fields_with_inputLayout
          3 body root htag3 (Or.inl rfl) hfields
      · have hinputTag : inputTag = 4 := by
          by_contra hne
          simp [CompactNumericProofRootBranchValid, hne, htag4] at hparser
        subst inputTag
        have hfields : compactNodeSequentTwoFormulaFields 0 body =
            some root.2 := by
          simpa [CompactNumericProofRootBranchValid, htag4] using hparser
        exact exists_compactProofRootTwoFormulaEndpointGraph_of_fields_with_inputLayout
          4 body root htag4 (Or.inr rfl) hfields

theorem exists_compactProofRootTwoFormulaEndpointGraph_of_success
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 3 ∨ root.1 = 4) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootTwoFormulaEndpointCoordinates,
      CompactProofRootTwoFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootTwoFormulaEndpointGraph_of_success_with_inputLayout
        hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates, hgraph⟩

#print axioms CompactProofRootTwoFormulaEndpointGraph.sound
#print axioms exists_compactProofRootTwoFormulaEndpointGraph_of_results
#print axioms exists_compactProofRootTwoFormulaEndpointGraph_of_success

end FoundationCompactNumericListedDirectProofRootTwoFormulaEndpoint
