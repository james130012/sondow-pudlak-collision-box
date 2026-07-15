import integration.FoundationCompactNumericListedDirectProofRootCanonicalSharedRows
import integration.FoundationCompactNumericListedDirectParserClosedEndpointFormula
import integration.FoundationCompactNumericListedDirectNatListAppendSlices
import integration.FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint

/-!
# Exact endpoint for the closed-formula proof-root branch

Tag 1 parses a sequent followed by a formula with no free variables.  The
closed-parser guard and every parser state share the root token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootClosedFormulaEndpoint

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
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
open FoundationCompactNumericListedDirectParserClosedEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData
open FoundationCompactNumericListedDirectProofRootCanonicalSharedRows

def CompactProofRootClosedFormulaEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootOneFormulaEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount
        inputFinish coordinates.inputBoundary coordinates.inputBoundarySize ∧
    coordinates.root.start = rootStart ∧
    coordinates.root.finish = rootFinish ∧
    CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates.root coordinates.rootSize ∧
    coordinates.root.tag = 1 ∧
    coordinates.binderArity = 0 ∧
    coordinates.root.secondCount = 0 ∧
    coordinates.root.witnessCount = 0 ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.sequent.inputBoundary coordinates.sequent.inputCount
        coordinates.inputBoundary coordinates.inputCount coordinates.root.tag ∧
    CompactSequentFormulaEndpointGraph
      tokenTable width tokenCount bodyStart bodyFinish
        (coordinates.root.start + 1) coordinates.root.gammaFinish
        coordinates.finalStart coordinates.finalFinish coordinates.sequent ∧
    CompactParserClosedEndpointGraph
      tokenTable width tokenCount coordinates.finalStart coordinates.finalFinish
        coordinates.root.witnessFinish coordinates.root.finish
        coordinates.binderArity coordinates.formula ∧
    CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.gammaFinish coordinates.root.firstFinish
          coordinates.root.firstCount
        coordinates.root.witnessFinish coordinates.root.finish
          coordinates.root.suffixCount
        coordinates.finalStart coordinates.finalFinish
          coordinates.formula.inputCount

theorem CompactProofRootClosedFormulaEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootOneFormulaEndpointCoordinates}
    (hgraph : CompactProofRootClosedFormulaEndpointGraph
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
    ⟨hinputWitness, hrootStart, hrootFinish, hrootCore,
      htag, hbinder, hsecondZero, hwitnessZero,
      hcons, hsequent, hclosed, happend⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨root, hrootLayout, hrootTag, hgammaRows, hgammaCount,
      hfirstLayout, hfirstCount, _hsecondLayout, hsecondCount,
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
      ⟨gammaBodyStart, _hgammaBodyStart, hgammaHeader,
        hgammaBoundary⟩
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
  rcases
      FoundationCompactNumericListedDirectParserClosedEndpointCompleteness.CompactParserClosedEndpointGraph.sound
        hclosed with
    ⟨closedInput, closedSuffix, hclosedInputLayout,
      hclosedSuffixLayout, hclosedParser⟩
  have hclosedInputEq : closedInput = finalSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hclosedInputLayout hfinalLayout).1.symm
  have hclosedSuffixEq : closedSuffix = root.2.2.2.2.2 :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hclosedSuffixLayout hsuffixLayout).1.symm
  rcases hclosed.1.realize with
    ⟨closedRowsInput, hclosedRowsInputCount,
      hclosedRowsInputLayout, _hclosedRowsInputRows⟩
  have hclosedRowsInputEq : closedRowsInput = closedInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hclosedRowsInputLayout hclosedInputLayout).1.symm
  have hfinalCount : finalSuffix.length = coordinates.formula.inputCount := by
    rw [← hclosedInputEq, ← hclosedRowsInputEq]
    exact hclosedRowsInputCount
  have happendTyped : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.gammaFinish coordinates.root.firstFinish
          root.2.2.1.length
        coordinates.root.witnessFinish coordinates.root.finish
          root.2.2.2.2.2.length
        coordinates.finalStart coordinates.finalFinish finalSuffix.length := by
    simpa only [hfirstCount, hsuffixCount, hfinalCount] using happend
  have hfinalSplit :
      finalSuffix = root.2.2.1 ++ root.2.2.2.2.2 :=
    (compactAdditiveNatListAppendSlices_iff_append
      hfirstLayout hsuffixLayout hfinalLayout).mp happendTyped
  have hclosedParser' : compactClosedFormulaTokenParser 0 finalSuffix =
      some root.2.2.2.2.2 := by
    simpa only [hbinder, hclosedInputEq, hclosedSuffixEq] using hclosedParser
  have hclosedValueParser :
      compactClosedFormulaTokenValueParser finalSuffix =
        some (root.2.2.1, root.2.2.2.2.2) := by
    unfold compactClosedFormulaTokenValueParser
    rw [hclosedParser']
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    simpa [hfinalSplit] using
      (consumedTokenPrefix_append root.2.2.1 root.2.2.2.2.2)
  have hsecondEmpty : root.2.2.2.1 = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [hsecondCount, hsecondZero]
  have hwitnessEmpty : root.2.2.2.2.1 = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [hwitnessCount, hwitnessZero]
  have hfieldsEq : root.2 =
      (root.2.1, (root.2.2.1,
        (([] : List Nat), (([] : List Nat), root.2.2.2.2.2)))) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact hsecondEmpty
        · apply Prod.ext
          · exact hwitnessEmpty
          · rfl
  have hfields : compactNodeSequentClosedFormulaFields bodyRowsValue =
      some root.2 := by
    simp [compactNodeSequentClosedFormulaFields, hsequentParser,
      hclosedValueParser, hvaluesEq, ← hfieldsEq]
  have hrootParser : compactListedProofNodeFieldsParser input = some root := by
    apply (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).2
    rw [hinputEq]
    have hrootTag1 : root.1 = 1 := hrootTag.trans htag
    simpa [CompactNumericProofRootBranchValid, htag] using
      (And.intro hrootTag1 hfields)
  exact ⟨input, root, hinputLayout, hrootLayout, hrootParser⟩

theorem exists_compactProofRootClosedFormulaEndpointGraph_of_results_with_inputLayout
    (body : List Nat) (values : List (List Nat))
    (afterSequent first suffix : List Nat)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hclosed : compactClosedFormulaTokenParser 0 afterSequent = some suffix)
    (hsplit : afterSequent = first ++ suffix) :
    let input := 1 :: body
    let root : CompactNumericProofRoot :=
      (1, (values, (first, ([], ([], suffix)))))
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootOneFormulaEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootClosedFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  let input := 1 :: body
  let root : CompactNumericProofRoot :=
    (1, (values, (first, ([], ([], suffix)))))
  rcases compactSequentTokenValueParser_sound hsequent with
    ⟨Gamma, hbody, hvalues⟩
  subst body
  subst values
  rcases
      (compactClosedFormulaTokenParser_eq_some_iff_exists_directTrace
        0 afterSequent suffix).mp hclosed with
    ⟨closedStates, hclosedValid⟩
  rcases exists_compactSequentFormulaCanonicalDirectData Gamma afterSequent with
    ⟨sequentSuffixes, sequentParserTraces,
      hsequentSuffixCount, hsequentParserCount,
      hsequentFirst, hsequentFinal, hsequentSteps⟩
  rcases exists_compactProofRootCanonicalSharedRows
      input root (compactSequentListTokens Gamma ++ afterSequent)
        sequentSuffixes sequentParserTraces [] [closedStates] with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish,
      sequentSuffixBoundary, _intermediateSuffixBoundary,
      hinputLayout, hrootLayout, hbodyLayout, hsequentSuffixRows,
      hsequentParserRows, _hintermediateSuffixRows, hextraParserRows⟩
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
      _hsecondLayout, hsecondCount, _hwitnessLayout, hwitnessCount,
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
        sequentCoordinates.inputCount inputBoundary input.length 1 := by
    have hraw :=
      CompactAdditiveStructuredListElementRowLayouts.natConsRows
        hwitnessBodyRows hwitnessInputRows
          (show input = 1 ::
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
  rcases hextraParserRows 0 (by simp) with
    ⟨closedStateBoundary, hclosedStateRowsRaw⟩
  have hclosedStateRows :
      FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount closedStateBoundary closedStates := by
    simpa using hclosedStateRowsRaw
  have hclosedStartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  have hclosedLocal : CompactParserOutputLocalTraceValid
      compactClosedSyntaxParserStep (compactSyntaxRunFuelBound afterSequent)
      (afterSequent, [(1, 0, 0)], none)
      (some suffix) closedStates := by
    simpa [CompactClosedFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hclosedValid
  rcases exists_compactParserClosedEndpointGraph_of_rows
      hendpointSuffixLayout hsuffixLayout hclosedStateRows
      hclosedStartWell hclosedLocal with
    ⟨closedCoordinates, hclosedGraph⟩
  rcases hclosedGraph.1.realize with
    ⟨closedInput, hclosedInputCount,
      hclosedInputLayout, _hclosedInputRows⟩
  have hclosedInputEq : closedInput = afterSequent :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hendpointSuffixLayout hclosedInputLayout).1
  have hafterCount : afterSequent.length = closedCoordinates.inputCount := by
    rw [← hclosedInputEq]
    exact hclosedInputCount
  have happendTyped : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        rootCoordinates.gammaFinish rootCoordinates.firstFinish
          root.2.2.1.length
        rootCoordinates.witnessFinish rootCoordinates.finish
          root.2.2.2.2.2.length
        finalStart finalFinish afterSequent.length :=
    (compactAdditiveNatListAppendSlices_iff_append
      hfirstLayout hsuffixLayout hendpointSuffixLayout).2 hsplit
  have happendGraph : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        rootCoordinates.gammaFinish rootCoordinates.firstFinish
          rootCoordinates.firstCount
        rootCoordinates.witnessFinish rootCoordinates.finish
          rootCoordinates.suffixCount
        finalStart finalFinish closedCoordinates.inputCount := by
    simpa only [hfirstCount, hsuffixCount, hafterCount] using happendTyped
  have hsecondZero : rootCoordinates.secondCount = 0 := by
    simpa [root] using hsecondCount.symm
  have hwitnessZero : rootCoordinates.witnessCount = 0 := by
    simpa [root] using hwitnessCount.symm
  have hcoordinateTag : rootCoordinates.tag = 1 := by
    simpa [root] using hrootTag
  have hconsCoordinateTag : CompactAdditiveNatListConsRows
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
      formula := closedCoordinates }
  refine ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
    hinputLayout, ?_⟩
  unfold CompactProofRootClosedFormulaEndpointGraph
  dsimp only [coordinates]
  exact ⟨hinputWitness, hrootStart, hrootFinish, hrootCore,
    hcoordinateTag, rfl, hsecondZero, hwitnessZero,
    hconsCoordinateTag, hsequentGraph, hclosedGraph, happendGraph⟩

theorem exists_compactProofRootClosedFormulaEndpointGraph_of_results
    (body : List Nat) (values : List (List Nat))
    (afterSequent first suffix : List Nat)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hclosed : compactClosedFormulaTokenParser 0 afterSequent = some suffix)
    (hsplit : afterSequent = first ++ suffix) :
    let input := 1 :: body
    let root : CompactNumericProofRoot :=
      (1, (values, (first, ([], ([], suffix)))))
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootOneFormulaEndpointCoordinates,
      CompactProofRootClosedFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootClosedFormulaEndpointGraph_of_results_with_inputLayout
        body values afterSequent first suffix hsequent hclosed hsplit with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates, hgraph⟩

private theorem compactClosedParser_of_valueParser
    {tokens value suffix : List Nat}
    (hvalue : compactClosedFormulaTokenValueParser tokens =
      some (value, suffix)) :
    compactClosedFormulaTokenParser 0 tokens = some suffix := by
  unfold compactClosedFormulaTokenValueParser at hvalue
  cases hraw : compactClosedFormulaTokenParser 0 tokens with
  | none => simp [hraw] at hvalue
  | some rawSuffix =>
      simp [hraw] at hvalue
      rcases hvalue with ⟨_hvalue, hsuffix⟩
      simpa [hsuffix] using hraw

theorem exists_compactProofRootClosedFormulaEndpointGraph_of_success_with_inputLayout
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 1) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootOneFormulaEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootClosedFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  rw [compactListedProofNodeFieldsParser_eq_some_iff_branchValid] at hparser
  cases input with
  | nil => simp [CompactNumericProofRootBranchValid] at hparser
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
                  afterSequent = compactArithmeticFormulaTokens formula ++
                      suffix := hafterSequent
                  _ = first ++ suffix := by rw [hfirst]
              subst root
              simpa using
                exists_compactProofRootClosedFormulaEndpointGraph_of_results_with_inputLayout
                  body values afterSequent first suffix
                    hsequent hclosed hsplit

theorem exists_compactProofRootClosedFormulaEndpointGraph_of_success
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 1) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootOneFormulaEndpointCoordinates,
      CompactProofRootClosedFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootClosedFormulaEndpointGraph_of_success_with_inputLayout
        hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates, hgraph⟩

#print axioms CompactProofRootClosedFormulaEndpointGraph.sound
#print axioms exists_compactProofRootClosedFormulaEndpointGraph_of_results
#print axioms exists_compactProofRootClosedFormulaEndpointGraph_of_success

end FoundationCompactNumericListedDirectProofRootClosedFormulaEndpoint
