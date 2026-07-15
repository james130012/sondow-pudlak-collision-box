import integration.FoundationCompactNumericListedDirectProofRootCanonicalSharedRows
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
import integration.FoundationCompactNumericListedDirectNatListAppendSlices

/-!
# Exact endpoint for one-formula proof-root branches

Tags 0, 5, and 9 parse a sequent followed by one formula.  This graph pins the
formula parser to the sequent's final suffix, the root's first field, and the
root's final suffix inside one shared token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint

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

structure CompactProofRootOneFormulaEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  root : CompactNumericVerifierTaskRowCoordinates
  rootSize : CompactNumericVerifierTaskSizeWitness
  finalStart : Nat
  finalFinish : Nat
  binderArity : Nat
  sequent : CompactSequentFormulaEndpointCoordinates
  formula : CompactParserSyntaxExactEndpointCoordinates

def CompactProofRootOneFormulaTagBinder
    (tag binderArity : Nat) : Prop :=
  (((tag = 0 ∨ tag = 9) ∧ binderArity = 0) ∨
    (tag = 5 ∧ binderArity = 1))

def CompactProofRootOneFormulaEndpointGraph
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
    CompactProofRootOneFormulaTagBinder
      coordinates.root.tag coordinates.binderArity ∧
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
    CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount coordinates.finalStart coordinates.finalFinish
        coordinates.root.witnessFinish coordinates.root.finish
        1 coordinates.binderArity 0 coordinates.formula ∧
    CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        coordinates.root.gammaFinish coordinates.root.firstFinish
          coordinates.root.firstCount
        coordinates.root.witnessFinish coordinates.root.finish
          coordinates.root.suffixCount
        coordinates.finalStart coordinates.finalFinish
          coordinates.formula.inputCount

/-- The one-formula endpoint graph reconstructs the exact public root parser
result for tags 0, 5, and 9. -/
theorem CompactProofRootOneFormulaEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootOneFormulaEndpointCoordinates}
    (hgraph : CompactProofRootOneFormulaEndpointGraph
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
    ⟨hinputWitness, hrootStart, hrootFinish, hrootCore, htagBinder,
      hsecondZero, hwitnessZero, hcons, hsequent, hformula, happend⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨root, hrootLayout, hrootTag, hgammaRows, hgammaCount,
      hfirstLayout, hfirstCount, hsecondLayout, hsecondCount,
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
      FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness.CompactParserSyntaxExactEndpointGraph.sound_formula
        hformula with
    ⟨formulaInput, formulaSuffix, hformulaInputLayout,
      hformulaSuffixLayout, hformulaParser⟩
  have hformulaInputEq : formulaInput = finalSuffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaInputLayout hfinalLayout).1.symm
  have hformulaSuffixEq : formulaSuffix = root.2.2.2.2.2 :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaSuffixLayout hsuffixLayout).1.symm
  rcases hformula.1.realize with
    ⟨formulaRowsInput, hformulaRowsInputCount,
      hformulaRowsInputLayout, _hformulaRowsInputRows⟩
  have hformulaRowsInputEq : formulaRowsInput = formulaInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaRowsInputLayout hformulaInputLayout).1.symm
  have hfinalCount : finalSuffix.length = coordinates.formula.inputCount := by
    rw [← hformulaInputEq, ← hformulaRowsInputEq]
    exact hformulaRowsInputCount
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
  have hformulaParser' :
      compactFormulaTokenParser coordinates.binderArity finalSuffix =
        some root.2.2.2.2.2 := by
    simpa only [hformulaInputEq, hformulaSuffixEq] using hformulaParser
  have hformulaValueParser :
      compactFormulaTokenValueParser coordinates.binderArity finalSuffix =
        some (root.2.2.1, root.2.2.2.2.2) := by
    unfold compactFormulaTokenValueParser
    rw [hformulaParser']
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
  have hfields :
      compactNodeSequentFormulaFields coordinates.binderArity bodyRowsValue =
        some root.2 := by
    simp [compactNodeSequentFormulaFields, hsequentParser,
      hformulaValueParser, hvaluesEq, ← hfieldsEq]
  have hrootParser : compactListedProofNodeFieldsParser input = some root := by
    apply (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).2
    rw [hinputEq]
    rcases htagBinder with ⟨htag09, hbinder0⟩ | ⟨htag5, hbinder1⟩
    · have hfields0 : compactNodeSequentFormulaFields 0 bodyRowsValue =
          some root.2 := by
        simpa only [hbinder0] using hfields
      rcases htag09 with htag0 | htag9
      · have hrootTag0 : root.1 = 0 := hrootTag.trans htag0
        simpa [CompactNumericProofRootBranchValid, htag0] using
          (And.intro hrootTag0 hfields0)
      · have hrootTag9 : root.1 = 9 := hrootTag.trans htag9
        simpa [CompactNumericProofRootBranchValid, htag9] using
          (And.intro hrootTag9 hfields0)
    · have hfields1 : compactNodeSequentFormulaFields 1 bodyRowsValue =
          some root.2 := by
        simpa only [hbinder1] using hfields
      have hrootTag5 : root.1 = 5 := hrootTag.trans htag5
      simpa [CompactNumericProofRootBranchValid, htag5] using
        (And.intro hrootTag5 hfields1)
  exact ⟨input, root, hinputLayout, hrootLayout, hrootParser⟩

/-- Every concrete successful one-formula branch constructs the complete
shared-table endpoint graph. -/
theorem exists_compactProofRootOneFormulaEndpointGraph_of_results_with_inputLayout
    (tag binderArity : Nat) (body : List Nat) (values : List (List Nat))
    (afterSequent first suffix : List Nat)
    (htagBinder : CompactProofRootOneFormulaTagBinder tag binderArity)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hformula : compactFormulaTokenParser binderArity afterSequent =
      some suffix)
    (hsplit : afterSequent = first ++ suffix) :
    let input := tag :: body
    let root : CompactNumericProofRoot :=
      (tag, (values, (first, ([], ([], suffix)))))
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootOneFormulaEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootOneFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  let input := tag :: body
  let root : CompactNumericProofRoot :=
    (tag, (values, (first, ([], ([], suffix)))))
  rcases compactSequentTokenValueParser_sound hsequent with
    ⟨Gamma, hbody, hvalues⟩
  subst body
  subst values
  rcases
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        binderArity afterSequent suffix).mp hformula with
    ⟨formulaStates, hformulaValid⟩
  rcases exists_compactSequentFormulaCanonicalDirectData Gamma afterSequent with
    ⟨sequentSuffixes, sequentParserTraces,
      hsequentSuffixCount, hsequentParserCount,
      hsequentFirst, hsequentFinal, hsequentSteps⟩
  rcases exists_compactProofRootCanonicalSharedRows
      input root (compactSequentListTokens Gamma ++ afterSequent)
        sequentSuffixes sequentParserTraces [] [formulaStates] with
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
  rcases hextraParserRows 0 (by simp) with
    ⟨formulaStateBoundary, hformulaStateRowsRaw⟩
  have hformulaStateRows :
      FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount formulaStateBoundary formulaStates := by
    simpa using hformulaStateRowsRaw
  have hformulaStartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, binderArity, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  have hformulaLocal : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound afterSequent)
      (afterSequent, [(1, binderArity, 0)], none)
      (some suffix) formulaStates := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hformulaValid
  rcases exists_compactParserSyntaxExactEndpointGraph_of_rows
      hendpointSuffixLayout hsuffixLayout hformulaStateRows
      hformulaStartWell hformulaLocal with
    ⟨formulaCoordinates, hformulaGraph⟩
  rcases hformulaGraph.1.realize with
    ⟨formulaInput, hformulaInputCount,
      hformulaInputLayout, _hformulaInputRows⟩
  have hformulaInputEq : formulaInput = afterSequent :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hendpointSuffixLayout hformulaInputLayout).1
  have hafterCount : afterSequent.length = formulaCoordinates.inputCount := by
    rw [← hformulaInputEq]
    exact hformulaInputCount
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
        finalStart finalFinish formulaCoordinates.inputCount := by
    simpa only [hfirstCount, hsuffixCount, hafterCount] using happendTyped
  have hsecondZero : rootCoordinates.secondCount = 0 := by
    simpa [root] using hsecondCount.symm
  have hwitnessZero : rootCoordinates.witnessCount = 0 := by
    simpa [root] using hwitnessCount.symm
  have hcoordinateTag : rootCoordinates.tag = tag := by
    simpa [root] using hrootTag
  have hcoordinateTagBinder :
      CompactProofRootOneFormulaTagBinder
        rootCoordinates.tag binderArity := by
    simpa only [hcoordinateTag] using htagBinder
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
      binderArity := binderArity
      sequent := sequentCoordinates
      formula := formulaCoordinates }
  refine ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
    hinputLayout, ?_⟩
  unfold CompactProofRootOneFormulaEndpointGraph
  dsimp only [coordinates]
  exact ⟨hinputWitness, hrootStart, hrootFinish, hrootCore,
    hcoordinateTagBinder, hsecondZero, hwitnessZero,
    hconsCoordinateTag, hsequentGraph, hformulaGraph, happendGraph⟩

theorem exists_compactProofRootOneFormulaEndpointGraph_of_results
    (tag binderArity : Nat) (body : List Nat) (values : List (List Nat))
    (afterSequent first suffix : List Nat)
    (htagBinder : CompactProofRootOneFormulaTagBinder tag binderArity)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hformula : compactFormulaTokenParser binderArity afterSequent =
      some suffix)
    (hsplit : afterSequent = first ++ suffix) :
    let input := tag :: body
    let root : CompactNumericProofRoot :=
      (tag, (values, (first, ([], ([], suffix)))))
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootOneFormulaEndpointCoordinates,
      CompactProofRootOneFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootOneFormulaEndpointGraph_of_results_with_inputLayout
        tag binderArity body values afterSequent first suffix
          htagBinder hsequent hformula hsplit with
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

private theorem exists_compactProofRootOneFormulaEndpointGraph_of_fields_with_inputLayout
    (tag binderArity : Nat) (body : List Nat)
    (root : CompactNumericProofRoot)
    (hrootTag : root.1 = tag)
    (htagBinder : CompactProofRootOneFormulaTagBinder tag binderArity)
    (hfields : compactNodeSequentFormulaFields binderArity body =
      some root.2) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootOneFormulaEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: body) ∧
        CompactProofRootOneFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  cases hsequent : compactSequentTokenValueParser body with
  | none => simp [compactNodeSequentFormulaFields, hsequent] at hfields
  | some parsedSequent =>
      rcases parsedSequent with ⟨values, afterSequent⟩
      cases hformulaValue :
          compactFormulaTokenValueParser binderArity afterSequent with
      | none =>
          simp [compactNodeSequentFormulaFields, hsequent,
            hformulaValue] at hfields
      | some parsedFormula =>
          rcases parsedFormula with ⟨first, suffix⟩
          have hroot : root =
              (tag, (values, (first, ([], ([], suffix))))) := by
            simp [compactNodeSequentFormulaFields, hsequent,
              hformulaValue] at hfields
            exact Prod.ext hrootTag (by simpa using hfields.symm)
          rcases compactFormulaTokenValueParser_sound hformulaValue with
            ⟨formula, hafterSequent, hfirst⟩
          have hsplit : afterSequent = first ++ suffix := by
            rw [hafterSequent, hfirst]
          have hformula := compactFormulaParser_of_valueParser hformulaValue
          subst root
          simpa using
            exists_compactProofRootOneFormulaEndpointGraph_of_results_with_inputLayout
              tag binderArity body values afterSequent first suffix
                htagBinder hsequent hformula hsplit

/-- Every public root-parser success in tags 0, 5, or 9 has a complete exact
endpoint witness. -/
theorem exists_compactProofRootOneFormulaEndpointGraph_of_success_with_inputLayout
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 0 ∨ root.1 = 5 ∨ root.1 = 9) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootOneFormulaEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootOneFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  rw [compactListedProofNodeFieldsParser_eq_some_iff_branchValid] at hparser
  cases input with
  | nil => simp [CompactNumericProofRootBranchValid] at hparser
  | cons inputTag body =>
      rcases htag with htag0 | htag59
      · have hinputTag : inputTag = 0 := by
          by_contra hne
          simp [CompactNumericProofRootBranchValid, hne, htag0] at hparser
        subst inputTag
        have hfields : compactNodeSequentFormulaFields 0 body =
            some root.2 := by
          simpa [CompactNumericProofRootBranchValid, htag0] using hparser
        exact exists_compactProofRootOneFormulaEndpointGraph_of_fields_with_inputLayout
          0 0 body root htag0 (Or.inl ⟨Or.inl rfl, rfl⟩) hfields
      · rcases htag59 with htag5 | htag9
        · have hinputTag : inputTag = 5 := by
            by_contra hne
            simp [CompactNumericProofRootBranchValid, hne, htag5] at hparser
          subst inputTag
          have hfields : compactNodeSequentFormulaFields 1 body =
              some root.2 := by
            simpa [CompactNumericProofRootBranchValid, htag5] using hparser
          exact exists_compactProofRootOneFormulaEndpointGraph_of_fields_with_inputLayout
            5 1 body root htag5 (Or.inr ⟨rfl, rfl⟩) hfields
        · have hinputTag : inputTag = 9 := by
            by_contra hne
            simp [CompactNumericProofRootBranchValid, hne, htag9] at hparser
          subst inputTag
          have hfields : compactNodeSequentFormulaFields 0 body =
              some root.2 := by
            simpa [CompactNumericProofRootBranchValid, htag9] using hparser
          exact exists_compactProofRootOneFormulaEndpointGraph_of_fields_with_inputLayout
            9 0 body root htag9 (Or.inl ⟨Or.inr rfl, rfl⟩) hfields

theorem exists_compactProofRootOneFormulaEndpointGraph_of_success
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 0 ∨ root.1 = 5 ∨ root.1 = 9) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootOneFormulaEndpointCoordinates,
      CompactProofRootOneFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootOneFormulaEndpointGraph_of_success_with_inputLayout
        hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates, hgraph⟩

#print axioms CompactProofRootOneFormulaEndpointGraph.sound
#print axioms exists_compactProofRootOneFormulaEndpointGraph_of_results
#print axioms exists_compactProofRootOneFormulaEndpointGraph_of_success

end FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint
