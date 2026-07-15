import integration.FoundationCompactNumericListedDirectProofRootTwoFormulaFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootCanonicalSharedRows
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormula

/-!
# Completeness of second-formula proof-root failure

For tags three and four, a successful sequent trace, a successful first formula
trace, and the failed second formula trace are installed in one canonical token
table.  The auxiliary root row stores only the parsed sequent values; no theorem
assumes that it is a successful public root-parser output.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootTwoFormulaFailureCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData
open FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectProofRootCanonicalSharedRows
open FoundationCompactNumericListedDirectProofRootTwoFormulaFailureBoundedFormula

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

theorem exists_compactProofRootTwoFormulaFailureEndpointGraph_of_results_with_inputLayout
    (tag : Nat) (body : List Nat) (values : List (List Nat))
    (afterSequent secondInput : List Nat)
    (htag : tag = 3 ∨ tag = 4)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hfirst : compactFormulaTokenParser 0 afterSequent = some secondInput)
    (hsecond : compactFormulaTokenParser 0 secondInput = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootTwoFormulaFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: body) ∧
        CompactProofRootTwoFormulaFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish coordinates := by
  let input := tag :: body
  let root : CompactNumericProofRoot :=
    (tag, (values, ([], ([], ([], [])))))
  rcases compactSequentTokenValueParser_sound hsequent with
    ⟨Gamma, hbody, hvalues⟩
  subst body
  subst values
  rcases
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        0 afterSequent secondInput).mp hfirst with
    ⟨firstStates, hfirstValid⟩
  have hsecondOutput : compactSyntaxParserStateOutput
      ((compactSyntaxParserStep^[compactSyntaxRunFuelBound secondInput])
        (compactFormulaParserInitialState 0 secondInput)) = none := by
    simpa [compactFormulaTokenParser, compactFormulaTokenParserRun] using
      hsecond
  rcases (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound secondInput)
      (compactFormulaParserInitialState 0 secondInput) none).mp
        hsecondOutput with
    ⟨secondStates, hsecondValid⟩
  have hformulaStartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  have hfirstLocal : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound afterSequent)
      (afterSequent, [(1, 0, 0)], none) (some secondInput) firstStates := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hfirstValid
  have hsecondLocal : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound secondInput)
      (secondInput, [(1, 0, 0)], none) none secondStates := by
    simpa [compactFormulaParserInitialState, compactFormulaTask] using
      hsecondValid
  rcases exists_compactSequentFormulaCanonicalDirectData Gamma afterSequent with
    ⟨sequentSuffixes, sequentParserTraces,
      hsequentSuffixCount, hsequentParserCount,
      hsequentFirst, hsequentFinal, hsequentSteps⟩
  rcases exists_compactProofRootCanonicalSharedRows
      input root (compactSequentListTokens Gamma ++ afterSequent)
        sequentSuffixes sequentParserTraces [secondInput]
          [firstStates, secondStates] with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish,
      _sequentSuffixBoundary, _intermediateSuffixBoundary,
      hinputLayout, hrootLayout, hbodyLayout, hsequentSuffixRows,
      hsequentParserRows, hintermediateSuffixRows, hextraParserRows⟩
  rcases CompactNumericVerifierTaskDirectLayout.toCoreGraph hrootLayout with
    ⟨rootCoordinates, _rootSize, hrootStart, hrootFinish,
      _hrootTag, hrootCore⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaCount, _hfirstLayout, _hfirstCount,
      _hsecondLayout, _hsecondCount, _hwitnessLayout, _hwitnessCount,
      _hsuffixLayout, _hsuffixCount⟩
  have hrealizedEq : realizedRoot = root :=
    FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hrootCore (by
        simpa [hrootStart, hrootFinish] using hrootLayout) hrealizedRoot
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
        CompactUnifiedParserStateListRowLayouts
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
    ⟨secondStart, _hsecondStartBound, secondFinish, _hsecondFinishBound,
      _hsecondStartEntry, _hsecondFinishEntry, hsecondInputLayoutRaw⟩
  have hsecondInputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount secondStart secondFinish secondInput := by
    simpa using hsecondInputLayoutRaw
  rcases hextraParserRows 0 (by simp) with
    ⟨firstStateBoundary, hfirstStateRowsRaw⟩
  have hfirstStateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount firstStateBoundary firstStates := by
    simpa using hfirstStateRowsRaw
  rcases hextraParserRows 1 (by simp) with
    ⟨secondStateBoundary, hsecondStateRowsRaw⟩
  have hsecondStateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount secondStateBoundary secondStates := by
    simpa using hsecondStateRowsRaw
  rcases exists_compactParserSyntaxExactEndpointGraph_of_rows
      hendpointSuffixLayout hsecondInputLayout hfirstStateRows
      hformulaStartWell hfirstLocal with
    ⟨firstCoordinates, hfirstGraph⟩
  rcases exists_compactParserSyntaxNoOutputExactEndpointGraph_of_rows
      hsecondInputLayout hsecondStateRows hformulaStartWell hsecondLocal with
    ⟨failureCoordinates, hfailureGraph⟩
  rcases
      FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness.CompactSequentFormulaEndpointGraph.exists_bounded
        hsequentGraph with
    ⟨sequentBound, hsequentBounded⟩
  rcases
      FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula.CompactParserSyntaxExactEndpointGraph.exists_bounded
        hfirstGraph with
    ⟨firstBound, hfirstBounded⟩
  rcases
      FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula.CompactParserSyntaxNoOutputExactEndpointGraph.exists_bounded
        hfailureGraph with
    ⟨failureBound, hfailureBounded⟩
  let coordinates : CompactProofRootTwoFormulaFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := inputBoundarySize
      bodyBoundary := sequentCoordinates.inputBoundary
      bodyCount := sequentCoordinates.inputCount
      bodyBoundarySize := sequentCoordinates.inputBoundarySize
      tag := tag
      valueStart := rootCoordinates.start + 1
      valueFinish := rootCoordinates.gammaFinish
      firstStart := finalStart
      firstFinish := finalFinish
      secondStart := secondStart
      secondFinish := secondFinish
      sequentBound := sequentBound
      firstBound := firstBound
      failureBound := failureBound }
  refine ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, coordinates,
    by simpa [input] using hinputLayout, ?_⟩
  exact ⟨hinputWitness, hsequentGraph.1, htag, hcons,
    hsequentBounded, hfirstBounded, hfailureBounded⟩

theorem exists_compactProofRootTwoFormulaFailureEndpointGraph_of_results
    (tag : Nat) (body : List Nat) (values : List (List Nat))
    (afterSequent secondInput : List Nat)
    (htag : tag = 3 ∨ tag = 4)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hfirst : compactFormulaTokenParser 0 afterSequent = some secondInput)
    (hsecond : compactFormulaTokenParser 0 secondInput = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootTwoFormulaFailureEndpointCoordinates,
      CompactProofRootTwoFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootTwoFormulaFailureEndpointGraph_of_results_with_inputLayout
        tag body values afterSequent secondInput
          htag hsequent hfirst hsecond with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, coordinates, hgraph⟩

theorem exists_compactProofRootTwoFormulaFailureEndpointBoundedGraph_of_results
    (tag : Nat) (body : List Nat) (values : List (List Nat))
    (afterSequent secondInput : List Nat)
    (htag : tag = 3 ∨ tag = 4)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hfirst : compactFormulaTokenParser 0 afterSequent = some secondInput)
    (hsecond : compactFormulaTokenParser 0 secondInput = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactProofRootTwoFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  rcases exists_compactProofRootTwoFormulaFailureEndpointGraph_of_results
      tag body values afterSequent secondInput htag hsequent hfirst hsecond with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, endpointBound, hbounded⟩

theorem exists_compactProofRootTwoFormulaFailureEndpointBoundedGraph_of_results_with_inputLayout
    (tag : Nat) (body : List Nat) (values : List (List Nat))
    (afterSequent secondInput : List Nat)
    (htag : tag = 3 ∨ tag = 4)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hfirst : compactFormulaTokenParser 0 afterSequent = some secondInput)
    (hsecond : compactFormulaTokenParser 0 secondInput = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: body) ∧
        CompactProofRootTwoFormulaFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound := by
  rcases
      exists_compactProofRootTwoFormulaFailureEndpointGraph_of_results_with_inputLayout
        tag body values afterSequent secondInput
          htag hsequent hfirst hsecond with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, hinputLayout, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, endpointBound, hinputLayout, hbounded⟩

#print axioms exists_compactProofRootTwoFormulaFailureEndpointGraph_of_results
#print axioms exists_compactProofRootTwoFormulaFailureEndpointBoundedGraph_of_results

end FoundationCompactNumericListedDirectProofRootTwoFormulaFailureCompleteness
