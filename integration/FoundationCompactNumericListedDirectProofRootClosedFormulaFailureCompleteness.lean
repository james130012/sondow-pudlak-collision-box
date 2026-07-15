import integration.FoundationCompactNumericListedDirectProofRootClosedFormulaFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootCanonicalSharedRows

/-!
# Completeness of closed-formula proof-root failure

The tag-one input, successful sequent trace, and failed closed-formula trace
are installed in one canonical table.  This includes failures caused only by
the closed parser's free-variable check.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootClosedFormulaFailureCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
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
open FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointFormula
open FoundationCompactNumericListedDirectProofRootCanonicalSharedRows
open FoundationCompactNumericListedDirectProofRootClosedFormulaFailureBoundedFormula

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

theorem exists_compactProofRootClosedFormulaFailureEndpointGraph_of_results_with_inputLayout
    (body : List Nat) (values : List (List Nat)) (afterSequent : List Nat)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hformula : compactClosedFormulaTokenParser 0 afterSequent = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootClosedFormulaFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (1 :: body) ∧
        CompactProofRootClosedFormulaFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish coordinates := by
  let input := 1 :: body
  let root : CompactNumericProofRoot :=
    (1, (values, ([], ([], ([], [])))))
  rcases compactSequentTokenValueParser_sound hsequent with
    ⟨Gamma, hbody, hvalues⟩
  subst body
  subst values
  have houtput : compactSyntaxParserStateOutput
      ((compactClosedSyntaxParserStep^[compactSyntaxRunFuelBound afterSequent])
        (compactFormulaParserInitialState 0 afterSequent)) = none := by
    simpa [compactClosedFormulaTokenParser,
      compactClosedFormulaTokenParserRun] using hformula
  rcases (compactParserOutput_eq_iff_exists_localTrace
      compactClosedSyntaxParserStep (compactSyntaxRunFuelBound afterSequent)
      (compactFormulaParserInitialState 0 afterSequent) none).mp houtput with
    ⟨formulaStates, hformulaValid⟩
  have hformulaLocal : CompactParserOutputLocalTraceValid
      compactClosedSyntaxParserStep (compactSyntaxRunFuelBound afterSequent)
      (afterSequent, [(1, 0, 0)], none) none formulaStates := by
    simpa [compactFormulaParserInitialState, compactFormulaTask] using
      hformulaValid
  have hformulaStartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
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
    ⟨formulaStateBoundary, hformulaStateRowsRaw⟩
  have hformulaStateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount formulaStateBoundary formulaStates := by
    simpa using hformulaStateRowsRaw
  rcases exists_compactParserClosedNoOutputExactEndpointGraph_of_rows
      hendpointSuffixLayout hformulaStateRows
      hformulaStartWell hformulaLocal with
    ⟨failureCoordinates, hfailureGraph⟩
  rcases
      FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness.CompactSequentFormulaEndpointGraph.exists_bounded
        hsequentGraph with
    ⟨sequentBound, hsequentBounded⟩
  rcases
      FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointFormula.CompactParserClosedNoOutputExactEndpointGraph.exists_bounded
        hfailureGraph with
    ⟨failureBound, hfailureBounded⟩
  let coordinates : CompactProofRootClosedFormulaFailureEndpointCoordinates :=
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
      sequentBound := sequentBound
      failureBound := failureBound }
  refine ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, coordinates,
    by simpa [input] using hinputLayout, ?_⟩
  exact ⟨hinputWitness, hsequentGraph.1, hcons,
    hsequentBounded, hfailureBounded⟩

theorem exists_compactProofRootClosedFormulaFailureEndpointGraph_of_results
    (body : List Nat) (values : List (List Nat)) (afterSequent : List Nat)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hformula : compactClosedFormulaTokenParser 0 afterSequent = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootClosedFormulaFailureEndpointCoordinates,
      CompactProofRootClosedFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootClosedFormulaFailureEndpointGraph_of_results_with_inputLayout
        body values afterSequent hsequent hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, coordinates, hgraph⟩

theorem exists_compactProofRootClosedFormulaFailureEndpointBoundedGraph_of_results
    (body : List Nat) (values : List (List Nat)) (afterSequent : List Nat)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hformula : compactClosedFormulaTokenParser 0 afterSequent = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactProofRootClosedFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  rcases exists_compactProofRootClosedFormulaFailureEndpointGraph_of_results
      body values afterSequent hsequent hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, endpointBound, hbounded⟩

theorem exists_compactProofRootClosedFormulaFailureEndpointBoundedGraph_of_results_with_inputLayout
    (body : List Nat) (values : List (List Nat)) (afterSequent : List Nat)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hformula : compactClosedFormulaTokenParser 0 afterSequent = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (1 :: body) ∧
        CompactProofRootClosedFormulaFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound := by
  rcases
      exists_compactProofRootClosedFormulaFailureEndpointGraph_of_results_with_inputLayout
        body values afterSequent hsequent hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, hinputLayout, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, endpointBound, hinputLayout, hbounded⟩

#print axioms exists_compactProofRootClosedFormulaFailureEndpointGraph_of_results
#print axioms exists_compactProofRootClosedFormulaFailureEndpointBoundedGraph_of_results

end FoundationCompactNumericListedDirectProofRootClosedFormulaFailureCompleteness
