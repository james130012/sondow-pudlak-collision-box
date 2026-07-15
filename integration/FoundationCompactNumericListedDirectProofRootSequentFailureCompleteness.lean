import integration.FoundationCompactNumericListedDirectProofRootSequentFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectSequentFormulaFailureEndpointCompleteness

/-!
# Completeness of the proof-root sequent-failure endpoint

For a nonempty failed sequent body, the outer proof-root input, that body, the
successful formula prefix, and the first failing formula trace are installed
in one canonical fixed-width table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootSequentFailureCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectSequentFormulaTraceCompleteness
open FoundationCompactNumericListedDirectSequentFormulaCanonicalLayouts
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectSequentFormulaFailureSemantics
open FoundationCompactNumericListedDirectSequentFormulaFailureEndpoint
open FoundationCompactNumericListedDirectSequentFormulaFailureBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaNoOutputBoundedFormula
open FoundationCompactNumericListedDirectProofRootSequentFailureBoundedFormula

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

private theorem structuredList_count_eq_of_same_start
    {tokenTable width tokenCount start
      leftCount leftFinish leftBoundary
      rightCount rightFinish rightBoundary : Nat}
    (hleft : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start leftCount leftFinish leftBoundary)
    (hright : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start rightCount rightFinish rightBoundary) :
    leftCount = rightCount := by
  rcases hleft with
    ⟨_leftBody, _hleftBody, hleftHeader, _hleftBoundary⟩
  rcases hright with
    ⟨_rightBody, _hrightBody, hrightHeader, _hrightBoundary⟩
  exact (CompactAdditiveTokenCell.value_eq_tableValue hleftHeader.1).trans
    (CompactAdditiveTokenCell.value_eq_tableValue hrightHeader.1).symm

theorem exists_compactProofRootSequentFailureEndpointGraph_of_cons_body_none_with_inputLayout
    (tag count : Nat) (inputTail : List Nat) (htag : tag ≤ 9)
    (hparser : compactSequentTokenValueParser (count :: inputTail) = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootSequentFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (tag :: count :: inputTail) ∧
        CompactProofRootSequentFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish coordinates := by
  rcases (compactSequentTokenValueParser_cons_eq_none_iff
      count inputTail).mp hparser with
    ⟨failedIndex, hfailedIndex, parsedValues, failedInput,
      hprefixRepeat, hfailedValueParser⟩
  have hfailedParser : compactFormulaTokenParser 0 failedInput = none := by
    simpa [compactFormulaTokenValueParser] using hfailedValueParser
  rcases compactFormulaTokenValuesRepeat_sound hprefixRepeat with
    ⟨Gamma, hGammaLength, hinputTail, hparsedValues⟩
  have hprefixRepeat' :
      compactFormulaTokenValuesRepeat Gamma.length inputTail =
        some (Gamma.map compactArithmeticFormulaTokens, failedInput) := by
    simpa only [hGammaLength, hparsedValues] using hprefixRepeat
  have hfailedIndex' : Gamma.length < count := by omega
  rcases exists_compactSequentFormulaCanonicalDirectData Gamma failedInput with
    ⟨suffixes, parserTraces, hsuffixCount, hparserCount,
      hfirst, hfinal, hsteps⟩
  have hfirstInputTail : suffixes.getI 0 = inputTail := by
    calc
      suffixes.getI 0 =
          Gamma.flatMap compactArithmeticFormulaTokens ++ failedInput := hfirst
      _ = inputTail := hinputTail.symm
  have houtput : compactSyntaxParserStateOutput
      ((compactSyntaxParserStep^[compactSyntaxRunFuelBound failedInput])
        (compactFormulaParserInitialState 0 failedInput)) = none := by
    simpa [compactFormulaTokenParser, compactFormulaTokenParserRun] using
      hfailedParser
  rcases (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound failedInput)
      (compactFormulaParserInitialState 0 failedInput) none).mp houtput with
    ⟨failureStates, hfailureValid⟩
  have hfailureLocal : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound failedInput)
      (failedInput, [(1, 0, 0)], none) none failureStates := by
    simpa [compactFormulaParserInitialState, compactFormulaTask] using
      hfailureValid
  have hfailureStartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  let rootInput := tag :: count :: inputTail
  let body := count :: inputTail
  let prefixInput := Gamma.length :: inputTail
  let formulaValues := Gamma.map compactArithmeticFormulaTokens
  let rootInputTokens := compactAdditiveEncode rootInput
  let bodyTokens := compactAdditiveEncode body
  let prefixInputTokens := compactAdditiveEncode prefixInput
  let suffixTokens := compactAdditiveEncode suffixes
  let valueTokens := compactAdditiveEncode formulaValues
  let parserTokens := compactAdditiveEncode parserTraces
  let failureStateTokens := compactAdditiveEncode failureStates
  let tokens := rootInputTokens ++ bodyTokens ++ prefixInputTokens ++
    suffixTokens ++ valueTokens ++ parserTokens ++ failureStateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hrootInputRaw := compactAdditiveNatListDirectLayout_canonical
    [] rootInput (bodyTokens ++ prefixInputTokens ++ suffixTokens ++
      valueTokens ++ parserTokens ++ failureStateTokens)
  dsimp only at hrootInputRaw
  have hrootInputTokenEq : [] ++ compactAdditiveEncode rootInput ++
      (bodyTokens ++ prefixInputTokens ++ suffixTokens ++
        valueTokens ++ parserTokens ++ failureStateTokens) = tokens := by
    simp [rootInputTokens, tokens, List.append_assoc]
  rw [hrootInputTokenEq] at hrootInputRaw
  have hbodyRaw := compactAdditiveNatListDirectLayout_canonical
    rootInputTokens body
      (prefixInputTokens ++ suffixTokens ++ valueTokens ++
        parserTokens ++ failureStateTokens)
  dsimp only at hbodyRaw
  have hbodyTokenEq : rootInputTokens ++ compactAdditiveEncode body ++
      (prefixInputTokens ++ suffixTokens ++ valueTokens ++
        parserTokens ++ failureStateTokens) = tokens := by
    simp [bodyTokens, tokens, List.append_assoc]
  rw [hbodyTokenEq] at hbodyRaw
  have hprefixInputRaw := compactAdditiveNatListDirectLayout_canonical
    (rootInputTokens ++ bodyTokens) prefixInput
      (suffixTokens ++ valueTokens ++ parserTokens ++ failureStateTokens)
  dsimp only at hprefixInputRaw
  have hprefixInputTokenEq : (rootInputTokens ++ bodyTokens) ++
      compactAdditiveEncode prefixInput ++
      (suffixTokens ++ valueTokens ++ parserTokens ++ failureStateTokens) =
        tokens := by
    simp [prefixInputTokens, tokens, List.append_assoc]
  rw [hprefixInputTokenEq] at hprefixInputRaw
  have hsuffixRaw := compactAdditiveNatListListDirectLayout_canonical
    (rootInputTokens ++ bodyTokens ++ prefixInputTokens) suffixes
      (valueTokens ++ parserTokens ++ failureStateTokens)
  dsimp only at hsuffixRaw
  have hsuffixTokenEq :
      (rootInputTokens ++ bodyTokens ++ prefixInputTokens) ++
        compactAdditiveEncode suffixes ++
        (valueTokens ++ parserTokens ++ failureStateTokens) = tokens := by
    simp [suffixTokens, tokens, List.append_assoc]
  rw [hsuffixTokenEq] at hsuffixRaw
  have hvalueRaw := compactAdditiveNatListListDirectLayout_canonical
    (rootInputTokens ++ bodyTokens ++ prefixInputTokens ++ suffixTokens)
      formulaValues (parserTokens ++ failureStateTokens)
  dsimp only at hvalueRaw
  have hvalueTokenEq :
      (rootInputTokens ++ bodyTokens ++ prefixInputTokens ++ suffixTokens) ++
        compactAdditiveEncode formulaValues ++
        (parserTokens ++ failureStateTokens) = tokens := by
    simp [valueTokens, tokens, List.append_assoc]
  rw [hvalueTokenEq] at hvalueRaw
  have hparserRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactUnifiedParserStateListDirectLayout
    compactUnifiedParserStateListDirectLayout_canonical
    (rootInputTokens ++ bodyTokens ++ prefixInputTokens ++ suffixTokens ++
      valueTokens) parserTraces failureStateTokens
  dsimp only at hparserRaw
  have hparserTokenEq :
      (rootInputTokens ++ bodyTokens ++ prefixInputTokens ++ suffixTokens ++
        valueTokens) ++ compactAdditiveEncode parserTraces ++
          failureStateTokens = tokens := by
    simp [parserTokens, tokens, List.append_assoc]
  rw [hparserTokenEq] at hparserRaw
  have hfailureStatesRaw :=
    FoundationCompactNumericListedDirectParserStateListLayout.compactUnifiedParserStateListDirectLayout_canonical
      (rootInputTokens ++ bodyTokens ++ prefixInputTokens ++ suffixTokens ++
        valueTokens ++ parserTokens) failureStates []
  dsimp only at hfailureStatesRaw
  have hfailureStateTokenEq :
      (rootInputTokens ++ bodyTokens ++ prefixInputTokens ++ suffixTokens ++
        valueTokens ++ parserTokens) ++
          compactAdditiveEncode failureStates ++ [] = tokens := by
    simp [failureStateTokens, tokens, List.append_assoc]
  rw [hfailureStateTokenEq] at hfailureStatesRaw
  have hrootInputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length 0 rootInputTokens.length rootInput := by
    simpa only [tokenTable, width, rootInputTokens,
      List.length_nil, Nat.zero_add] using hrootInputRaw
  have hbodyLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length rootInputTokens.length
        (rootInputTokens.length + bodyTokens.length) body := by
    simpa only [tokenTable, width, bodyTokens,
      List.length_append] using hbodyRaw
  have hprefixInputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (rootInputTokens.length + bodyTokens.length)
        (rootInputTokens.length + bodyTokens.length + prefixInputTokens.length)
        prefixInput := by
    simpa only [tokenTable, width, prefixInputTokens,
      List.length_append] using hprefixInputRaw
  rcases hsuffixRaw with
    ⟨suffixBoundary, _hsuffixStructure, hsuffixRows, _hsuffixSize⟩
  have hsuffixRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        suffixBoundary suffixes := by
    simpa only [tokenTable, width] using hsuffixRows
  rcases hvalueRaw with
    ⟨valueBoundary, hvalueStructure, hvalueRows, hvalueSize⟩
  have hvalueStructure' : CompactAdditiveStructuredListLayout
      tokenTable width tokens.length
        (rootInputTokens.length + bodyTokens.length +
          prefixInputTokens.length + suffixTokens.length)
        formulaValues.length
        (rootInputTokens.length + bodyTokens.length +
          prefixInputTokens.length + suffixTokens.length + valueTokens.length)
        valueBoundary := by
    simpa only [tokenTable, width, List.length_append]
      using hvalueStructure
  have hvalueRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        valueBoundary formulaValues := by
    simpa only [tokenTable, width] using hvalueRows
  have hvalueSize' : Nat.size valueBoundary ≤
      (formulaValues.length + 1) * tokens.length := by
    simpa only using hvalueSize
  have hparserRowsRaw := hparserRaw.2.1
  have hparserRows' : ∀ index < formulaValues.length,
      ∃ parserStateBoundary,
        CompactUnifiedParserStateListRowLayouts
          tokenTable width tokens.length parserStateBoundary
            (parserTraces.getI index) := by
    intro index hindex
    rcases hparserRowsRaw index (by
        rw [hparserCount]
        simpa [formulaValues] using hindex) with
      ⟨left, _hleftBound, right, _hrightBound,
        _hleftEntry, _hrightEntry, htraceLayout⟩
    rcases htraceLayout with
      ⟨parserStateBoundary, _htraceStructure,
        hparserStateRows, _hparserStateSize⟩
    exact ⟨parserStateBoundary, by
      simpa only [tokenTable, width] using hparserStateRows⟩
  rcases hfailureStatesRaw with
    ⟨_hfailureStateStructure, hfailureStateRows,
      _hfailureStateSize⟩
  have hfailureStateRows' : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokens.length
        (compactUnifiedParserStateBoundaryTable tokens.length
          ((rootInputTokens ++ bodyTokens ++ prefixInputTokens ++
            suffixTokens ++ valueTokens ++ parserTokens).length + 1)
          failureStates)
        failureStates := by
    simpa only [tokenTable, width] using hfailureStateRows
  have hsuffixCount' : suffixes.length = formulaValues.length + 1 := by
    simpa [formulaValues] using hsuffixCount
  have hparserCount' : parserTraces.length = formulaValues.length := by
    simpa [formulaValues] using hparserCount
  have hsteps' : ∀ index < formulaValues.length,
      CompactFormulaTokenParserDirectTraceValid
          0 (suffixes.getI index) (suffixes.getI (index + 1))
            (parserTraces.getI index) ∧
        suffixes.getI index =
          formulaValues.getI index ++ suffixes.getI (index + 1) := by
    intro index hindex
    simpa [formulaValues] using hsteps index (by
      simpa [formulaValues] using hindex)
  have hprefixInputEq : prefixInput =
      formulaValues.length :: suffixes.getI 0 := by
    simp [prefixInput, formulaValues, hfirstInputTail]
  have hfinalEq : suffixes.getI formulaValues.length = failedInput := by
    simpa [formulaValues] using hfinal
  rcases exists_compactSequentFormulaEndpointGraph_of_rows
      hprefixInputLayout hsuffixRows' hvalueStructure' hvalueRows'
      hvalueSize' hparserRows' hsuffixCount' hparserCount' hsteps'
      hprefixInputEq hfinalEq with
    ⟨failedStart, failedFinish, prefixCoordinates, hprefixGraph⟩
  have hprefixParts := hprefixGraph
  rcases hprefixParts with
    ⟨hprefixInputWitness, hfirstWitness, _hfinalWitness,
      _htraceGraph, _hfirstStartEntry, _hfirstFinishEntry,
      _hfinalStartEntry, _hfinalFinishEntry, hprefixCons,
      hprefixValueStructure, _hprefixValueSizeEq,
      _hprefixValueSize⟩
  have hvalueCountEq : prefixCoordinates.valueCount = formulaValues.length :=
    structuredList_count_eq_of_same_start
      hprefixValueStructure hvalueStructure'
  rcases hprefixInputWitness.realize with
    ⟨prefixInputFromRows, hprefixInputCount,
      hprefixInputFromRowsLayout, hprefixInputRows⟩
  rcases hfirstWitness.realize with
    ⟨firstFromRows, hfirstCount, _hfirstFromRowsLayout, hfirstRows⟩
  have hprefixInputFromRowsEq : prefixInputFromRows = prefixInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hprefixInputLayout hprefixInputFromRowsLayout).1
  have hprefixCons' : CompactAdditiveNatListConsRows
      tokenTable width tokens.length prefixCoordinates.firstBoundary
        firstFromRows.length prefixCoordinates.inputBoundary
        prefixInputFromRows.length prefixCoordinates.valueCount := by
    simpa only [hfirstCount, hprefixInputCount] using hprefixCons
  have hprefixInputFromRowsCons :
      prefixInputFromRows = prefixCoordinates.valueCount :: firstFromRows :=
    hprefixCons'.eq_cons_of_rows hfirstRows hprefixInputRows
  have hfirstFromRowsEq : firstFromRows = inputTail := by
    rw [hprefixInputFromRowsEq] at hprefixInputFromRowsCons
    simp only [prefixInput, List.cons.injEq] at hprefixInputFromRowsCons
    exact hprefixInputFromRowsCons.2.symm
  rcases hbodyLayout with
    ⟨bodyBoundary, hbodyStructure, hbodyElementRows, hbodySize⟩
  have hbodyWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length rootInputTokens.length body.length
        (rootInputTokens.length + bodyTokens.length)
        bodyBoundary (Nat.size bodyBoundary) :=
    ⟨hbodyStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hbodyElementRows,
      rfl, hbodySize⟩
  have hbodyEq : body = count :: firstFromRows := by
    simp [body, hfirstFromRowsEq]
  have hbodyCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length prefixCoordinates.firstBoundary
        firstFromRows.length bodyBoundary body.length count :=
    CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hfirstRows hbodyElementRows hbodyEq
  rcases hprefixGraph.sound with
    ⟨decodedPrefixInput, decodedValues, decodedFailedInput,
      hdecodedPrefixLayout, _hdecodedValueLayout,
      hdecodedFailedLayout, hdecodedPrefixParser⟩
  have hdecodedPrefixEq : decodedPrefixInput = prefixInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hprefixInputLayout hdecodedPrefixLayout).1
  rw [hdecodedPrefixEq] at hdecodedPrefixParser
  have hknownPrefixParser : compactSequentTokenValueParser prefixInput =
      some (formulaValues, failedInput) := by
    simpa [prefixInput, formulaValues, compactSequentTokenValueParser] using
      hprefixRepeat'
  have hdecodedPairEq :
      (decodedValues, decodedFailedInput) = (formulaValues, failedInput) :=
    Option.some.inj (hdecodedPrefixParser.symm.trans hknownPrefixParser)
  have hdecodedFailedEq : decodedFailedInput = failedInput :=
    congrArg Prod.snd hdecodedPairEq
  rw [hdecodedFailedEq] at hdecodedFailedLayout
  rcases exists_compactParserSyntaxNoOutputExactEndpointGraph_of_rows
      hdecodedFailedLayout hfailureStateRows'
      hfailureStartWell hfailureLocal with
    ⟨failureCoordinates, hfailureGraph⟩
  let failureCoordinates : CompactSequentFormulaFailureEndpointCoordinates :=
    { inputBoundary := bodyBoundary
      inputCount := body.length
      inputBoundarySize := Nat.size bodyBoundary
      count := count
      prefixInputStart := rootInputTokens.length + bodyTokens.length
      prefixInputFinish := rootInputTokens.length + bodyTokens.length +
        prefixInputTokens.length
      valueStart := rootInputTokens.length + bodyTokens.length +
        prefixInputTokens.length + suffixTokens.length
      valueFinish := rootInputTokens.length + bodyTokens.length +
        prefixInputTokens.length + suffixTokens.length + valueTokens.length
      failedStart := failedStart
      failedFinish := failedFinish
      prefixEndpoint := prefixCoordinates
      failureEndpoint := failureCoordinates }
  have hfailureExact : CompactSequentFormulaFailureEndpointGraph
      tokenTable width tokens.length rootInputTokens.length
        (rootInputTokens.length + bodyTokens.length)
        failureCoordinates := by
    unfold CompactSequentFormulaFailureEndpointGraph
    dsimp only [failureCoordinates]
    refine ⟨hbodyWitness, hprefixGraph, ?_, ?_, hfailureGraph⟩
    · rw [hvalueCountEq]
      simpa [formulaValues] using hfailedIndex'
    · simpa only [hfirstCount] using hbodyCons
  rcases exists_compactSequentFormulaFailureArithmeticGraph_of_exact
      hfailureExact with
    ⟨arithmeticCoordinates, harithmetic⟩
  rcases harithmetic.exists_bounded with
    ⟨sequentBound, hsequentFailure⟩
  have hsequent : CompactSequentFormulaNoOutputEndpointBoundedGraph
      tokenTable width tokens.length rootInputTokens.length
        (rootInputTokens.length + bodyTokens.length) sequentBound :=
    Or.inr hsequentFailure
  have hrootInputLayoutExact := hrootInputLayout
  rcases hrootInputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  have hinputWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 rootInput.length rootInputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputSize⟩
  have hrootInputEq : rootInput = tag :: body := by
    simp [rootInput, body]
  have hrootCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length bodyBoundary body.length
        inputBoundary rootInput.length tag :=
    CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hbodyElementRows hinputElementRows hrootInputEq
  let coordinates : CompactProofRootSequentFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := rootInput.length
      inputBoundarySize := Nat.size inputBoundary
      bodyBoundary := bodyBoundary
      bodyCount := body.length
      bodyBoundarySize := Nat.size bodyBoundary
      tag := tag
      sequentBound := sequentBound }
  refine ⟨tokenTable, width, tokens.length, 0, rootInputTokens.length,
    rootInputTokens.length, rootInputTokens.length + bodyTokens.length,
    coordinates, by simpa [rootInput] using hrootInputLayoutExact, ?_⟩
  exact ⟨hinputWitness, hbodyWitness, htag, hrootCons, hsequent⟩

theorem exists_compactProofRootSequentFailureEndpointGraph_of_cons_body_none
    (tag count : Nat) (inputTail : List Nat) (htag : tag ≤ 9)
    (hparser : compactSequentTokenValueParser (count :: inputTail) = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootSequentFailureEndpointCoordinates,
      CompactProofRootSequentFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootSequentFailureEndpointGraph_of_cons_body_none_with_inputLayout
        tag count inputTail htag hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, coordinates, hgraph⟩

theorem exists_compactProofRootSequentFailureEndpointBoundedGraph_of_cons_body_none
    (tag count : Nat) (inputTail : List Nat) (htag : tag ≤ 9)
    (hparser : compactSequentTokenValueParser (count :: inputTail) = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactProofRootSequentFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  rcases exists_compactProofRootSequentFailureEndpointGraph_of_cons_body_none
      tag count inputTail htag hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, endpointBound, hbounded⟩

theorem exists_compactProofRootSequentFailureEndpointBoundedGraph_of_cons_body_none_with_inputLayout
    (tag count : Nat) (inputTail : List Nat) (htag : tag ≤ 9)
    (hparser : compactSequentTokenValueParser (count :: inputTail) = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (tag :: count :: inputTail) ∧
        CompactProofRootSequentFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound := by
  rcases
      exists_compactProofRootSequentFailureEndpointGraph_of_cons_body_none_with_inputLayout
        tag count inputTail htag hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, hinputLayout, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, endpointBound, hinputLayout, hbounded⟩

theorem exists_compactProofRootSequentFailureEndpointBoundedGraph_of_none
    (tag : Nat) (body : List Nat) (htag : tag ≤ 9)
    (hparser : compactSequentTokenValueParser body = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactProofRootSequentFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  cases body with
  | nil =>
      exact
        exists_compactProofRootSequentFailureEndpointBoundedGraph_of_empty_body
          tag htag
  | cons count inputTail =>
      exact
        exists_compactProofRootSequentFailureEndpointBoundedGraph_of_cons_body_none
          tag count inputTail htag hparser

theorem exists_compactProofRootSequentFailureEndpointBoundedGraph_of_none_with_inputLayout
    (tag : Nat) (body : List Nat) (htag : tag ≤ 9)
    (hparser : compactSequentTokenValueParser body = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: body) ∧
        CompactProofRootSequentFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound := by
  cases body with
  | nil =>
      simpa using
        exists_compactProofRootSequentFailureEndpointBoundedGraph_of_empty_body_with_inputLayout
          tag htag
  | cons count inputTail =>
      exact
        exists_compactProofRootSequentFailureEndpointBoundedGraph_of_cons_body_none_with_inputLayout
          tag count inputTail htag hparser

#print axioms exists_compactProofRootSequentFailureEndpointGraph_of_cons_body_none
#print axioms exists_compactProofRootSequentFailureEndpointBoundedGraph_of_cons_body_none
#print axioms exists_compactProofRootSequentFailureEndpointBoundedGraph_of_none

end FoundationCompactNumericListedDirectProofRootSequentFailureCompleteness
