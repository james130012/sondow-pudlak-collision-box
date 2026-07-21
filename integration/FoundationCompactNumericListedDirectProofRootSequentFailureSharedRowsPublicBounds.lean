import integration.FoundationCompactNumericListedDirectProofRootSequentFailureCompleteness

/-!
# Public shared rows for proof-root sequent failure

The nonempty sequent-failure branch uses one canonical table containing the
root input, its body, the successful-prefix input, all parser suffixes and
values, the successful parser traces, and the first failed parser trace.  This
module installs those seven regions while retaining public bounds for the
table code and every exposed outer position.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootSequentFailureSharedRowsPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectSequentFormulaCanonicalLayouts

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

def compactProofRootSequentFailureSharedDataWeight
    (rootInput body prefixInput : List Nat)
    (suffixes formulaValues : List (List Nat))
    (parserTraces : List CompactFormulaTokenParserDirectTrace)
    (failureStates : CompactFormulaTokenParserDirectTrace) : Nat :=
  compactAdditiveValueWeight rootInput +
    compactAdditiveValueWeight body +
    compactAdditiveValueWeight prefixInput +
    compactAdditiveValueWeight suffixes +
    compactAdditiveValueWeight formulaValues +
    compactAdditiveValueWeight parserTraces +
    compactAdditiveValueWeight failureStates

def compactProofRootSequentFailureSharedCoordinateSizeBound
    (dataWeight : Nat) : Nat :=
  dataWeight * (2 * dataWeight) +
    2 * dataWeight + dataWeight + 10

structure CompactProofRootSequentFailureSharedTablePublicBounds
    (tokenTable width tokenCount
      rootInputStart rootInputFinish bodyStart bodyFinish
      prefixInputStart prefixInputFinish valueStart valueFinish
      failureStart failureFinish bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width_size : Nat.size width <= bound
  width_value : width <= bound
  tokenCount_size : Nat.size tokenCount <= bound
  tokenCount_value : tokenCount <= bound
  rootInputStart : Nat.size rootInputStart <= bound
  rootInputFinish : Nat.size rootInputFinish <= bound
  bodyStart : Nat.size bodyStart <= bound
  bodyFinish : Nat.size bodyFinish <= bound
  prefixInputStart : Nat.size prefixInputStart <= bound
  prefixInputFinish : Nat.size prefixInputFinish <= bound
  valueStart : Nat.size valueStart <= bound
  valueFinish : Nat.size valueFinish <= bound
  failureStart : Nat.size failureStart <= bound
  failureFinish : Nat.size failureFinish <= bound

structure CompactProofRootSequentFailureSharedRowsPackage
    (tokenTable width tokenCount
      rootInputStart rootInputFinish bodyStart bodyFinish
      prefixInputStart prefixInputFinish valueStart valueFinish
      suffixBoundary valueBoundary failureStateBoundary : Nat)
    (rootInput body prefixInput : List Nat)
    (suffixes formulaValues : List (List Nat))
    (parserTraces : List CompactFormulaTokenParserDirectTrace)
    (failureStates : CompactFormulaTokenParserDirectTrace) : Prop where
  rootInputLayout :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount
        rootInputStart rootInputFinish rootInput
  bodyLayout :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount bodyStart bodyFinish body
  prefixInputLayout :
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount
        prefixInputStart prefixInputFinish prefixInput
  suffixRows :
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        suffixBoundary suffixes
  suffixBoundary_size_le :
    Nat.size suffixBoundary <= (suffixes.length + 1) * tokenCount
  valueStructure :
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount valueStart formulaValues.length
        valueFinish valueBoundary
  valueRows :
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        valueBoundary formulaValues
  valueBoundary_size_le :
    Nat.size valueBoundary <=
      (formulaValues.length + 1) * tokenCount
  parserRows :
    ∀ index < parserTraces.length,
      ∃ parserStateBoundary,
        CompactUnifiedParserStateListRowLayouts
            tokenTable width tokenCount parserStateBoundary
              (parserTraces.getI index) ∧
          Nat.size parserStateBoundary <=
            ((parserTraces.getI index).length + 1) * tokenCount
  failureStateRows :
    CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount failureStateBoundary failureStates
  failureStateBoundary_size_le :
    Nat.size failureStateBoundary <=
      (failureStates.length + 1) * tokenCount

private theorem compactAdditiveTokenList_length_le_weight
    (tokens : List Nat) :
    tokens.length <= compactAdditiveTokenWeight tokens := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      simp only [List.length_cons, compactAdditiveTokenWeight_cons]
      omega

theorem exists_compactProofRootSequentFailureSharedRows_with_publicBounds
    (rootInput body prefixInput : List Nat)
    (suffixes formulaValues : List (List Nat))
    (parserTraces : List CompactFormulaTokenParserDirectTrace)
    (failureStates : CompactFormulaTokenParserDirectTrace) :
    let dataWeight :=
      compactProofRootSequentFailureSharedDataWeight
        rootInput body prefixInput suffixes formulaValues
          parserTraces failureStates
    ∃ tokenTable width tokenCount,
    ∃ rootInputStart rootInputFinish bodyStart bodyFinish,
    ∃ prefixInputStart prefixInputFinish valueStart valueFinish,
    ∃ failureStart failureFinish,
    ∃ suffixBoundary valueBoundary failureStateBoundary,
      CompactProofRootSequentFailureSharedRowsPackage
          tokenTable width tokenCount
          rootInputStart rootInputFinish bodyStart bodyFinish
          prefixInputStart prefixInputFinish valueStart valueFinish
          suffixBoundary valueBoundary failureStateBoundary
          rootInput body prefixInput suffixes formulaValues
          parserTraces failureStates ∧
        CompactProofRootSequentFailureSharedTablePublicBounds
          tokenTable width tokenCount
          rootInputStart rootInputFinish bodyStart bodyFinish
          prefixInputStart prefixInputFinish valueStart valueFinish
          failureStart failureFinish
          (compactProofRootSequentFailureSharedCoordinateSizeBound
            dataWeight) := by
  let dataWeight :=
    compactProofRootSequentFailureSharedDataWeight
      rootInput body prefixInput suffixes formulaValues
        parserTraces failureStates
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
  let rootInputStart := 0
  let rootInputFinish := rootInputTokens.length
  let bodyStart := rootInputFinish
  let bodyFinish := bodyStart + bodyTokens.length
  let prefixInputStart := bodyFinish
  let prefixInputFinish := prefixInputStart + prefixInputTokens.length
  let suffixStart := prefixInputFinish
  let suffixFinish := suffixStart + suffixTokens.length
  let valueStart := suffixFinish
  let valueFinish := valueStart + valueTokens.length
  let parserStart := valueFinish
  let parserFinish := parserStart + parserTokens.length
  let failureStart := parserFinish
  let failureFinish := tokens.length
  have htokenWeight :
      compactAdditiveTokenWeight tokens = dataWeight := by
    simp only [tokens, compactAdditiveTokenWeight_append,
      rootInputTokens, bodyTokens, prefixInputTokens,
      suffixTokens, valueTokens, parserTokens, failureStateTokens]
    rfl
  have htokenCount : tokens.length <= dataWeight := by
    rw [← htokenWeight]
    exact compactAdditiveTokenList_length_le_weight tokens
  have hwidth : width <= 2 * dataWeight := by
    change compactAdditiveTokenBitLength tokens <= 2 * dataWeight
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight, htokenWeight]
  have htable :
      Nat.size tokenTable <= dataWeight * (2 * dataWeight) := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (Nat.mul_le_mul htokenCount hwidth)
  have hrootInputRaw := compactAdditiveNatListDirectLayout_canonical
    [] rootInput
      (bodyTokens ++ prefixInputTokens ++ suffixTokens ++
        valueTokens ++ parserTokens ++ failureStateTokens)
  dsimp only at hrootInputRaw
  have hrootInputTokenEq :
      [] ++ compactAdditiveEncode rootInput ++
        (bodyTokens ++ prefixInputTokens ++ suffixTokens ++
          valueTokens ++ parserTokens ++ failureStateTokens) = tokens := by
    simp [rootInputTokens, tokens, List.append_assoc]
  rw [hrootInputTokenEq] at hrootInputRaw
  have hbodyRaw := compactAdditiveNatListDirectLayout_canonical
    rootInputTokens body
      (prefixInputTokens ++ suffixTokens ++ valueTokens ++
        parserTokens ++ failureStateTokens)
  dsimp only at hbodyRaw
  have hbodyTokenEq :
      rootInputTokens ++ compactAdditiveEncode body ++
        (prefixInputTokens ++ suffixTokens ++ valueTokens ++
          parserTokens ++ failureStateTokens) = tokens := by
    simp [bodyTokens, tokens, List.append_assoc]
  rw [hbodyTokenEq] at hbodyRaw
  have hprefixInputRaw := compactAdditiveNatListDirectLayout_canonical
    (rootInputTokens ++ bodyTokens) prefixInput
      (suffixTokens ++ valueTokens ++ parserTokens ++ failureStateTokens)
  dsimp only at hprefixInputRaw
  have hprefixInputTokenEq :
      (rootInputTokens ++ bodyTokens) ++
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
  have hfailureRaw :=
    FoundationCompactNumericListedDirectParserStateListLayout.compactUnifiedParserStateListDirectLayout_canonical
      (rootInputTokens ++ bodyTokens ++ prefixInputTokens ++ suffixTokens ++
        valueTokens ++ parserTokens) failureStates []
  dsimp only at hfailureRaw
  have hfailureTokenEq :
      (rootInputTokens ++ bodyTokens ++ prefixInputTokens ++ suffixTokens ++
        valueTokens ++ parserTokens) ++
          compactAdditiveEncode failureStates ++ [] = tokens := by
    simp [failureStateTokens, tokens, List.append_assoc]
  rw [hfailureTokenEq] at hfailureRaw
  have hrootInputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        rootInputStart rootInputFinish rootInput := by
    simpa only [tokenTable, width, rootInputStart, rootInputFinish,
      rootInputTokens, List.length_nil, Nat.zero_add] using hrootInputRaw
  have hbodyLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length bodyStart bodyFinish body := by
    simpa only [tokenTable, width, bodyStart, bodyFinish,
      rootInputFinish, rootInputTokens, bodyTokens,
      List.length_append] using hbodyRaw
  have hprefixInputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        prefixInputStart prefixInputFinish prefixInput := by
    simpa only [tokenTable, width, prefixInputStart, prefixInputFinish,
      bodyFinish, bodyStart, rootInputFinish,
      rootInputTokens, bodyTokens, prefixInputTokens,
      List.length_append] using hprefixInputRaw
  rcases hsuffixRaw with
    ⟨suffixBoundary, _hsuffixStructure, hsuffixRows,
      hsuffixBoundarySize⟩
  have hsuffixRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        suffixBoundary suffixes := by
    simpa only [tokenTable, width] using hsuffixRows
  have hsuffixBoundarySize' :
      Nat.size suffixBoundary <=
        (suffixes.length + 1) * tokens.length := by
    simpa only using hsuffixBoundarySize
  rcases hvalueRaw with
    ⟨valueBoundary, hvalueStructure, hvalueRows, hvalueBoundarySize⟩
  have hvalueStructure' : CompactAdditiveStructuredListLayout
      tokenTable width tokens.length valueStart formulaValues.length
        valueFinish valueBoundary := by
    simpa only [tokenTable, width, valueStart, valueFinish,
      suffixFinish, suffixStart, prefixInputFinish,
      prefixInputStart, bodyFinish, bodyStart, rootInputFinish,
      rootInputTokens, bodyTokens, prefixInputTokens, suffixTokens,
      valueTokens, List.length_append] using hvalueStructure
  have hvalueRows' : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        valueBoundary formulaValues := by
    simpa only [tokenTable, width] using hvalueRows
  have hvalueBoundarySize' :
      Nat.size valueBoundary <=
        (formulaValues.length + 1) * tokens.length := by
    simpa only using hvalueBoundarySize
  have hparserRowsRaw := hparserRaw.2.1
  have hparserRows' :
      ∀ index < parserTraces.length,
        ∃ parserStateBoundary,
          CompactUnifiedParserStateListRowLayouts
              tokenTable width tokens.length parserStateBoundary
                (parserTraces.getI index) ∧
            Nat.size parserStateBoundary <=
              ((parserTraces.getI index).length + 1) * tokens.length := by
    intro index hindex
    rcases hparserRowsRaw index hindex with
      ⟨_left, _hleftBound, _right, _hrightBound,
        _hleftEntry, _hrightEntry, htraceLayout⟩
    rcases htraceLayout with
      ⟨parserStateBoundary, _htraceStructure,
        hparserStateRows, hparserStateSize⟩
    exact ⟨parserStateBoundary, by
      constructor
      · simpa only [tokenTable, width] using hparserStateRows
      · simpa only using hparserStateSize⟩
  rcases hfailureRaw with
    ⟨hfailureStructure, hfailureRows, hfailureBoundarySize⟩
  let failureStateBoundary :=
    compactUnifiedParserStateBoundaryTable tokens.length
      (failureStart + 1) failureStates
  have hfailureRows' : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokens.length failureStateBoundary
        failureStates := by
    dsimp only [failureStateBoundary, failureStart, parserFinish,
      parserStart, valueFinish, valueStart, suffixFinish, suffixStart,
      prefixInputFinish, prefixInputStart, bodyFinish, bodyStart,
      rootInputFinish]
    simpa only [tokenTable, width, rootInputTokens, bodyTokens,
      prefixInputTokens, suffixTokens, valueTokens, parserTokens,
      List.length_append] using hfailureRows
  have hfailureBoundarySize' :
      Nat.size failureStateBoundary <=
        (failureStates.length + 1) * tokens.length := by
    dsimp only [failureStateBoundary, failureStart, parserFinish,
      parserStart, valueFinish, valueStart, suffixFinish, suffixStart,
      prefixInputFinish, prefixInputStart, bodyFinish, bodyStart,
      rootInputFinish]
    simpa only [rootInputTokens, bodyTokens, prefixInputTokens,
      suffixTokens, valueTokens, parserTokens,
      List.length_append] using hfailureBoundarySize
  let coordinateBound :=
    compactProofRootSequentFailureSharedCoordinateSizeBound dataWeight
  have htablePublic : Nat.size tokenTable <= coordinateBound := by
    exact htable.trans (by
      dsimp only [coordinateBound]
      unfold compactProofRootSequentFailureSharedCoordinateSizeBound
      omega)
  have hwidthSizePublic : Nat.size width <= coordinateBound := by
    exact (natSize_le_of_le hwidth).trans (by
      dsimp only [coordinateBound]
      unfold compactProofRootSequentFailureSharedCoordinateSizeBound
      omega)
  have hwidthValuePublic : width <= coordinateBound := by
    exact hwidth.trans (by
      dsimp only [coordinateBound]
      unfold compactProofRootSequentFailureSharedCoordinateSizeBound
      omega)
  have htokenCountSizePublic :
      Nat.size tokens.length <= coordinateBound := by
    exact (natSize_le_of_le htokenCount).trans (by
      dsimp only [coordinateBound]
      unfold compactProofRootSequentFailureSharedCoordinateSizeBound
      omega)
  have htokenCountValuePublic : tokens.length <= coordinateBound := by
    exact htokenCount.trans (by
      dsimp only [coordinateBound]
      unfold compactProofRootSequentFailureSharedCoordinateSizeBound
      omega)
  have hpositionSize
      {position : Nat} (hposition : position <= tokens.length) :
      Nat.size position <= coordinateBound :=
    (natSize_le_of_le hposition).trans htokenCountValuePublic
  have hrootInputFinish : rootInputFinish <= tokens.length := by
    dsimp only [rootInputFinish, rootInputTokens, tokens]
    simp only [List.length_append]
    omega
  have hbodyFinish : bodyFinish <= tokens.length := by
    dsimp only [bodyFinish, bodyStart, rootInputFinish,
      rootInputTokens, bodyTokens, tokens]
    simp only [List.length_append]
    omega
  have hprefixInputFinish : prefixInputFinish <= tokens.length := by
    dsimp only [prefixInputFinish, prefixInputStart, bodyFinish,
      bodyStart, rootInputFinish, rootInputTokens, bodyTokens,
      prefixInputTokens, tokens]
    simp only [List.length_append]
    omega
  have hvalueStart : valueStart <= tokens.length := by
    dsimp only [valueStart, suffixFinish, suffixStart,
      prefixInputFinish, prefixInputStart, bodyFinish, bodyStart,
      rootInputFinish, rootInputTokens, bodyTokens, prefixInputTokens,
      suffixTokens, tokens]
    simp only [List.length_append]
    omega
  have hvalueFinish : valueFinish <= tokens.length := by
    dsimp only [valueFinish, valueStart, suffixFinish, suffixStart,
      prefixInputFinish, prefixInputStart, bodyFinish, bodyStart,
      rootInputFinish, rootInputTokens, bodyTokens, prefixInputTokens,
      suffixTokens, valueTokens, tokens]
    simp only [List.length_append]
    omega
  have hfailureStart : failureStart <= tokens.length := by
    dsimp only [failureStart, parserFinish, parserStart,
      valueFinish, valueStart, suffixFinish, suffixStart,
      prefixInputFinish, prefixInputStart, bodyFinish, bodyStart,
      rootInputFinish, rootInputTokens, bodyTokens, prefixInputTokens,
      suffixTokens, valueTokens, parserTokens, tokens]
    simp only [List.length_append]
    omega
  have hfailureFinish : failureFinish <= tokens.length := by
    exact Nat.le_refl tokens.length
  refine ⟨tokenTable, width, tokens.length,
    rootInputStart, rootInputFinish, bodyStart, bodyFinish,
    prefixInputStart, prefixInputFinish, valueStart, valueFinish,
    failureStart, failureFinish,
    suffixBoundary, valueBoundary, failureStateBoundary, ?_, ?_⟩
  · exact
      { rootInputLayout := hrootInputLayout
        bodyLayout := hbodyLayout
        prefixInputLayout := hprefixInputLayout
        suffixRows := hsuffixRows'
        suffixBoundary_size_le := hsuffixBoundarySize'
        valueStructure := hvalueStructure'
        valueRows := hvalueRows'
        valueBoundary_size_le := hvalueBoundarySize'
        parserRows := hparserRows'
        failureStateRows := hfailureRows'
        failureStateBoundary_size_le := hfailureBoundarySize' }
  · exact
      { tokenTable := htablePublic
        width_size := hwidthSizePublic
        width_value := hwidthValuePublic
        tokenCount_size := htokenCountSizePublic
        tokenCount_value := htokenCountValuePublic
        rootInputStart := by simp [rootInputStart]
        rootInputFinish := hpositionSize hrootInputFinish
        bodyStart := hpositionSize hrootInputFinish
        bodyFinish := hpositionSize hbodyFinish
        prefixInputStart := hpositionSize hbodyFinish
        prefixInputFinish := hpositionSize hprefixInputFinish
        valueStart := hpositionSize hvalueStart
        valueFinish := hpositionSize hvalueFinish
        failureStart := hpositionSize hfailureStart
        failureFinish := hpositionSize hfailureFinish }

#print axioms
  exists_compactProofRootSequentFailureSharedRows_with_publicBounds

end FoundationCompactNumericListedDirectProofRootSequentFailureSharedRowsPublicBounds
