import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness
import integration.FoundationCompactNumericListedDirectVerifierTaskFieldRealization
import integration.FoundationCompactNumericListedDirectNatListSliceEquality
import integration.FoundationCompactNumericListedRootFieldsDecomposition

/-!
# Exact endpoint for the sequent-only proof-root branches

Tags 2, 7, and 8 parse a count-prefixed sequent and no additional formula or
term.  This module puts the full input, parsed root, sequent body, repeated
formula traces, and final suffix in one token table.  The graph is both sound
for the public root parser and constructible from every successful public run
in these three branches.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootSequentOnlyEndpoint

open FoundationCompactAdditiveTokenCodec
open FoundationCompactProofTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListSliceEquality
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness
open FoundationCompactNumericListedDirectSequentFormulaCanonicalLayouts
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

structure CompactProofRootSequentOnlyEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  root : CompactNumericVerifierTaskRowCoordinates
  rootSize : CompactNumericVerifierTaskSizeWitness
  finalStart : Nat
  finalFinish : Nat
  sequent : CompactSequentFormulaEndpointCoordinates

def CompactProofRootSequentOnlyEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootSequentOnlyEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount
        inputFinish coordinates.inputBoundary coordinates.inputBoundarySize ∧
    coordinates.root.start = rootStart ∧
    coordinates.root.finish = rootFinish ∧
    CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates.root coordinates.rootSize ∧
    (coordinates.root.tag = 2 ∨
      coordinates.root.tag = 7 ∨ coordinates.root.tag = 8) ∧
    coordinates.root.firstCount = 0 ∧
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
    CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
        coordinates.finalStart coordinates.finalFinish
        coordinates.root.witnessFinish coordinates.root.finish

def compactProofRootSequentOnlyEndpointGraphDef : 𝚺₀.Semisentence 46 :=
  .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish
      inputBoundary inputCount inputBoundarySize
      taskStart taskFinish taskTag taskGammaFinish taskGammaCount
      taskGammaBoundary taskFirstFinish taskFirstCount
      taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
      taskSuffixCount taskGammaBoundarySize
      finalStart finalFinish
      sequentInputBoundary sequentInputCount sequentInputBoundarySize
      sequentFirstStart sequentFirstFinish sequentFirstBoundary
      sequentFirstCount sequentFirstBoundarySize
      sequentSuffixBoundary sequentSuffixCount
      sequentValueBoundary sequentValueCount sequentValueBoundarySize
      sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
      sequentTraceTableWidth sequentTraceValueBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    taskStart = rootStart ∧
    taskFinish = rootFinish ∧
    !(compactNumericVerifierTaskCoreGraphDef)
      tokenTable width tokenCount
      taskStart taskFinish taskTag taskGammaFinish taskGammaCount
      taskGammaBoundary taskFirstFinish taskFirstCount
      taskSecondFinish taskSecondCount taskWitnessFinish taskWitnessCount
      taskSuffixCount taskGammaBoundarySize ∧
    (taskTag = 2 ∨ taskTag = 7 ∨ taskTag = 8) ∧
    taskFirstCount = 0 ∧
    taskSecondCount = 0 ∧
    taskWitnessCount = 0 ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
      sequentInputBoundary sequentInputCount
      inputBoundary inputCount taskTag ∧
    !(compactSequentFormulaEndpointGraphDef)
      tokenTable width tokenCount bodyStart bodyFinish
      (taskStart + 1) taskGammaFinish finalStart finalFinish
      sequentInputBoundary sequentInputCount sequentInputBoundarySize
      sequentFirstStart sequentFirstFinish sequentFirstBoundary
      sequentFirstCount sequentFirstBoundarySize
      sequentSuffixBoundary sequentSuffixCount
      sequentValueBoundary sequentValueCount sequentValueBoundarySize
      sequentFinalBoundary sequentFinalCount sequentFinalBoundarySize
      sequentTraceTableWidth sequentTraceValueBound ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount finalStart finalFinish
        taskWitnessFinish taskFinish”

def compactProofRootSequentOnlyEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootSequentOnlyEndpointCoordinates) :
    Fin 46 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.root.start, coordinates.root.finish, coordinates.root.tag,
    coordinates.root.gammaFinish, coordinates.root.gammaCount,
    coordinates.root.gammaBoundary, coordinates.root.firstFinish,
    coordinates.root.firstCount, coordinates.root.secondFinish,
    coordinates.root.secondCount, coordinates.root.witnessFinish,
    coordinates.root.witnessCount, coordinates.root.suffixCount,
    coordinates.rootSize.gammaBoundarySize,
    coordinates.finalStart, coordinates.finalFinish,
    coordinates.sequent.inputBoundary, coordinates.sequent.inputCount,
    coordinates.sequent.inputBoundarySize,
    coordinates.sequent.firstStart, coordinates.sequent.firstFinish,
    coordinates.sequent.firstBoundary, coordinates.sequent.firstCount,
    coordinates.sequent.firstBoundarySize,
    coordinates.sequent.suffixBoundary, coordinates.sequent.suffixCount,
    coordinates.sequent.valueBoundary, coordinates.sequent.valueCount,
    coordinates.sequent.valueBoundarySize,
    coordinates.sequent.finalBoundary, coordinates.sequent.finalCount,
    coordinates.sequent.finalBoundarySize,
    coordinates.sequent.traceTableWidth,
    coordinates.sequent.traceValueBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootSequentOnlyEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootSequentOnlyEndpointCoordinates) :
    compactProofRootSequentOnlyEndpointGraphDef.val.Evalb
        (compactProofRootSequentOnlyEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates) ↔
      CompactProofRootSequentOnlyEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  let env := compactProofRootSequentOnlyEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish coordinates
  change compactProofRootSequentOnlyEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 46), #1, #2, #3, #10, #4,
          #9, #11]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htaskEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 46), #1, #2,
          #12, #13, #14, #15, #16, #17, #18, #19, #20, #21,
          #22, #23, #24, #25]) =
        compactNumericVerifierTaskCoreFormulaEnvironment
          tokenTable width tokenCount
          coordinates.root.start coordinates.root.finish
          coordinates.root.tag coordinates.root.gammaFinish
          coordinates.root.gammaCount coordinates.root.gammaBoundary
          coordinates.root.firstFinish coordinates.root.firstCount
          coordinates.root.secondFinish coordinates.root.secondCount
          coordinates.root.witnessFinish coordinates.root.witnessCount
          coordinates.root.suffixCount
          coordinates.rootSize.gammaBoundarySize := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 46), #1, #2,
          #28, #29, #9, #10, #14]) =
        ![tokenTable, width, tokenCount,
          coordinates.sequent.inputBoundary,
          coordinates.sequent.inputCount,
          coordinates.inputBoundary, coordinates.inputCount,
          coordinates.root.tag] := by
    funext index
    fin_cases index <;> rfl
  have hsequentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 46), #1, #2, #7, #8,
          ‘(#12 + 1)’, #15, #26, #27,
          #28, #29, #30, #31, #32, #33, #34, #35,
          #36, #37, #38, #39, #40, #41, #42, #43, #44, #45]) =
        compactSequentFormulaEndpointEnvironment
          tokenTable width tokenCount bodyStart bodyFinish
          (coordinates.root.start + 1) coordinates.root.gammaFinish
          coordinates.finalStart coordinates.finalFinish
          coordinates.sequent := by
    funext index
    fin_cases index <;> simp [env,
      compactProofRootSequentOnlyEndpointEnvironment,
      compactSequentFormulaEndpointEnvironment]
  have hslicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 46), #1, #2,
          #26, #27, #22, #13]) =
        ![tokenTable, width, tokenCount,
          coordinates.finalStart, coordinates.finalFinish,
          coordinates.root.witnessFinish, coordinates.root.finish] := by
    funext index
    fin_cases index <;> rfl
  have hrootStartValue : env 12 = coordinates.root.start := rfl
  have hrootFinishValue : env 13 = coordinates.root.finish := rfl
  have hrootStartParameterValue : env 5 = rootStart := rfl
  have hrootFinishParameterValue : env 6 = rootFinish := rfl
  have hrootTagValue : env 14 = coordinates.root.tag := rfl
  have hfirstCountValue : env 19 = coordinates.root.firstCount := rfl
  have hsecondCountValue : env 21 = coordinates.root.secondCount := rfl
  have hwitnessCountValue : env 23 = coordinates.root.witnessCount := rfl
  have hrootCoordinatesOf :
      compactNumericVerifierTaskRowCoordinatesOf
        coordinates.root.start coordinates.root.finish coordinates.root.tag
        coordinates.root.gammaFinish coordinates.root.gammaCount
        coordinates.root.gammaBoundary coordinates.root.firstFinish
        coordinates.root.firstCount coordinates.root.secondFinish
        coordinates.root.secondCount coordinates.root.witnessFinish
        coordinates.root.witnessCount coordinates.root.suffixCount =
          coordinates.root := by
    cases coordinates.root
    rfl
  have hrootSizeOf :
      (CompactNumericVerifierTaskSizeWitness.mk
        coordinates.rootSize.gammaBoundarySize) = coordinates.rootSize := by
    cases coordinates.rootSize
    rfl
  simp [compactProofRootSequentOnlyEndpointGraphDef,
    CompactProofRootSequentOnlyEndpointGraph, hinputEnv, htaskEnv,
    hconsEnv, hsequentEnv, hslicesEnv, hrootStartValue,
    hrootFinishValue, hrootStartParameterValue,
    hrootFinishParameterValue, hrootTagValue, hfirstCountValue,
    hsecondCountValue, hwitnessCountValue, hrootCoordinatesOf,
    hrootSizeOf]
  tauto

theorem compactProofRootSequentOnlyEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootSequentOnlyEndpointGraphDef.val := by
  simp [compactProofRootSequentOnlyEndpointGraphDef]

/-- A sequent-only endpoint graph reconstructs the exact public proof-root
parser result, not merely a compatible collection of fields. -/
theorem CompactProofRootSequentOnlyEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootSequentOnlyEndpointCoordinates}
    (hgraph : CompactProofRootSequentOnlyEndpointGraph
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
      hfirstZero, hsecondZero, hwitnessZero, hcons, hsequent,
      hfinalSlices⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨root, hrootLayout, hrootTag, hgammaRows, hgammaCount,
      hfirstLayout, hfirstCount, hsecondLayout, hsecondCount,
      hwitnessLayout, hwitnessCount, hsuffixLayout, _hsuffixCount⟩
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
  have hsuffixEq : root.2.2.2.2.2 = finalSuffix :=
    CompactFixedWidthTokenSlicesEq.natListValues_eq
      hfinalSlices hfinalLayout hsuffixLayout
  have hfirstEmpty : root.2.2.1 = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [hfirstCount, hfirstZero]
  have hsecondEmpty : root.2.2.2.1 = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [hsecondCount, hsecondZero]
  have hwitnessEmpty : root.2.2.2.2.1 = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [hwitnessCount, hwitnessZero]
  have hfieldsEq : root.2 =
      (root.2.1, (([] : List Nat),
        (([] : List Nat), (([] : List Nat), finalSuffix)))) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact hfirstEmpty
      · apply Prod.ext
        · exact hsecondEmpty
        · apply Prod.ext
          · exact hwitnessEmpty
          · exact hsuffixEq
  have hfields : compactNodeSequentOnlyFields bodyRowsValue =
      some root.2 := by
    simp only [compactNodeSequentOnlyFields, hsequentParser, Option.map_some,
      Option.some.injEq]
    rw [hvaluesEq]
    exact hfieldsEq.symm
  have hrootParser : compactListedProofNodeFieldsParser input = some root := by
    apply (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).2
    rw [hinputEq]
    rcases htag with htag2 | htag78
    · have hrootTag2 : root.1 = 2 := hrootTag.trans htag2
      simpa [CompactNumericProofRootBranchValid, htag2] using
        (And.intro hrootTag2 hfields)
    · rcases htag78 with htag7 | htag8
      · have hrootTag7 : root.1 = 7 := hrootTag.trans htag7
        simpa [CompactNumericProofRootBranchValid, htag7] using
          (And.intro hrootTag7 hfields)
      · have hrootTag8 : root.1 = 8 := hrootTag.trans htag8
        simpa [CompactNumericProofRootBranchValid, htag8] using
          (And.intro hrootTag8 hfields)
  exact ⟨input, root, hinputLayout, hrootLayout, hrootParser⟩

/-- Canonical shared rows for the full input, parsed root, sequent body,
intermediate suffixes, and every formula-parser state trace. -/
theorem exists_compactProofRootSequentOnlyCanonicalRows
    (input : List Nat) (root : CompactNumericProofRoot) (body : List Nat)
    (suffixes : List (List Nat))
    (parserTraces : List FoundationCompactParserDirectTrace.CompactFormulaTokenParserDirectTrace) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish suffixBoundary,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount rootStart rootFinish root ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount bodyStart bodyFinish body ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          suffixBoundary suffixes ∧
      (∀ index < parserTraces.length,
        ∃ parserStateBoundary,
          FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
            tokenTable width tokenCount parserStateBoundary
              (parserTraces.getI index)) := by
  let inputTokens := compactAdditiveEncode input
  let rootTokens := compactAdditiveEncode root
  let bodyTokens := compactAdditiveEncode body
  let suffixTokens := compactAdditiveEncode suffixes
  let parserTokens := compactAdditiveEncode parserTraces
  let tokens := inputTokens ++ rootTokens ++ bodyTokens ++
    suffixTokens ++ parserTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (rootTokens ++ bodyTokens ++ suffixTokens ++ parserTokens)
  dsimp only at hinputRaw
  have hinputTokens : [] ++ compactAdditiveEncode input ++
      (rootTokens ++ bodyTokens ++ suffixTokens ++ parserTokens) = tokens := by
    simp [inputTokens, tokens, List.append_assoc]
  rw [hinputTokens] at hinputRaw
  have hrootRaw := compactNumericVerifierTaskDirectLayout_canonical
    inputTokens root (bodyTokens ++ suffixTokens ++ parserTokens)
  dsimp only at hrootRaw
  have hrootTokens : inputTokens ++ compactAdditiveEncode root ++
      (bodyTokens ++ suffixTokens ++ parserTokens) = tokens := by
    simp [rootTokens, tokens, List.append_assoc]
  rw [hrootTokens] at hrootRaw
  have hbodyRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ rootTokens) body (suffixTokens ++ parserTokens)
  dsimp only at hbodyRaw
  have hbodyTokens : (inputTokens ++ rootTokens) ++
      compactAdditiveEncode body ++ (suffixTokens ++ parserTokens) = tokens := by
    simp [bodyTokens, tokens, List.append_assoc]
  rw [hbodyTokens] at hbodyRaw
  have hsuffixRaw := compactAdditiveNatListListDirectLayout_canonical
    (inputTokens ++ rootTokens ++ bodyTokens) suffixes parserTokens
  dsimp only at hsuffixRaw
  have hsuffixTokens : (inputTokens ++ rootTokens ++ bodyTokens) ++
      compactAdditiveEncode suffixes ++ parserTokens = tokens := by
    simp [suffixTokens, tokens, List.append_assoc]
  rw [hsuffixTokens] at hsuffixRaw
  rcases hsuffixRaw with
    ⟨suffixBoundary, _hsuffixStructure, hsuffixRows, _hsuffixSize⟩
  have hparserRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactUnifiedParserStateListDirectLayout
    compactUnifiedParserStateListDirectLayout_canonical
    (inputTokens ++ rootTokens ++ bodyTokens ++ suffixTokens)
      parserTraces []
  dsimp only at hparserRaw
  have hparserTokens :
      (inputTokens ++ rootTokens ++ bodyTokens ++ suffixTokens) ++
          compactAdditiveEncode parserTraces ++ [] = tokens := by
    simp [parserTokens, tokens, List.append_assoc]
  rw [hparserTokens] at hparserRaw
  have hparserRows := hparserRaw.2.1
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length, inputTokens.length + rootTokens.length,
    inputTokens.length + rootTokens.length,
    inputTokens.length + rootTokens.length + bodyTokens.length,
    suffixBoundary, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tokenTable, width, inputTokens,
      List.length_nil, Nat.zero_add] using hinputRaw
  · simpa only [tokenTable, width, List.length_append] using hrootRaw
  · simpa only [tokenTable, width, List.length_append] using hbodyRaw
  · simpa only [tokenTable, width] using hsuffixRows
  · intro index hindex
    rcases hparserRows index hindex with
      ⟨left, _hleftBound, right, _hrightBound,
        _hleftEntry, _hrightEntry, htraceLayout⟩
    rcases htraceLayout with
      ⟨parserStateBoundary, _htraceStructure,
        hparserStateRows, _hparserStateSize⟩
    exact ⟨parserStateBoundary, by
      simpa only [tokenTable, width] using hparserStateRows⟩

/-- Every real successful sequent-only branch constructs the complete shared
endpoint graph. -/
theorem exists_compactProofRootSequentOnlyEndpointGraph_of_results_with_inputLayout
    (tag : Nat) (body : List Nat) (values : List (List Nat))
    (suffix : List Nat)
    (htag : tag = 2 ∨ tag = 7 ∨ tag = 8)
    (hsequent : compactSequentTokenValueParser body = some (values, suffix)) :
    let input := tag :: body
    let root : CompactNumericProofRoot :=
      (tag, (values, ([], ([], ([], suffix)))))
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootSequentOnlyEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSequentOnlyEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  let input := tag :: body
  let root : CompactNumericProofRoot :=
    (tag, (values, ([], ([], ([], suffix)))))
  rcases compactSequentTokenValueParser_sound hsequent with
    ⟨Gamma, hbody, hvalues⟩
  subst body
  subst values
  rcases exists_compactSequentFormulaCanonicalDirectData Gamma suffix with
    ⟨suffixes, parserTraces, hsuffixCount, hparserCount,
      hfirst, hfinal, hsteps⟩
  rcases exists_compactProofRootSequentOnlyCanonicalRows
      input root (compactSequentListTokens Gamma ++ suffix)
        suffixes parserTraces with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, suffixBoundary,
      hinputLayout, hrootLayout, hbodyLayout, hsuffixRows, hparserRows⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFormula.CompactNumericVerifierTaskDirectLayout.toCoreGraph
        hrootLayout with
    ⟨rootCoordinates, rootSize, hrootStart, hrootFinish,
      hrootTag, hrootCore⟩
  rcases
      FoundationCompactNumericListedDirectVerifierTaskFieldRealization.CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaCount, _hfirstLayout, hfirstCount,
      _hsecondLayout, hsecondCount, _hwitnessLayout, hwitnessCount,
      hsuffixLayout, _hsuffixCount⟩
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
  have hparserRows' : ∀ index <
      (Gamma.map compactArithmeticFormulaTokens).length,
      ∃ parserStateBoundary,
        FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
          tokenTable width tokenCount parserStateBoundary
            (parserTraces.getI index) := by
    intro index hindex
    apply hparserRows index
    rw [hparserCount]
    simpa using hindex
  have hsteps' : ∀ index <
      (Gamma.map compactArithmeticFormulaTokens).length,
      FoundationCompactParserDirectTrace.CompactFormulaTokenParserDirectTraceValid
          0 (suffixes.getI index) (suffixes.getI (index + 1))
            (parserTraces.getI index) ∧
        suffixes.getI index =
          (Gamma.map compactArithmeticFormulaTokens).getI index ++
            suffixes.getI (index + 1) := by
    intro index hindex
    apply hsteps index
    simpa using hindex
  have hsuffixCount' : suffixes.length =
      (Gamma.map compactArithmeticFormulaTokens).length + 1 := by
    simpa using hsuffixCount
  have hparserCount' : parserTraces.length =
      (Gamma.map compactArithmeticFormulaTokens).length := by
    simpa using hparserCount
  have hbodyFirst : compactSequentListTokens Gamma ++ suffix =
      (Gamma.map compactArithmeticFormulaTokens).length ::
        suffixes.getI 0 := by
    rw [hfirst]
    simp [compactSequentListTokens]
  have hfinal' : suffixes.getI root.2.1.length = suffix := by
    simpa [root] using hfinal
  rcases exists_compactSequentFormulaEndpointGraph_of_rows
      hbodyLayout hsuffixRows hgammaStructure hgammaRows hgammaSize
      hparserRows' hsuffixCount' hparserCount' hsteps'
      hbodyFirst hfinal' with
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
      compactSequentListTokens Gamma ++ suffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hbodyLayout hwitnessBodyLayout).1
  subst witnessBody
  have hcons : CompactAdditiveNatListConsRows
      tokenTable width tokenCount sequentCoordinates.inputBoundary
        sequentCoordinates.inputCount inputBoundary input.length tag := by
    have hraw :=
      CompactAdditiveStructuredListElementRowLayouts.natConsRows
        hwitnessBodyRows hwitnessInputRows (show input = tag ::
          (compactSequentListTokens Gamma ++ suffix) by rfl)
    simpa only [hwitnessBodyCount, hwitnessInputCount] using hraw
  rcases hsequentGraph.sound with
    ⟨endpointBody, endpointValues, endpointSuffix,
      hendpointBodyLayout, _hendpointValuesLayout,
      hendpointSuffixLayout, hendpointParser⟩
  have hendpointBodyEq : endpointBody =
      compactSequentListTokens Gamma ++ suffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hbodyLayout hendpointBodyLayout).1
  subst endpointBody
  have hendpointResult :
      (endpointValues, endpointSuffix) =
        (Gamma.map compactArithmeticFormulaTokens, suffix) := by
    exact Option.some.inj (hendpointParser.symm.trans
      (by simpa using hsequent))
  have hendpointSuffix : endpointSuffix = suffix :=
    congrArg Prod.snd hendpointResult
  have hfinalSlices : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount finalStart finalFinish
        rootCoordinates.witnessFinish rootCoordinates.finish := by
    apply CompactAdditiveNatListDirectLayout.slicesEq_of_eq
      hendpointSuffixLayout hsuffixLayout
    simpa [root, hendpointSuffix]
  have hfirstZero : rootCoordinates.firstCount = 0 := by
    simpa [root] using hfirstCount.symm
  have hsecondZero : rootCoordinates.secondCount = 0 := by
    simpa [root] using hsecondCount.symm
  have hwitnessZero : rootCoordinates.witnessCount = 0 := by
    simpa [root] using hwitnessCount.symm
  have hcoordinateTag : rootCoordinates.tag = tag := by
    simpa [root] using hrootTag
  have hcoordinateTagCases : rootCoordinates.tag = 2 ∨
      rootCoordinates.tag = 7 ∨ rootCoordinates.tag = 8 := by
    rw [hcoordinateTag]
    exact htag
  have hconsCoordinateTag : CompactAdditiveNatListConsRows
      tokenTable width tokenCount sequentCoordinates.inputBoundary
        sequentCoordinates.inputCount inputBoundary input.length
        rootCoordinates.tag := by
    simpa only [hcoordinateTag] using hcons
  let coordinates : CompactProofRootSequentOnlyEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := inputBoundarySize
      root := rootCoordinates
      rootSize := rootSize
      finalStart := finalStart
      finalFinish := finalFinish
      sequent := sequentCoordinates }
  refine ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
    hinputLayout, ?_⟩
  unfold CompactProofRootSequentOnlyEndpointGraph
  dsimp only [coordinates]
  exact ⟨hinputWitness, hrootStart, hrootFinish, hrootCore,
    hcoordinateTagCases, hfirstZero, hsecondZero, hwitnessZero,
    hconsCoordinateTag, hsequentGraph, hfinalSlices⟩

theorem exists_compactProofRootSequentOnlyEndpointGraph_of_results
    (tag : Nat) (body : List Nat) (values : List (List Nat))
    (suffix : List Nat)
    (htag : tag = 2 ∨ tag = 7 ∨ tag = 8)
    (hsequent : compactSequentTokenValueParser body = some (values, suffix)) :
    let input := tag :: body
    let root : CompactNumericProofRoot :=
      (tag, (values, ([], ([], ([], suffix)))))
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootSequentOnlyEndpointCoordinates,
      CompactProofRootSequentOnlyEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootSequentOnlyEndpointGraph_of_results_with_inputLayout
        tag body values suffix htag hsequent with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates, hgraph⟩

/-- Public root-parser success in one of tags 2, 7, or 8 has a complete
bounded-coordinate endpoint witness. -/
theorem exists_compactProofRootSequentOnlyEndpointGraph_of_success_with_inputLayout
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 2 ∨ root.1 = 7 ∨ root.1 = 8) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootSequentOnlyEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSequentOnlyEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish coordinates := by
  rw [compactListedProofNodeFieldsParser_eq_some_iff_branchValid] at hparser
  cases input with
  | nil => simp [CompactNumericProofRootBranchValid] at hparser
  | cons inputTag body =>
      rcases htag with htag2 | htag78
      · have hinputTag : inputTag = 2 := by
          by_contra hne
          simp [CompactNumericProofRootBranchValid, hne, htag2] at hparser
        subst inputTag
        have hfields : compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, htag2] using hparser
        cases hsequent : compactSequentTokenValueParser body with
        | none => simp [compactNodeSequentOnlyFields, hsequent] at hfields
        | some parsed =>
            rcases parsed with ⟨values, suffix⟩
            have hroot : root =
                (2, (values, ([], ([], ([], suffix))))) := by
              simp [compactNodeSequentOnlyFields, hsequent] at hfields
              exact Prod.ext htag2 (by simpa using hfields.symm)
            subst root
            simpa using
              exists_compactProofRootSequentOnlyEndpointGraph_of_results_with_inputLayout
                2 body values suffix (Or.inl rfl) hsequent
      · rcases htag78 with htag7 | htag8
        · have hinputTag : inputTag = 7 := by
            by_contra hne
            simp [CompactNumericProofRootBranchValid, hne, htag7] at hparser
          subst inputTag
          have hfields : compactNodeSequentOnlyFields body = some root.2 := by
            simpa [CompactNumericProofRootBranchValid, htag7] using hparser
          cases hsequent : compactSequentTokenValueParser body with
          | none => simp [compactNodeSequentOnlyFields, hsequent] at hfields
          | some parsed =>
              rcases parsed with ⟨values, suffix⟩
              have hroot : root =
                  (7, (values, ([], ([], ([], suffix))))) := by
                simp [compactNodeSequentOnlyFields, hsequent] at hfields
                exact Prod.ext htag7 (by simpa using hfields.symm)
              subst root
              simpa using
                exists_compactProofRootSequentOnlyEndpointGraph_of_results_with_inputLayout
                  7 body values suffix (Or.inr (Or.inl rfl)) hsequent
        · have hinputTag : inputTag = 8 := by
            by_contra hne
            simp [CompactNumericProofRootBranchValid, hne, htag8] at hparser
          subst inputTag
          have hfields : compactNodeSequentOnlyFields body = some root.2 := by
            simpa [CompactNumericProofRootBranchValid, htag8] using hparser
          cases hsequent : compactSequentTokenValueParser body with
          | none => simp [compactNodeSequentOnlyFields, hsequent] at hfields
          | some parsed =>
              rcases parsed with ⟨values, suffix⟩
              have hroot : root =
                  (8, (values, ([], ([], ([], suffix))))) := by
                simp [compactNodeSequentOnlyFields, hsequent] at hfields
                exact Prod.ext htag8 (by simpa using hfields.symm)
              subst root
              simpa using
                exists_compactProofRootSequentOnlyEndpointGraph_of_results_with_inputLayout
                  8 body values suffix (Or.inr (Or.inr rfl)) hsequent

theorem exists_compactProofRootSequentOnlyEndpointGraph_of_success
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 2 ∨ root.1 = 7 ∨ root.1 = 8) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootSequentOnlyEndpointCoordinates,
      CompactProofRootSequentOnlyEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootSequentOnlyEndpointGraph_of_success_with_inputLayout
        hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, coordinates,
      _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, bodyStart, bodyFinish, coordinates, hgraph⟩

#print axioms CompactProofRootSequentOnlyEndpointGraph.sound
#print axioms compactProofRootSequentOnlyEndpointGraphDef_spec
#print axioms compactProofRootSequentOnlyEndpointGraphDef_sigmaZero
#print axioms exists_compactProofRootSequentOnlyCanonicalRows
#print axioms exists_compactProofRootSequentOnlyEndpointGraph_of_results
#print axioms exists_compactProofRootSequentOnlyEndpointGraph_of_success

end FoundationCompactNumericListedDirectProofRootSequentOnlyEndpoint
