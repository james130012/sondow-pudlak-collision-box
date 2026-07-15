import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
import integration.FoundationCompactSyntaxTokenMachineInversion

/-!
# Exact endpoint for the induction PA-axiom certificate tag

PA certificate tag 22 is followed by one formula at binder arity one.  This
graph places the complete structural-certificate input, its PA tail, the
consumed axiom tokens, the formula-parser input and suffix, and the complete
ordinary parser trace in one fixed-width table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactSyntaxTokenMachineInversion
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

structure CompactCertificateNodeInductionPAEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  tailStart : Nat
  tailFinish : Nat
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  axiomBoundary : Nat
  axiomCount : Nat
  axiomBoundarySize : Nat
  parser : CompactParserSyntaxExactEndpointCoordinates

def CompactCertificateNodeInductionPAEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount coordinates.tailStart coordinates.tailCount
        coordinates.tailFinish coordinates.tailBoundary
        coordinates.tailBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount axiomStart coordinates.axiomCount axiomFinish
        coordinates.axiomBoundary coordinates.axiomBoundarySize ∧
    certificateTag = 1 ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.tailBoundary coordinates.tailCount
        coordinates.inputBoundary coordinates.inputCount 1 ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.parser.inputBoundary coordinates.parser.inputCount
        coordinates.tailBoundary coordinates.tailCount 22 ∧
    CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount formulaStart formulaFinish
        suffixStart suffixFinish 1 1 0 coordinates.parser ∧
    CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        axiomStart axiomFinish coordinates.axiomCount
        suffixStart suffixFinish coordinates.parser.expectedCount
        coordinates.tailStart coordinates.tailFinish coordinates.tailCount

def compactCertificateNodeInductionPAEndpointGraphDef :
    𝚺₀.Semisentence 33 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      axiomBoundary axiomCount axiomBoundarySize
      formulaBoundary formulaCount formulaBoundarySize
      suffixBoundary suffixCount suffixBoundarySize
      stateBoundary stateCount tableWidth valueBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount tailStart tailCount tailFinish
        tailBoundary tailBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount axiomStart axiomCount axiomFinish
        axiomBoundary axiomBoundarySize ∧
    certificateTag = 1 ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount inputBoundary inputCount 1 ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        formulaBoundary formulaCount tailBoundary tailCount 22 ∧
    !(compactParserSyntaxExactEndpointGraphDef)
      tokenTable width tokenCount formulaStart formulaFinish
        suffixStart suffixFinish 1 1 0
        formulaBoundary formulaCount formulaBoundarySize
        suffixBoundary suffixCount suffixBoundarySize
        stateBoundary stateCount tableWidth valueBound ∧
    !(compactAdditiveNatListAppendSlicesDef)
      tokenTable width tokenCount
        axiomStart axiomFinish axiomCount
        suffixStart suffixFinish suffixCount
        tailStart tailFinish tailCount”

def compactCertificateNodeInductionPAEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates) :
    Fin 33 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.tailStart, coordinates.tailFinish,
    coordinates.tailBoundary, coordinates.tailCount,
    coordinates.tailBoundarySize,
    coordinates.axiomBoundary, coordinates.axiomCount,
    coordinates.axiomBoundarySize,
    coordinates.parser.inputBoundary, coordinates.parser.inputCount,
    coordinates.parser.inputBoundarySize,
    coordinates.parser.expectedBoundary, coordinates.parser.expectedCount,
    coordinates.parser.expectedBoundarySize,
    coordinates.parser.stateBoundary, coordinates.parser.stateCount,
    coordinates.parser.tableWidth, coordinates.parser.valueBound]

set_option maxHeartbeats 1200000 in
-- Normalizing the embedded twenty-column parser endpoint exceeds the default budget.
set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeInductionPAEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates) :
    compactCertificateNodeInductionPAEndpointGraphDef.val.Evalb
        (compactCertificateNodeInductionPAEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag coordinates) ↔
      CompactCertificateNodeInductionPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag coordinates := by
  let env := compactCertificateNodeInductionPAEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag coordinates
  change compactCertificateNodeInductionPAEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #3, #13, #4,
          #12, #14]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #15, #18, #16,
          #17, #19]) =
        ![tokenTable, width, tokenCount, coordinates.tailStart,
          coordinates.tailCount, coordinates.tailFinish,
          coordinates.tailBoundary, coordinates.tailBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have haxiomEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #5, #21, #6,
          #20, #22]) =
        ![tokenTable, width, tokenCount, axiomStart,
          coordinates.axiomCount, axiomFinish,
          coordinates.axiomBoundary, coordinates.axiomBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have houterConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #17, #18,
          #12, #13, ‘1’]) =
        ![tokenTable, width, tokenCount,
          coordinates.tailBoundary, coordinates.tailCount,
          coordinates.inputBoundary, coordinates.inputCount, 1] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeInductionPAEndpointEnvironment]
  have hinnerConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #23, #24,
          #17, #18, ‘22’]) =
        ![tokenTable, width, tokenCount,
          coordinates.parser.inputBoundary, coordinates.parser.inputCount,
          coordinates.tailBoundary, coordinates.tailCount, 22] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeInductionPAEndpointEnvironment]
  have hparserEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2, #7, #8, #9, #10,
          ‘1’, ‘1’, ‘0’, #23, #24, #25, #26, #27, #28,
          #29, #30, #31, #32]) =
        compactParserSyntaxExactEndpointEnvironment
          tokenTable width tokenCount formulaStart formulaFinish
            suffixStart suffixFinish 1 1 0 coordinates.parser := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeInductionPAEndpointEnvironment,
      compactParserSyntaxExactEndpointEnvironment]
  have happendEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 33), #1, #2,
          #5, #6, #21, #9, #10, #27, #15, #16, #18]) =
        ![tokenTable, width, tokenCount,
          axiomStart, axiomFinish, coordinates.axiomCount,
          suffixStart, suffixFinish, coordinates.parser.expectedCount,
          coordinates.tailStart, coordinates.tailFinish,
          coordinates.tailCount] := by
    funext index
    fin_cases index <;> rfl
  have hcertificateTagValue : env 11 = certificateTag := rfl
  simp [compactCertificateNodeInductionPAEndpointGraphDef,
    CompactCertificateNodeInductionPAEndpointGraph,
    hinputEnv, htailEnv, haxiomEnv, houterConsEnv, hinnerConsEnv,
    hparserEnv, happendEnv, hcertificateTagValue]

theorem compactCertificateNodeInductionPAEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeInductionPAEndpointGraphDef.val := by
  simp [compactCertificateNodeInductionPAEndpointGraphDef]

theorem CompactCertificateNodeInductionPAEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeInductionPAEndpointCoordinates}
    (hgraph : CompactCertificateNodeInductionPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag coordinates) :
    ∃ input axiomTokens suffix : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount axiomStart axiomFinish axiomTokens ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      compactStructuralCertificateNodeParser input =
        some (certificateTag, (axiomTokens, suffix)) := by
  rcases hgraph with
    ⟨hinputRows, htailRows, haxiomRows, hcertificateTag,
      houterCons, hinnerCons, hformula, happend⟩
  rcases hinputRows.realize with
    ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
  rcases htailRows.realize with
    ⟨tail, htailCount, htailLayout, htailElementRows⟩
  rcases haxiomRows.realize with
    ⟨axiomTokens, haxiomCount, haxiomLayout, _haxiomElementRows⟩
  rcases hformula.sound_formula with
    ⟨formulaInput, suffix, hformulaInputLayout,
      hsuffixLayout, hformulaParser⟩
  rcases hformula.1.realize with
    ⟨formulaRowsInput, hformulaRowsInputCount,
      hformulaRowsInputLayout, hformulaInputRows⟩
  have hformulaRowsInputEq : formulaRowsInput = formulaInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaRowsInputLayout hformulaInputLayout).1.symm
  subst formulaRowsInput
  rcases hformula.2.1.realize with
    ⟨suffixRows, hsuffixRowsCount, hsuffixRowsLayout, _hsuffixRows⟩
  have hsuffixRowsEq : suffixRows = suffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hsuffixRowsLayout hsuffixLayout).1.symm
  subst suffixRows
  have houterCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.tailBoundary tail.length
        coordinates.inputBoundary input.length 1 := by
    simpa only [hinputCount, htailCount] using houterCons
  have hinput : input = 1 :: tail :=
    houterCons'.eq_cons_of_rows htailElementRows hinputElementRows
  have hinnerCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.parser.inputBoundary formulaInput.length
        coordinates.tailBoundary tail.length 22 := by
    simpa only [hformulaRowsInputCount, htailCount] using hinnerCons
  have htailCons : tail = 22 :: formulaInput :=
    hinnerCons'.eq_cons_of_rows hformulaInputRows htailElementRows
  have happend' : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        axiomStart axiomFinish axiomTokens.length
        suffixStart suffixFinish suffix.length
        coordinates.tailStart coordinates.tailFinish tail.length := by
    simpa only [haxiomCount, hsuffixRowsCount, htailCount] using happend
  have htailSplit : tail = axiomTokens ++ suffix :=
    (compactAdditiveNatListAppendSlices_iff_append
      haxiomLayout hsuffixLayout htailLayout).mp happend'
  have hpaParser : compactPAAxiomCertificateTokenParser tail = some suffix := by
    rw [htailCons]
    simp [compactPAAxiomCertificateTokenParser, hformulaParser]
  refine ⟨input, axiomTokens, suffix,
    hinputLayout, haxiomLayout, hsuffixLayout, ?_⟩
  subst certificateTag
  rw [hinput]
  simp only [compactStructuralCertificateNodeParser, ↓reduceIte, hpaParser,
    Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
  simpa [htailSplit] using consumedTokenPrefix_append axiomTokens suffix

/-- Every successful tag-22 PA parser call constructs the complete shared-table
endpoint graph. -/
theorem exists_compactCertificateNodeInductionPAEndpointGraph_of_results_with_inputLayout
    (formulaInput suffix : List Nat)
    (hformula : compactFormulaTokenParser 1 formulaInput = some suffix) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish,
    ∃ coordinates : CompactCertificateNodeInductionPAEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: 22 :: formulaInput) ∧
        CompactCertificateNodeInductionPAEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish 1 coordinates := by
  rcases (compactFormulaTokenParser_success_iff
      1 formulaInput suffix).mp hformula with
    ⟨formula, hformulaSplit⟩
  rcases (compactFormulaTokenParser_eq_some_iff_exists_directTrace
      1 formulaInput suffix).mp hformula with
    ⟨states, hformulaValid⟩
  let formulaTokens := compactArithmeticFormulaTokens formula
  let axiomTokens := 22 :: formulaTokens
  let tail := 22 :: formulaInput
  let input := 1 :: tail
  have htailSplit : tail = axiomTokens ++ suffix := by
    simp [tail, axiomTokens, formulaTokens, hformulaSplit]
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let axiomEncoded := compactAdditiveEncode axiomTokens
  let formulaEncoded := compactAdditiveEncode formulaInput
  let suffixEncoded := compactAdditiveEncode suffix
  let stateTokens := compactAdditiveEncode states
  let tokens := inputTokens ++ tailTokens ++ axiomEncoded ++
    formulaEncoded ++ suffixEncoded ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (tailTokens ++ axiomEncoded ++ formulaEncoded ++
      suffixEncoded ++ stateTokens)
  dsimp only at hinputRaw
  have hinputTokenEq : [] ++ compactAdditiveEncode input ++
      (tailTokens ++ axiomEncoded ++ formulaEncoded ++
        suffixEncoded ++ stateTokens) = tokens := by
    simp [inputTokens, tokens, List.append_assoc]
  rw [hinputTokenEq] at hinputRaw
  have htailRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens tail (axiomEncoded ++ formulaEncoded ++
      suffixEncoded ++ stateTokens)
  dsimp only at htailRaw
  have htailTokenEq : inputTokens ++ compactAdditiveEncode tail ++
      (axiomEncoded ++ formulaEncoded ++ suffixEncoded ++ stateTokens) =
        tokens := by
    simp [tailTokens, tokens, List.append_assoc]
  rw [htailTokenEq] at htailRaw
  have haxiomRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens) axiomTokens
      (formulaEncoded ++ suffixEncoded ++ stateTokens)
  dsimp only at haxiomRaw
  have haxiomTokenEq : (inputTokens ++ tailTokens) ++
      compactAdditiveEncode axiomTokens ++
      (formulaEncoded ++ suffixEncoded ++ stateTokens) = tokens := by
    simp [axiomEncoded, tokens, List.append_assoc]
  rw [haxiomTokenEq] at haxiomRaw
  have hformulaRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens ++ axiomEncoded) formulaInput
      (suffixEncoded ++ stateTokens)
  dsimp only at hformulaRaw
  have hformulaTokenEq :
      (inputTokens ++ tailTokens ++ axiomEncoded) ++
        compactAdditiveEncode formulaInput ++ (suffixEncoded ++ stateTokens) =
          tokens := by
    simp [formulaEncoded, tokens, List.append_assoc]
  rw [hformulaTokenEq] at hformulaRaw
  have hsuffixRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens ++ axiomEncoded ++ formulaEncoded)
      suffix stateTokens
  dsimp only at hsuffixRaw
  have hsuffixTokenEq :
      (inputTokens ++ tailTokens ++ axiomEncoded ++ formulaEncoded) ++
        compactAdditiveEncode suffix ++ stateTokens = tokens := by
    simp [suffixEncoded, tokens, List.append_assoc]
  rw [hsuffixTokenEq] at hsuffixRaw
  have hstatesRaw := compactUnifiedParserStateListDirectLayout_canonical
    (inputTokens ++ tailTokens ++ axiomEncoded ++ formulaEncoded ++
      suffixEncoded) states []
  dsimp only at hstatesRaw
  have hstateTokenEq :
      (inputTokens ++ tailTokens ++ axiomEncoded ++ formulaEncoded ++
        suffixEncoded) ++ compactAdditiveEncode states ++ [] = tokens := by
    simp [stateTokens, tokens, List.append_assoc]
  rw [hstateTokenEq] at hstatesRaw
  have hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length 0 inputTokens.length input := by
    simpa only [tokenTable, width, inputTokens,
      List.length_nil, Nat.zero_add] using hinputRaw
  have htailLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length inputTokens.length
        (inputTokens.length + tailTokens.length) tail := by
    simpa only [tokenTable, width, tailTokens,
      List.length_append] using htailRaw
  have haxiomLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens := by
    simpa only [tokenTable, width, axiomEncoded,
      List.length_append] using haxiomRaw
  have hformulaLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length) formulaInput := by
    simpa only [tokenTable, width, formulaEncoded,
      List.length_append] using hformulaRaw
  have hsuffixLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length) suffix := by
    simpa only [tokenTable, width, suffixEncoded,
      List.length_append] using hsuffixRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  rcases htailLayout with
    ⟨tailBoundary, htailStructure, htailElementRows, htailSize⟩
  rcases haxiomLayout with
    ⟨axiomBoundary, haxiomStructure, haxiomElementRows, haxiomSize⟩
  rcases hformulaLayout with
    ⟨formulaBoundary, hformulaStructure, hformulaElementRows, hformulaSize⟩
  rcases hsuffixLayout with
    ⟨suffixBoundary, hsuffixStructure, hsuffixElementRows, hsuffixSize⟩
  rcases hstatesRaw with
    ⟨_hstateStructure, hstateRows, _hstateSize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputSize⟩
  have htailRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length tail.length
        (inputTokens.length + tailTokens.length)
        tailBoundary (Nat.size tailBoundary) :=
    ⟨htailStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        htailElementRows,
      rfl, htailSize⟩
  have haxiomRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length) axiomTokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomBoundary (Nat.size axiomBoundary) :=
    ⟨haxiomStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        haxiomElementRows,
      rfl, haxiomSize⟩
  have houterCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length tailBoundary tail.length
        inputBoundary input.length 1 := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      htailElementRows hinputElementRows
    rfl
  have hinnerCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length formulaBoundary formulaInput.length
        tailBoundary tail.length 22 := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hformulaElementRows htailElementRows
    rfl
  have hlocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound formulaInput)
      (formulaInput, [(1, 1, 0)], none) (some suffix) states := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hformulaValid
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 1, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  let stateBoundary := compactUnifiedParserStateBoundaryTable
    tokens.length
      ((inputTokens ++ tailTokens ++ axiomEncoded ++ formulaEncoded ++
        suffixEncoded).length + 1) states
  have hstateRows' : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokens.length stateBoundary states := by
    simpa only [tokenTable, width, stateBoundary] using hstateRows
  rcases localTrace_exists_compactParserSyntaxExactBoundedFormula
      hstateRows' hformulaElementRows hsuffixElementRows hstartWell hlocal with
    ⟨tableWidth, hformulaBounded⟩
  have hexact : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokens.length stateBoundary states.length
        formulaBoundary formulaInput.length suffixBoundary suffix.length
        1 1 0 tableWidth (2 ^ tableWidth) := by
    apply (compactParserSyntaxExactBoundedGraphDef_spec
      tokenTable width tokens.length stateBoundary states.length
        formulaBoundary formulaInput.length suffixBoundary suffix.length
        1 1 0 tableWidth (2 ^ tableWidth)).mp
    exact hformulaBounded
  have hformulaWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        formulaInput.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length) formulaBoundary (Nat.size formulaBoundary) :=
    ⟨hformulaStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hformulaElementRows,
      rfl, hformulaSize⟩
  have hsuffixWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length) suffix.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length)
        suffixBoundary (Nat.size suffixBoundary) :=
    ⟨hsuffixStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hsuffixElementRows,
      rfl, hsuffixSize⟩
  let parserCoordinates : CompactParserSyntaxExactEndpointCoordinates :=
    { inputBoundary := formulaBoundary
      inputCount := formulaInput.length
      inputBoundarySize := Nat.size formulaBoundary
      expectedBoundary := suffixBoundary
      expectedCount := suffix.length
      expectedBoundarySize := Nat.size suffixBoundary
      stateBoundary := stateBoundary
      stateCount := states.length
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  have hparserGraph : CompactParserSyntaxExactEndpointGraph
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length)
        1 1 0 parserCoordinates := by
    unfold CompactParserSyntaxExactEndpointGraph
    dsimp only [parserCoordinates]
    exact ⟨hformulaWitness, hsuffixWitness, hexact⟩
  have happend : CompactAdditiveNatListAppendSlices
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length) suffix.length
        inputTokens.length (inputTokens.length + tailTokens.length)
        tail.length := by
    apply (compactAdditiveNatListAppendSlices_iff_append
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens from
        ⟨axiomBoundary, haxiomStructure, haxiomElementRows, haxiomSize⟩)
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length) suffix from
        ⟨suffixBoundary, hsuffixStructure, hsuffixElementRows, hsuffixSize⟩)
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        inputTokens.length (inputTokens.length + tailTokens.length) tail from
        ⟨tailBoundary, htailStructure, htailElementRows, htailSize⟩)).2
    exact htailSplit
  let coordinates : CompactCertificateNodeInductionPAEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      tailStart := inputTokens.length
      tailFinish := inputTokens.length + tailTokens.length
      tailBoundary := tailBoundary
      tailCount := tail.length
      tailBoundarySize := Nat.size tailBoundary
      axiomBoundary := axiomBoundary
      axiomCount := axiomTokens.length
      axiomBoundarySize := Nat.size axiomBoundary
      parser := parserCoordinates }
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length + tailTokens.length,
    inputTokens.length + tailTokens.length + axiomEncoded.length,
    inputTokens.length + tailTokens.length + axiomEncoded.length,
    inputTokens.length + tailTokens.length + axiomEncoded.length +
      formulaEncoded.length,
    inputTokens.length + tailTokens.length + axiomEncoded.length +
      formulaEncoded.length,
    inputTokens.length + tailTokens.length + axiomEncoded.length +
      formulaEncoded.length + suffixEncoded.length,
    coordinates, by simpa [input, tail] using hinputLayoutExact, ?_⟩
  unfold CompactCertificateNodeInductionPAEndpointGraph
  dsimp only [coordinates]
  exact ⟨hinputRows, htailRows, haxiomRows, rfl,
    houterCons, hinnerCons, hparserGraph, by
      simpa only [parserCoordinates] using happend⟩

theorem exists_compactCertificateNodeInductionPAEndpointGraph_of_results
    (formulaInput suffix : List Nat)
    (hformula : compactFormulaTokenParser 1 formulaInput = some suffix) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish,
    ∃ coordinates : CompactCertificateNodeInductionPAEndpointCoordinates,
      CompactCertificateNodeInductionPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish 1 coordinates := by
  rcases
      exists_compactCertificateNodeInductionPAEndpointGraph_of_results_with_inputLayout
        formulaInput suffix hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, coordinates, hgraph⟩

#print axioms compactCertificateNodeInductionPAEndpointGraphDef_spec
#print axioms compactCertificateNodeInductionPAEndpointGraphDef_sigmaZero
#print axioms CompactCertificateNodeInductionPAEndpointGraph.sound
#print axioms exists_compactCertificateNodeInductionPAEndpointGraph_of_results_with_inputLayout
#print axioms exists_compactCertificateNodeInductionPAEndpointGraph_of_results

end FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
