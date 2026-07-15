import integration.FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
import integration.FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
import integration.FoundationCompactNumericListedDirectNatListAtRows

/-!
# Exact endpoint for the two symbol PA-axiom certificate tags

PA certificate tags 3 and 4 consume exactly three tokens.  The consumed list
is read at indices 0, 1, and 2 and checked against the direct function- or
relation-symbol validity predicate.  All lists share one fixed-width table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint

open FoundationCompactAdditiveTokenCodec
open FoundationCompactArithmeticSymbolCode
open FoundationCompactCertificateTokenMachine
open FoundationCompactSyntaxTokenMachine
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
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

def CompactSymbolPAAxiomTagValid
    (paTag arity symbolCode : Nat) : Prop :=
  (paTag = 3 ∧ ArithmeticFuncCodeValid arity symbolCode) ∨
    (paTag = 4 ∧ ArithmeticRelCodeValid arity symbolCode)

structure CompactCertificateNodeSymbolPAEndpointCoordinates where
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
  suffixBoundary : Nat
  suffixCount : Nat
  suffixBoundarySize : Nat
  paTag : Nat
  arity : Nat
  symbolCode : Nat

def CompactCertificateNodeSymbolPAEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) : Prop :=
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
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount suffixStart coordinates.suffixCount suffixFinish
        coordinates.suffixBoundary coordinates.suffixBoundarySize ∧
    certificateTag = 1 ∧
    coordinates.axiomCount = 3 ∧
    CompactSymbolPAAxiomTagValid
      coordinates.paTag coordinates.arity coordinates.symbolCode ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.tailBoundary coordinates.tailCount
        coordinates.inputBoundary coordinates.inputCount 1 ∧
    CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        axiomStart axiomFinish coordinates.axiomCount
        suffixStart suffixFinish coordinates.suffixCount
        coordinates.tailStart coordinates.tailFinish coordinates.tailCount ∧
    CompactAdditiveNatListAtRows tokenTable width tokenCount
      coordinates.axiomBoundary coordinates.axiomCount 0 coordinates.paTag ∧
    CompactAdditiveNatListAtRows tokenTable width tokenCount
      coordinates.axiomBoundary coordinates.axiomCount 1 coordinates.arity ∧
    CompactAdditiveNatListAtRows tokenTable width tokenCount
      coordinates.axiomBoundary coordinates.axiomCount 2 coordinates.symbolCode

def compactCertificateNodeSymbolPAEndpointGraphDef : 𝚺₀.Semisentence 27 :=
  .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      axiomBoundary axiomCount axiomBoundarySize
      suffixBoundary suffixCount suffixBoundarySize
      paTag arity symbolCode.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount tailStart tailCount tailFinish
        tailBoundary tailBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount axiomStart axiomCount axiomFinish
        axiomBoundary axiomBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount suffixStart suffixCount suffixFinish
        suffixBoundary suffixBoundarySize ∧
    certificateTag = 1 ∧ axiomCount = 3 ∧
    ((paTag = 3 ∧
        !(compactAdditiveArithmeticFuncCodeValidDef) arity symbolCode) ∨
      (paTag = 4 ∧
        !(compactAdditiveArithmeticRelCodeValidDef) arity symbolCode)) ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount inputBoundary inputCount 1 ∧
    !(compactAdditiveNatListAppendSlicesDef)
      tokenTable width tokenCount
        axiomStart axiomFinish axiomCount
        suffixStart suffixFinish suffixCount
        tailStart tailFinish tailCount ∧
    !(compactAdditiveNatListAtRowsDef)
      tokenTable width tokenCount axiomBoundary axiomCount 0 paTag ∧
    !(compactAdditiveNatListAtRowsDef)
      tokenTable width tokenCount axiomBoundary axiomCount 1 arity ∧
    !(compactAdditiveNatListAtRowsDef)
      tokenTable width tokenCount axiomBoundary axiomCount 2 symbolCode”

def compactCertificateNodeSymbolPAEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    Fin 27 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, suffixStart, suffixFinish, certificateTag,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.tailStart, coordinates.tailFinish,
    coordinates.tailBoundary, coordinates.tailCount,
    coordinates.tailBoundarySize,
    coordinates.axiomBoundary, coordinates.axiomCount,
    coordinates.axiomBoundarySize,
    coordinates.suffixBoundary, coordinates.suffixCount,
    coordinates.suffixBoundarySize,
    coordinates.paTag, coordinates.arity, coordinates.symbolCode]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeSymbolPAEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates) :
    compactCertificateNodeSymbolPAEndpointGraphDef.val.Evalb
        (compactCertificateNodeSymbolPAEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish suffixStart suffixFinish certificateTag
            coordinates) ↔
      CompactCertificateNodeSymbolPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish certificateTag
          coordinates := by
  let env := compactCertificateNodeSymbolPAEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag coordinates
  change compactCertificateNodeSymbolPAEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #3, #11, #4, #10, #12]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #13, #16, #14, #15, #17]) =
        ![tokenTable, width, tokenCount, coordinates.tailStart,
          coordinates.tailCount, coordinates.tailFinish,
          coordinates.tailBoundary, coordinates.tailBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have haxiomEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #5, #19, #6, #18, #20]) =
        ![tokenTable, width, tokenCount, axiomStart,
          coordinates.axiomCount, axiomFinish,
          coordinates.axiomBoundary, coordinates.axiomBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hsuffixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #7, #22, #8, #21, #23]) =
        ![tokenTable, width, tokenCount, suffixStart,
          coordinates.suffixCount, suffixFinish,
          coordinates.suffixBoundary, coordinates.suffixBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hfuncEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#25 : Semiterm ℒₒᵣ Empty 27), #26]) =
        ![coordinates.arity, coordinates.symbolCode] := by
    funext index
    fin_cases index <;> rfl
  have houterConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #15, #16, #10, #11, ‘1’]) =
        ![tokenTable, width, tokenCount,
          coordinates.tailBoundary, coordinates.tailCount,
          coordinates.inputBoundary, coordinates.inputCount, 1] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeSymbolPAEndpointEnvironment]
  have happendEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2,
          #5, #6, #19, #7, #8, #22, #13, #14, #16]) =
        ![tokenTable, width, tokenCount,
          axiomStart, axiomFinish, coordinates.axiomCount,
          suffixStart, suffixFinish, coordinates.suffixCount,
          coordinates.tailStart, coordinates.tailFinish,
          coordinates.tailCount] := by
    funext index
    fin_cases index <;> rfl
  have hatZeroEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #18, #19, ‘0’, #24]) =
        ![tokenTable, width, tokenCount, coordinates.axiomBoundary,
          coordinates.axiomCount, 0, coordinates.paTag] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeSymbolPAEndpointEnvironment]
  have hatOneEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #18, #19, ‘1’, #25]) =
        ![tokenTable, width, tokenCount, coordinates.axiomBoundary,
          coordinates.axiomCount, 1, coordinates.arity] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeSymbolPAEndpointEnvironment]
  have hatTwoEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #18, #19, ‘2’, #26]) =
        ![tokenTable, width, tokenCount, coordinates.axiomBoundary,
          coordinates.axiomCount, 2, coordinates.symbolCode] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeSymbolPAEndpointEnvironment]
  have hcertificateTagValue : env 9 = certificateTag := rfl
  have haxiomCountValue : env 19 = coordinates.axiomCount := rfl
  have hpaTagValue : env 24 = coordinates.paTag := rfl
  have hatZeroSpec :
      (Semiformula.Eval
          ![tokenTable, width, tokenCount, coordinates.axiomBoundary,
            coordinates.axiomCount, 0, coordinates.paTag]
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          coordinates.axiomBoundary coordinates.axiomCount 0
          coordinates.paTag := by
    simpa [compactAdditiveNatListAtRowsEnvironment] using
      (compactAdditiveNatListAtRowsDef_spec tokenTable width tokenCount
        coordinates.axiomBoundary coordinates.axiomCount 0
        coordinates.paTag)
  have hatOneSpec :
      (Semiformula.Eval
          ![tokenTable, width, tokenCount, coordinates.axiomBoundary,
            coordinates.axiomCount, 1, coordinates.arity]
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          coordinates.axiomBoundary coordinates.axiomCount 1
          coordinates.arity := by
    simpa [compactAdditiveNatListAtRowsEnvironment] using
      (compactAdditiveNatListAtRowsDef_spec tokenTable width tokenCount
        coordinates.axiomBoundary coordinates.axiomCount 1
        coordinates.arity)
  have hatTwoSpec :
      (Semiformula.Eval
          ![tokenTable, width, tokenCount, coordinates.axiomBoundary,
            coordinates.axiomCount, 2, coordinates.symbolCode]
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          coordinates.axiomBoundary coordinates.axiomCount 2
          coordinates.symbolCode := by
    simpa [compactAdditiveNatListAtRowsEnvironment] using
      (compactAdditiveNatListAtRowsDef_spec tokenTable width tokenCount
        coordinates.axiomBoundary coordinates.axiomCount 2
        coordinates.symbolCode)
  simp [compactCertificateNodeSymbolPAEndpointGraphDef,
    CompactCertificateNodeSymbolPAEndpointGraph,
    CompactSymbolPAAxiomTagValid,
    hinputEnv, htailEnv, haxiomEnv, hsuffixEnv, hfuncEnv,
    houterConsEnv, happendEnv, hatZeroEnv, hatOneEnv, hatTwoEnv,
    hcertificateTagValue, haxiomCountValue, hpaTagValue,
    hatZeroSpec, hatOneSpec, hatTwoSpec] <;> tauto

theorem compactCertificateNodeSymbolPAEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeSymbolPAEndpointGraphDef.val := by
  simp [compactCertificateNodeSymbolPAEndpointGraphDef]

theorem compactPAAxiomCertificateTokenParser_symbol
    (paTag arity symbolCode : Nat) (suffix : List Nat)
    (hvalid : CompactSymbolPAAxiomTagValid paTag arity symbolCode) :
    compactPAAxiomCertificateTokenParser
      (paTag :: arity :: symbolCode :: suffix) = some suffix := by
  rcases hvalid with ⟨rfl, hfunc⟩ | ⟨rfl, hrel⟩ <;>
    simp [compactPAAxiomCertificateTokenParser,
      FoundationCompactSyntaxTokenMachine.compactTokenAt, *]

theorem CompactCertificateNodeSymbolPAEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates}
    (hgraph : CompactCertificateNodeSymbolPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag
        coordinates) :
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
    ⟨hinputRows, htailRows, haxiomRows, hsuffixRows,
      hcertificateTag, haxiomCount, hvalid, houterCons, happend,
      hatZero, hatOne, hatTwo⟩
  rcases hinputRows.realize with
    ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
  rcases htailRows.realize with
    ⟨tail, htailCount, htailLayout, htailElementRows⟩
  rcases haxiomRows.realize with
    ⟨axiomTokens, haxiomCount', haxiomLayout, haxiomElementRows⟩
  rcases hsuffixRows.realize with
    ⟨suffix, hsuffixCount, hsuffixLayout, _hsuffixElementRows⟩
  have houterCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.tailBoundary tail.length
        coordinates.inputBoundary input.length 1 := by
    simpa only [hinputCount, htailCount] using houterCons
  have hinput : input = 1 :: tail :=
    houterCons'.eq_cons_of_rows htailElementRows hinputElementRows
  have happend' : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        axiomStart axiomFinish axiomTokens.length
        suffixStart suffixFinish suffix.length
        coordinates.tailStart coordinates.tailFinish tail.length := by
    simpa only [haxiomCount', hsuffixCount, htailCount] using happend
  have htail : tail = axiomTokens ++ suffix :=
    (compactAdditiveNatListAppendSlices_iff_append
      haxiomLayout hsuffixLayout htailLayout).mp happend'
  have hlength : axiomTokens.length = 3 := by omega
  have hzero' : axiomTokens.getI 0 = coordinates.paTag :=
    ((compactAdditiveNatListAtRows_iff_getI haxiomElementRows
      0 coordinates.paTag).mp
      (by simpa only [haxiomCount'] using hatZero)).2
  have hone' : axiomTokens.getI 1 = coordinates.arity :=
    ((compactAdditiveNatListAtRows_iff_getI haxiomElementRows
      1 coordinates.arity).mp
      (by simpa only [haxiomCount'] using hatOne)).2
  have htwo' : axiomTokens.getI 2 = coordinates.symbolCode :=
    ((compactAdditiveNatListAtRows_iff_getI haxiomElementRows
      2 coordinates.symbolCode).mp
      (by simpa only [haxiomCount'] using hatTwo)).2
  have haxiom : axiomTokens =
      [coordinates.paTag, coordinates.arity, coordinates.symbolCode] := by
    cases axiomTokens with
    | nil => simp at hlength
    | cons first rest =>
        cases rest with
        | nil => simp at hlength
        | cons second rest =>
            cases rest with
            | nil => simp at hlength
            | cons third rest =>
                have hrest : rest = [] := by
                  exact List.eq_nil_of_length_eq_zero (by
                    simpa using hlength)
                subst rest
                simp at hzero' hone' htwo'
                simp_all
  rw [haxiom] at htail haxiomLayout
  have hpaParser := compactPAAxiomCertificateTokenParser_symbol
    coordinates.paTag coordinates.arity coordinates.symbolCode suffix hvalid
  refine ⟨input,
    [coordinates.paTag, coordinates.arity, coordinates.symbolCode], suffix,
    hinputLayout, haxiomLayout, hsuffixLayout, ?_⟩
  subst certificateTag
  rw [hinput, htail]
  simp [compactStructuralCertificateNodeParser, hpaParser]
  simpa using consumedTokenPrefix_append
    [coordinates.paTag, coordinates.arity, coordinates.symbolCode] suffix

theorem exists_compactCertificateNodeSymbolPAEndpointGraph_of_results_with_inputLayout
    (paTag arity symbolCode : Nat) (suffix : List Nat)
    (hvalid : CompactSymbolPAAxiomTagValid paTag arity symbolCode) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish suffixStart suffixFinish,
    ∃ coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: paTag :: arity :: symbolCode :: suffix) ∧
        CompactCertificateNodeSymbolPAEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish suffixStart suffixFinish 1 coordinates := by
  let axiomTokens := [paTag, arity, symbolCode]
  let tail := axiomTokens ++ suffix
  let input := 1 :: tail
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let axiomEncoded := compactAdditiveEncode axiomTokens
  let suffixTokens := compactAdditiveEncode suffix
  let tokens := inputTokens ++ tailTokens ++ axiomEncoded ++ suffixTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (tailTokens ++ axiomEncoded ++ suffixTokens)
  dsimp only at hinputRaw
  have hinputTokenEq : [] ++ compactAdditiveEncode input ++
      (tailTokens ++ axiomEncoded ++ suffixTokens) = tokens := by
    simp [inputTokens, tokens, List.append_assoc]
  rw [hinputTokenEq] at hinputRaw
  have htailRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens tail (axiomEncoded ++ suffixTokens)
  dsimp only at htailRaw
  have htailTokenEq : inputTokens ++ compactAdditiveEncode tail ++
      (axiomEncoded ++ suffixTokens) = tokens := by
    simp [tailTokens, tokens, List.append_assoc]
  rw [htailTokenEq] at htailRaw
  have haxiomRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens) axiomTokens suffixTokens
  dsimp only at haxiomRaw
  have haxiomTokenEq : (inputTokens ++ tailTokens) ++
      compactAdditiveEncode axiomTokens ++ suffixTokens = tokens := by
    simp [axiomEncoded, tokens, List.append_assoc]
  rw [haxiomTokenEq] at haxiomRaw
  have hsuffixRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens ++ axiomEncoded) suffix []
  dsimp only at hsuffixRaw
  have hsuffixTokenEq : (inputTokens ++ tailTokens ++ axiomEncoded) ++
      compactAdditiveEncode suffix ++ [] = tokens := by
    simp [suffixTokens, tokens, List.append_assoc]
  rw [hsuffixTokenEq] at hsuffixRaw
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
  have hsuffixLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        tokens.length suffix := by
    simpa only [tokenTable, width, tokens, suffixTokens,
      List.length_append, List.length_nil, Nat.add_zero] using hsuffixRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  rcases htailLayout with
    ⟨tailBoundary, htailStructure, htailElementRows, htailSize⟩
  rcases haxiomLayout with
    ⟨axiomBoundary, haxiomStructure, haxiomElementRows, haxiomSize⟩
  rcases hsuffixLayout with
    ⟨suffixBoundary, hsuffixStructure, hsuffixElementRows, hsuffixSize⟩
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
  have hsuffixRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        suffix.length tokens.length suffixBoundary (Nat.size suffixBoundary) :=
    ⟨hsuffixStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hsuffixElementRows,
      rfl, hsuffixSize⟩
  have houterCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length
        tailBoundary tail.length inputBoundary input.length 1 := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      htailElementRows hinputElementRows
    rfl
  have happend : CompactAdditiveNatListAppendSlices
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        tokens.length suffix.length
        inputTokens.length (inputTokens.length + tailTokens.length)
        tail.length := by
    apply (compactAdditiveNatListAppendSlices_iff_append
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens from
          ⟨axiomBoundary, haxiomStructure, haxiomElementRows, haxiomSize⟩)
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        tokens.length suffix from
          ⟨suffixBoundary, hsuffixStructure, hsuffixElementRows, hsuffixSize⟩)
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        inputTokens.length (inputTokens.length + tailTokens.length) tail from
          ⟨tailBoundary, htailStructure, htailElementRows, htailSize⟩)).2
    rfl
  have hatZero : CompactAdditiveNatListAtRows tokenTable width tokens.length
      axiomBoundary axiomTokens.length 0 paTag := by
    apply (compactAdditiveNatListAtRows_iff_getI
      haxiomElementRows 0 paTag).2
    simp [axiomTokens]
  have hatOne : CompactAdditiveNatListAtRows tokenTable width tokens.length
      axiomBoundary axiomTokens.length 1 arity := by
    apply (compactAdditiveNatListAtRows_iff_getI
      haxiomElementRows 1 arity).2
    simp [axiomTokens]
  have hatTwo : CompactAdditiveNatListAtRows tokenTable width tokens.length
      axiomBoundary axiomTokens.length 2 symbolCode := by
    apply (compactAdditiveNatListAtRows_iff_getI
      haxiomElementRows 2 symbolCode).2
    simp [axiomTokens]
  let coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates :=
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
      suffixBoundary := suffixBoundary
      suffixCount := suffix.length
      suffixBoundarySize := Nat.size suffixBoundary
      paTag := paTag
      arity := arity
      symbolCode := symbolCode }
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length + tailTokens.length,
    inputTokens.length + tailTokens.length + axiomEncoded.length,
    inputTokens.length + tailTokens.length + axiomEncoded.length,
    tokens.length, coordinates,
    by simpa [input, tail, axiomTokens] using hinputLayoutExact, ?_⟩
  exact ⟨hinputRows, htailRows, haxiomRows, hsuffixRows,
    rfl, by simp [coordinates, axiomTokens], hvalid, houterCons, happend,
    hatZero, hatOne, hatTwo⟩

theorem exists_compactCertificateNodeSymbolPAEndpointGraph_of_results
    (paTag arity symbolCode : Nat) (suffix : List Nat)
    (hvalid : CompactSymbolPAAxiomTagValid paTag arity symbolCode) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish suffixStart suffixFinish,
    ∃ coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates,
      CompactCertificateNodeSymbolPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish 1 coordinates := by
  rcases
      exists_compactCertificateNodeSymbolPAEndpointGraph_of_results_with_inputLayout
        paTag arity symbolCode suffix hvalid with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, suffixStart, suffixFinish,
      coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, suffixStart, suffixFinish, coordinates, hgraph⟩

#print axioms compactCertificateNodeSymbolPAEndpointGraphDef_spec
#print axioms compactCertificateNodeSymbolPAEndpointGraphDef_sigmaZero
#print axioms compactPAAxiomCertificateTokenParser_symbol
#print axioms CompactCertificateNodeSymbolPAEndpointGraph.sound
#print axioms exists_compactCertificateNodeSymbolPAEndpointGraph_of_results_with_inputLayout
#print axioms exists_compactCertificateNodeSymbolPAEndpointGraph_of_results

end FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
