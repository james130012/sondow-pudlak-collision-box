import integration.FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint
import integration.FoundationCompactNumericListedDirectNatListAppendSlices

/-!
# Exact endpoint for fixed one-token PA-axiom certificates

Twenty PA-axiom certificate tags consume one token: all tags below 22 except
the function- and relation-symbol tags 3 and 4.  This module represents the
outer structural tag, the PA tag, the consumed axiom-token list, and the final
suffix in one fixed-width table.  No parser-success proposition is stored in
the graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
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

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

def CompactFixedPAAxiomTag (paTag : Nat) : Prop :=
  paTag < 22 ∧ paTag ≠ 3 ∧ paTag ≠ 4

structure CompactCertificateNodeFixedPAEndpointCoordinates where
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

def CompactCertificateNodeFixedPAEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates) : Prop :=
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
    CompactFixedPAAxiomTag coordinates.paTag ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.tailBoundary coordinates.tailCount
        coordinates.inputBoundary coordinates.inputCount 1 ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.suffixBoundary coordinates.suffixCount
        coordinates.tailBoundary coordinates.tailCount coordinates.paTag ∧
    CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        axiomStart axiomFinish coordinates.axiomCount
        suffixStart suffixFinish coordinates.suffixCount
        coordinates.tailStart coordinates.tailFinish coordinates.tailCount

def compactCertificateNodeFixedPAEndpointGraphDef : 𝚺₀.Semisentence 25 :=
  .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      axiomBoundary axiomCount axiomBoundarySize
      suffixBoundary suffixCount suffixBoundarySize paTag.
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
    certificateTag = 1 ∧
    paTag < 22 ∧ paTag ≠ 3 ∧ paTag ≠ 4 ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount inputBoundary inputCount 1 ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        suffixBoundary suffixCount tailBoundary tailCount paTag ∧
    !(compactAdditiveNatListAppendSlicesDef)
      tokenTable width tokenCount
        axiomStart axiomFinish axiomCount
        suffixStart suffixFinish suffixCount
        tailStart tailFinish tailCount”

def compactCertificateNodeFixedPAEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates) :
    Fin 25 → Nat :=
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
    coordinates.suffixBoundarySize, coordinates.paTag]

@[simp] theorem compactCertificateNodeFixedPAEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates) :
    compactCertificateNodeFixedPAEndpointGraphDef.val.Evalb
        (compactCertificateNodeFixedPAEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish suffixStart suffixFinish certificateTag
            coordinates) ↔
      CompactCertificateNodeFixedPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish certificateTag
          coordinates := by
  let env := compactCertificateNodeFixedPAEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag coordinates
  change compactCertificateNodeFixedPAEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #3, #11, #4, #10, #12]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #13, #16, #14, #15, #17]) =
        ![tokenTable, width, tokenCount, coordinates.tailStart,
          coordinates.tailCount, coordinates.tailFinish,
          coordinates.tailBoundary, coordinates.tailBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have haxiomEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #5, #19, #6, #18, #20]) =
        ![tokenTable, width, tokenCount, axiomStart,
          coordinates.axiomCount, axiomFinish,
          coordinates.axiomBoundary, coordinates.axiomBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hsuffixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #7, #22, #8, #21, #23]) =
        ![tokenTable, width, tokenCount, suffixStart,
          coordinates.suffixCount, suffixFinish,
          coordinates.suffixBoundary, coordinates.suffixBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have houterConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #15, #16, #10, #11, ‘1’]) =
        ![tokenTable, width, tokenCount,
          coordinates.tailBoundary, coordinates.tailCount,
          coordinates.inputBoundary, coordinates.inputCount, 1] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeFixedPAEndpointEnvironment]
  have hinnerConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #21, #22, #15, #16, #24]) =
        ![tokenTable, width, tokenCount,
          coordinates.suffixBoundary, coordinates.suffixCount,
          coordinates.tailBoundary, coordinates.tailCount, coordinates.paTag] := by
    funext index
    fin_cases index <;> rfl
  have happendEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2,
          #5, #6, #19, #7, #8, #22, #13, #14, #16]) =
        ![tokenTable, width, tokenCount,
          axiomStart, axiomFinish, coordinates.axiomCount,
          suffixStart, suffixFinish, coordinates.suffixCount,
          coordinates.tailStart, coordinates.tailFinish,
          coordinates.tailCount] := by
    funext index
    fin_cases index <;> rfl
  have hcertificateTagValue : env 9 = certificateTag := rfl
  have hpaTagValue : env 24 = coordinates.paTag := rfl
  simp [compactCertificateNodeFixedPAEndpointGraphDef,
    CompactCertificateNodeFixedPAEndpointGraph, CompactFixedPAAxiomTag,
    hinputEnv, htailEnv, haxiomEnv, hsuffixEnv,
    houterConsEnv, hinnerConsEnv, happendEnv,
    hcertificateTagValue, hpaTagValue] <;> tauto

theorem compactCertificateNodeFixedPAEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeFixedPAEndpointGraphDef.val := by
  simp [compactCertificateNodeFixedPAEndpointGraphDef]

theorem compactPAAxiomCertificateTokenParser_fixed
    (paTag : Nat) (suffix : List Nat)
    (hfixed : CompactFixedPAAxiomTag paTag) :
    compactPAAxiomCertificateTokenParser (paTag :: suffix) = some suffix := by
  rcases hfixed with ⟨hlt, h3, h4⟩
  have h22 : paTag ≠ 22 := by omega
  simp [compactPAAxiomCertificateTokenParser, h3, h4, h22, hlt]

theorem CompactCertificateNodeFixedPAEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeFixedPAEndpointCoordinates}
    (hgraph : CompactCertificateNodeFixedPAEndpointGraph
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
      hcertificateTag, hfixed, houterCons, hinnerCons, happend⟩
  rcases hinputRows.realize with
    ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
  rcases htailRows.realize with
    ⟨tail, htailCount, htailLayout, htailElementRows⟩
  rcases haxiomRows.realize with
    ⟨axiomTokens, haxiomCount, haxiomLayout, _haxiomElementRows⟩
  rcases hsuffixRows.realize with
    ⟨suffix, hsuffixCount, hsuffixLayout, hsuffixElementRows⟩
  have houterCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.tailBoundary tail.length
        coordinates.inputBoundary input.length 1 := by
    simpa only [hinputCount, htailCount] using houterCons
  have hinput : input = 1 :: tail :=
    houterCons'.eq_cons_of_rows htailElementRows hinputElementRows
  have hinnerCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.suffixBoundary suffix.length
        coordinates.tailBoundary tail.length coordinates.paTag := by
    simpa only [htailCount, hsuffixCount] using hinnerCons
  have htailCons : tail = coordinates.paTag :: suffix :=
    hinnerCons'.eq_cons_of_rows hsuffixElementRows htailElementRows
  have happend' : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
        axiomStart axiomFinish axiomTokens.length
        suffixStart suffixFinish suffix.length
        coordinates.tailStart coordinates.tailFinish tail.length := by
    simpa only [haxiomCount, hsuffixCount, htailCount] using happend
  have htailAppend : tail = axiomTokens ++ suffix :=
    (compactAdditiveNatListAppendSlices_iff_append
      haxiomLayout hsuffixLayout htailLayout).mp happend'
  have haxiomAppend : axiomTokens ++ suffix =
      [coordinates.paTag] ++ suffix := by
    rw [← htailAppend]
    simpa using htailCons
  have haxiom : axiomTokens = [coordinates.paTag] :=
    List.append_cancel_right haxiomAppend
  have hpaParser := compactPAAxiomCertificateTokenParser_fixed
    coordinates.paTag suffix hfixed
  have hprefix : consumedTokenPrefix
      (coordinates.paTag :: suffix) suffix = [coordinates.paTag] := by
    simpa using consumedTokenPrefix_append [coordinates.paTag] suffix
  refine ⟨input, axiomTokens, suffix,
    hinputLayout, haxiomLayout, hsuffixLayout, ?_⟩
  subst certificateTag
  rw [hinput, htailCons]
  simp [compactStructuralCertificateNodeParser,
    hpaParser, hprefix, haxiom]

theorem exists_compactCertificateNodeFixedPAEndpointGraph_of_results_with_inputLayout
    (paTag : Nat) (suffix : List Nat)
    (hfixed : CompactFixedPAAxiomTag paTag) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish suffixStart suffixFinish,
    ∃ coordinates : CompactCertificateNodeFixedPAEndpointCoordinates,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          inputStart inputFinish (1 :: paTag :: suffix) ∧
        CompactCertificateNodeFixedPAEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish suffixStart suffixFinish 1 coordinates := by
  let tail := paTag :: suffix
  let input := 1 :: tail
  let axiomTokens := [paTag]
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
  have hinnerCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length
        suffixBoundary suffix.length tailBoundary tail.length paTag := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hsuffixElementRows htailElementRows
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
  let coordinates : CompactCertificateNodeFixedPAEndpointCoordinates :=
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
      paTag := paTag }
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length + tailTokens.length,
    inputTokens.length + tailTokens.length + axiomEncoded.length,
    inputTokens.length + tailTokens.length + axiomEncoded.length,
    tokens.length, coordinates,
    by simpa [input, tail] using hinputLayoutExact, ?_⟩
  exact ⟨hinputRows, htailRows, haxiomRows, hsuffixRows,
    rfl, hfixed, houterCons, hinnerCons, happend⟩

theorem exists_compactCertificateNodeFixedPAEndpointGraph_of_results
    (paTag : Nat) (suffix : List Nat)
    (hfixed : CompactFixedPAAxiomTag paTag) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish suffixStart suffixFinish,
    ∃ coordinates : CompactCertificateNodeFixedPAEndpointCoordinates,
      CompactCertificateNodeFixedPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish 1 coordinates := by
  rcases
      exists_compactCertificateNodeFixedPAEndpointGraph_of_results_with_inputLayout
        paTag suffix hfixed with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, suffixStart, suffixFinish,
      coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, suffixStart, suffixFinish, coordinates, hgraph⟩

#print axioms compactCertificateNodeFixedPAEndpointGraphDef_spec
#print axioms compactCertificateNodeFixedPAEndpointGraphDef_sigmaZero
#print axioms compactPAAxiomCertificateTokenParser_fixed
#print axioms CompactCertificateNodeFixedPAEndpointGraph.sound
#print axioms exists_compactCertificateNodeFixedPAEndpointGraph_of_results_with_inputLayout
#print axioms exists_compactCertificateNodeFixedPAEndpointGraph_of_results

end FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
