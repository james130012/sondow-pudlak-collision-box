import integration.FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint

/-!
# Exact endpoint for outer structural-certificate dispatch failure

The outer node parser fails immediately on an empty input or on a nonempty
input whose leading tag is not one of 0, 1, 2, 3.  Failure below tag 1 is kept
for the separate PA-certificate endpoint.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpoint

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

structure CompactCertificateNodeOuterFailureEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  tag : Nat

def CompactCertificateNodeOuterFailureEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    (coordinates.inputCount = 0 ∨
      (CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount tailStart coordinates.tailCount tailFinish
            coordinates.tailBoundary coordinates.tailBoundarySize ∧
        coordinates.tag ≠ 0 ∧ coordinates.tag ≠ 1 ∧
        coordinates.tag ≠ 2 ∧ coordinates.tag ≠ 3 ∧
          CompactAdditiveNatListConsRows
            tokenTable width tokenCount
              coordinates.tailBoundary coordinates.tailCount
              coordinates.inputBoundary coordinates.inputCount
              coordinates.tag))

def compactCertificateNodeOuterFailureEndpointGraphDef :
    𝚺₀.Semisentence 14 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish tailStart tailFinish
      inputBoundary inputCount inputBoundarySize
      tailBoundary tailCount tailBoundarySize tag.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    (inputCount = 0 ∨
      (!(compactAdditiveNatListWitnessRowsDef)
          tokenTable width tokenCount tailStart tailCount tailFinish
            tailBoundary tailBoundarySize ∧
        tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 3 ∧
          !(compactAdditiveNatListConsRowsDef)
            tokenTable width tokenCount
              tailBoundary tailCount inputBoundary inputCount tag))”

def compactCertificateNodeOuterFailureEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates) :
    Fin 14 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.tailBoundary, coordinates.tailCount,
    coordinates.tailBoundarySize, coordinates.tag]

set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeOuterFailureEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates) :
    compactCertificateNodeOuterFailureEndpointGraphDef.val.Evalb
        (compactCertificateNodeOuterFailureEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish coordinates) ↔
      CompactCertificateNodeOuterFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish coordinates := by
  let env := compactCertificateNodeOuterFailureEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish coordinates
  change compactCertificateNodeOuterFailureEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #3, #8, #4, #7, #9]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #5, #11, #6, #10, #12]) =
        ![tokenTable, width, tokenCount, tailStart,
          coordinates.tailCount, tailFinish,
          coordinates.tailBoundary, coordinates.tailBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #10, #11, #7, #8, #13]) =
        ![tokenTable, width, tokenCount,
          coordinates.tailBoundary, coordinates.tailCount,
          coordinates.inputBoundary, coordinates.inputCount,
          coordinates.tag] := by
    funext index
    fin_cases index <;> rfl
  have hinputCount : env 8 = coordinates.inputCount := rfl
  have htag : env 13 = coordinates.tag := rfl
  simp [compactCertificateNodeOuterFailureEndpointGraphDef,
    CompactCertificateNodeOuterFailureEndpointGraph,
    hinputEnv, htailEnv, hconsEnv, hinputCount, htag] <;> tauto

theorem compactCertificateNodeOuterFailureEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeOuterFailureEndpointGraphDef.val := by
  simp [compactCertificateNodeOuterFailureEndpointGraphDef]

theorem CompactCertificateNodeOuterFailureEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat}
    {coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates}
    (hgraph : CompactCertificateNodeOuterFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactStructuralCertificateNodeParser input = none := by
  rcases hgraph with ⟨hinputRows, hempty | hinvalid⟩
  · rcases hinputRows.realize with
      ⟨input, hinputCount, hinputLayout, _hinputElementRows⟩
    have hnil : input = [] := by
      cases input <;> simp_all
    subst input
    exact ⟨[], hinputLayout, by
      simp [compactStructuralCertificateNodeParser]⟩
  · rcases hinvalid with ⟨htailRows, h0, h1, h2, h3, hconsRows⟩
    rcases hinputRows.realize with
      ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
    rcases htailRows.realize with
      ⟨tail, htailCount, _htailLayout, htailElementRows⟩
    have hconsRows' : CompactAdditiveNatListConsRows
        tokenTable width tokenCount
          coordinates.tailBoundary tail.length
          coordinates.inputBoundary input.length coordinates.tag := by
      simpa only [hinputCount, htailCount] using hconsRows
    have hinput : input = coordinates.tag :: tail :=
      hconsRows'.eq_cons_of_rows htailElementRows hinputElementRows
    refine ⟨input, hinputLayout, ?_⟩
    simp [compactStructuralCertificateNodeParser, hinput, h0, h1, h2, h3]

theorem exists_compactCertificateNodeOuterFailureEndpointGraph_of_empty_with_inputLayout :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish,
    ∃ coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish [] ∧
        CompactCertificateNodeOuterFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish coordinates := by
  let input := ([] : List Nat)
  let inputTokens := compactAdditiveEncode input
  let width := (compactBinaryNatPayloadBits inputTokens).length
  let tokenTable := compactFixedWidthTableCode width inputTokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical [] input []
  dsimp only at hinputRaw
  have htokenEq : [] ++ compactAdditiveEncode input ++ [] = inputTokens := by
    simp [inputTokens]
  rw [htokenEq] at hinputRaw
  have hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width inputTokens.length 0 inputTokens.length input := by
    simpa only [tokenTable, width, List.length_nil, Nat.zero_add,
      Nat.add_zero, inputTokens] using hinputRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width inputTokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputSize⟩
  let coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      tailBoundary := 0
      tailCount := 0
      tailBoundarySize := 0
      tag := 0 }
  refine ⟨tokenTable, width, inputTokens.length, 0, inputTokens.length,
    0, 0, coordinates, by simpa [input] using hinputLayoutExact, ?_⟩
  exact ⟨hinputRows, Or.inl rfl⟩

theorem exists_compactCertificateNodeOuterFailureEndpointGraph_of_empty :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish,
    ∃ coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates,
      CompactCertificateNodeOuterFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish coordinates := by
  rcases exists_compactCertificateNodeOuterFailureEndpointGraph_of_empty_with_inputLayout with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, coordinates, hgraph⟩

theorem exists_compactCertificateNodeOuterFailureEndpointGraph_of_invalid_with_inputLayout
    (tag : Nat) (tail : List Nat)
    (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) (h3 : tag ≠ 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish,
    ∃ coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: tail) ∧
        CompactCertificateNodeOuterFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish coordinates := by
  let input := tag :: tail
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let tokens := inputTokens ++ tailTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input tailTokens
  dsimp only at hinputRaw
  have hinputTokenEq :
      [] ++ compactAdditiveEncode input ++ tailTokens = tokens := by
    simp [inputTokens, tokens]
  rw [hinputTokenEq] at hinputRaw
  have htailRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens tail []
  dsimp only at htailRaw
  have htailTokenEq :
      inputTokens ++ compactAdditiveEncode tail ++ [] = tokens := by
    simp [tailTokens, tokens]
  rw [htailTokenEq] at htailRaw
  have hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length 0 inputTokens.length input := by
    simpa only [tokenTable, width, inputTokens,
      List.length_nil, Nat.zero_add] using hinputRaw
  have htailLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length inputTokens.length tokens.length tail := by
    simpa only [tokenTable, width, tokens, tailTokens,
      List.length_append, List.length_nil, Nat.add_zero] using htailRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  rcases htailLayout with
    ⟨tailBoundary, htailStructure, htailElementRows, htailSize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputSize⟩
  have htailRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length tail.length tokens.length
        tailBoundary (Nat.size tailBoundary) :=
    ⟨htailStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        htailElementRows,
      rfl, htailSize⟩
  have hconsRows : CompactAdditiveNatListConsRows
      tokenTable width tokens.length tailBoundary tail.length
        inputBoundary input.length tag := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      htailElementRows hinputElementRows
    rfl
  let coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      tailBoundary := tailBoundary
      tailCount := tail.length
      tailBoundarySize := Nat.size tailBoundary
      tag := tag }
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length, tokens.length, coordinates,
    by simpa [input] using hinputLayoutExact, ?_⟩
  exact ⟨hinputRows, Or.inr ⟨htailRows, h0, h1, h2, h3, hconsRows⟩⟩

theorem exists_compactCertificateNodeOuterFailureEndpointGraph_of_invalid
    (tag : Nat) (tail : List Nat)
    (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) (h3 : tag ≠ 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish,
    ∃ coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates,
      CompactCertificateNodeOuterFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish coordinates := by
  rcases
      exists_compactCertificateNodeOuterFailureEndpointGraph_of_invalid_with_inputLayout
        tag tail h0 h1 h2 h3 with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, coordinates, hgraph⟩

#print axioms compactCertificateNodeOuterFailureEndpointGraphDef_spec
#print axioms compactCertificateNodeOuterFailureEndpointGraphDef_sigmaZero
#print axioms CompactCertificateNodeOuterFailureEndpointGraph.sound
#print axioms exists_compactCertificateNodeOuterFailureEndpointGraph_of_empty
#print axioms exists_compactCertificateNodeOuterFailureEndpointGraph_of_invalid

end FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpoint
