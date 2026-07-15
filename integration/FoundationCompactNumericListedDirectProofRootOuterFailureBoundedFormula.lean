import integration.FoundationCompactNumericListedDirectProofRootFailureSemantics
import integration.FoundationCompactNumericListedDirectNatListConsRows
import integration.FoundationCompactNumericListedDirectNatListBoundaryRigidity
import integration.FoundationCompactNumericListedDirectNatListWitnessRows
import integration.FoundationCompactNumericListedDirectVerifierValueLayouts

/-!
# Bounded endpoint for outer proof-root dispatch failure

The public proof-root parser fails before calling a subparser exactly when its
input is empty or its leading tag is greater than nine.  The input and tail are
decoded from one fixed-width table, and the nonempty branch pins their exact
cons relation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootOuterFailureBoundedFormula

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

structure CompactProofRootOuterFailureEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  tag : Nat

def CompactProofRootOuterFailureEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactProofRootOuterFailureEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    (coordinates.inputCount = 0 ∨
      (CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount tailStart coordinates.tailCount tailFinish
            coordinates.tailBoundary coordinates.tailBoundarySize ∧
        9 < coordinates.tag ∧
          CompactAdditiveNatListConsRows
            tokenTable width tokenCount
              coordinates.tailBoundary coordinates.tailCount
              coordinates.inputBoundary coordinates.inputCount
              coordinates.tag))

def compactProofRootOuterFailureEndpointGraphDef :
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
        9 < tag ∧
          !(compactAdditiveNatListConsRowsDef)
            tokenTable width tokenCount
              tailBoundary tailCount inputBoundary inputCount tag))”

def compactProofRootOuterFailureEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactProofRootOuterFailureEndpointCoordinates) :
    Fin 14 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.tailBoundary, coordinates.tailCount,
    coordinates.tailBoundarySize, coordinates.tag]

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootOuterFailureEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactProofRootOuterFailureEndpointCoordinates) :
    compactProofRootOuterFailureEndpointGraphDef.val.Evalb
        (compactProofRootOuterFailureEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish coordinates) ↔
      CompactProofRootOuterFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish coordinates := by
  let env := compactProofRootOuterFailureEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish coordinates
  change compactProofRootOuterFailureEndpointGraphDef.val.Evalb env ↔ _
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
  simp [compactProofRootOuterFailureEndpointGraphDef,
    CompactProofRootOuterFailureEndpointGraph,
    hinputEnv, htailEnv, hconsEnv, hinputCount, htag]

theorem compactProofRootOuterFailureEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootOuterFailureEndpointGraphDef.val := by
  simp [compactProofRootOuterFailureEndpointGraphDef]

theorem CompactProofRootOuterFailureEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat}
    {coordinates : CompactProofRootOuterFailureEndpointCoordinates}
    (hgraph : CompactProofRootOuterFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hgraph with ⟨hinputRows, hempty | hinvalid⟩
  · rcases hinputRows.realize with
      ⟨input, hinputCount, hinputLayout, _hinputElementRows⟩
    have hnil : input = [] := by
      cases input <;> simp_all
    subst input
    exact ⟨[], hinputLayout, rfl⟩
  · rcases hinvalid with ⟨htailRows, htag, hconsRows⟩
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
    have h0 : coordinates.tag ≠ 0 := by omega
    have h1 : coordinates.tag ≠ 1 := by omega
    have h2 : coordinates.tag ≠ 2 := by omega
    have h3 : coordinates.tag ≠ 3 := by omega
    have h4 : coordinates.tag ≠ 4 := by omega
    have h5 : coordinates.tag ≠ 5 := by omega
    have h6 : coordinates.tag ≠ 6 := by omega
    have h7 : coordinates.tag ≠ 7 := by omega
    have h8 : coordinates.tag ≠ 8 := by omega
    have h9 : coordinates.tag ≠ 9 := by omega
    refine ⟨input, hinputLayout, ?_⟩
    simp [compactListedProofNodeFieldsParser, hinput,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem exists_compactProofRootOuterFailureEndpointGraph_of_empty_with_inputLayout :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish,
    ∃ coordinates : CompactProofRootOuterFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish [] ∧
        CompactProofRootOuterFailureEndpointGraph
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
  let coordinates : CompactProofRootOuterFailureEndpointCoordinates :=
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

theorem exists_compactProofRootOuterFailureEndpointGraph_of_empty :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish,
    ∃ coordinates : CompactProofRootOuterFailureEndpointCoordinates,
      CompactProofRootOuterFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish coordinates := by
  rcases exists_compactProofRootOuterFailureEndpointGraph_of_empty_with_inputLayout with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, coordinates, hgraph⟩

theorem exists_compactProofRootOuterFailureEndpointGraph_of_invalid_with_inputLayout
    (tag : Nat) (tail : List Nat) (htag : 9 < tag) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish,
    ∃ coordinates : CompactProofRootOuterFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: tail) ∧
        CompactProofRootOuterFailureEndpointGraph
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
  let coordinates : CompactProofRootOuterFailureEndpointCoordinates :=
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
  exact ⟨hinputRows, Or.inr ⟨htailRows, htag, hconsRows⟩⟩

theorem exists_compactProofRootOuterFailureEndpointGraph_of_invalid
    (tag : Nat) (tail : List Nat) (htag : 9 < tag) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish,
    ∃ coordinates : CompactProofRootOuterFailureEndpointCoordinates,
      CompactProofRootOuterFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish coordinates := by
  rcases exists_compactProofRootOuterFailureEndpointGraph_of_invalid_with_inputLayout
      tag tail htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, coordinates, hgraph⟩

def compactProofRootOuterFailureEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      tailBoundary tailCount tailBoundarySize tag : Nat) :
    CompactProofRootOuterFailureEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    tailBoundary := tailBoundary
    tailCount := tailCount
    tailBoundarySize := tailBoundarySize
    tag := tag }

def CompactProofRootOuterFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ tailBoundary, tailBoundary ≤ endpointBound ∧
  ∃ tailCount, tailCount ≤ endpointBound ∧
  ∃ tailBoundarySize, tailBoundarySize ≤ endpointBound ∧
  ∃ tag, tag ≤ endpointBound ∧
    CompactProofRootOuterFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish
        (compactProofRootOuterFailureEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          tailBoundary tailCount tailBoundarySize tag)

def compactProofRootOuterFailureEndpointBoundedGraphDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish tailStart tailFinish
      endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ tailBoundary <⁺ endpointBound,
    ∃ tailCount <⁺ endpointBound,
    ∃ tailBoundarySize <⁺ endpointBound,
    ∃ tag <⁺ endpointBound,
      !(compactProofRootOuterFailureEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish tailStart tailFinish
        inputBoundary inputCount inputBoundarySize
        tailBoundary tailCount tailBoundarySize tag”

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootOuterFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    compactProofRootOuterFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          tailStart, tailFinish, endpointBound] ↔
      CompactProofRootOuterFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish endpointBound := by
  have hrow
      (tag tailBoundarySize tailCount tailBoundary
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![tag, tailBoundarySize, tailCount, tailBoundary,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                tailStart, tailFinish, endpointBound]
              Empty.elim ∘
            ![(#7 : Semiterm ℒₒᵣ Empty 15), #8, #9, #10, #11, #12, #13,
              #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactProofRootOuterFailureEndpointGraphDef.val ↔
      CompactProofRootOuterFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish
          (compactProofRootOuterFailureEndpointCoordinatesOfValues
            inputBoundary inputCount inputBoundarySize
            tailBoundary tailCount tailBoundarySize tag) := by
    have henv :
        (Semiterm.val
            ![tag, tailBoundarySize, tailCount, tailBoundary,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              tailStart, tailFinish, endpointBound]
            Empty.elim ∘
          ![(#7 : Semiterm ℒₒᵣ Empty 15), #8, #9, #10, #11, #12, #13,
            #6, #5, #4, #3, #2, #1, #0]) =
          compactProofRootOuterFailureEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              tailStart tailFinish
              (compactProofRootOuterFailureEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                tailBoundary tailCount tailBoundarySize tag) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactProofRootOuterFailureEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish _
  simp [compactProofRootOuterFailureEndpointBoundedGraphDef,
    CompactProofRootOuterFailureEndpointBoundedGraph, hrow]

theorem compactProofRootOuterFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootOuterFailureEndpointBoundedGraphDef.val := by
  simp [compactProofRootOuterFailureEndpointBoundedGraphDef]

theorem CompactProofRootOuterFailureEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat}
    (hbounded : CompactProofRootOuterFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound) :
    ∃ coordinates : CompactProofRootOuterFailureEndpointCoordinates,
      CompactProofRootOuterFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      tailBoundary, _, tailCount, _, tailBoundarySize, _, tag, _, hgraph⟩
  exact ⟨compactProofRootOuterFailureEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    tailBoundary tailCount tailBoundarySize tag, hgraph⟩

theorem CompactProofRootOuterFailureEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat}
    {coordinates : CompactProofRootOuterFailureEndpointCoordinates}
    (hgraph : CompactProofRootOuterFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish coordinates) :
    ∃ endpointBound,
      CompactProofRootOuterFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.tailBoundary +
    coordinates.tailCount + coordinates.tailBoundarySize + coordinates.tag
  refine ⟨endpointBound, ?_⟩
  unfold CompactProofRootOuterFailureEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.tailBoundary, ?_,
    coordinates.tailCount, ?_, coordinates.tailBoundarySize, ?_,
    coordinates.tag, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactProofRootOuterFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat}
    (hbounded : CompactProofRootOuterFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactProofRootOuterFailureEndpointBoundedGraph_of_empty :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish endpointBound,
      CompactProofRootOuterFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish endpointBound := by
  rcases exists_compactProofRootOuterFailureEndpointGraph_of_empty with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, endpointBound, hbounded⟩

theorem exists_compactProofRootOuterFailureEndpointBoundedGraph_of_empty_with_inputLayout :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish [] ∧
        CompactProofRootOuterFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound := by
  rcases exists_compactProofRootOuterFailureEndpointGraph_of_empty_with_inputLayout with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, hinputLayout, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, endpointBound, hinputLayout, hbounded⟩

theorem exists_compactProofRootOuterFailureEndpointBoundedGraph_of_invalid
    (tag : Nat) (tail : List Nat) (htag : 9 < tag) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish endpointBound,
      CompactProofRootOuterFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish endpointBound := by
  rcases exists_compactProofRootOuterFailureEndpointGraph_of_invalid
      tag tail htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, endpointBound, hbounded⟩

theorem exists_compactProofRootOuterFailureEndpointBoundedGraph_of_invalid_with_inputLayout
    (tag : Nat) (tail : List Nat) (htag : 9 < tag) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: tail) ∧
        CompactProofRootOuterFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound := by
  rcases exists_compactProofRootOuterFailureEndpointGraph_of_invalid_with_inputLayout
      tag tail htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, hinputLayout, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, endpointBound, hinputLayout, hbounded⟩

#print axioms compactProofRootOuterFailureEndpointGraphDef_spec
#print axioms compactProofRootOuterFailureEndpointGraphDef_sigmaZero
#print axioms CompactProofRootOuterFailureEndpointGraph.sound
#print axioms exists_compactProofRootOuterFailureEndpointGraph_of_empty
#print axioms exists_compactProofRootOuterFailureEndpointGraph_of_invalid
#print axioms compactProofRootOuterFailureEndpointBoundedGraphDef_spec
#print axioms compactProofRootOuterFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactProofRootOuterFailureEndpointGraph.exists_bounded
#print axioms CompactProofRootOuterFailureEndpointBoundedGraph.sound
#print axioms exists_compactProofRootOuterFailureEndpointBoundedGraph_of_empty
#print axioms exists_compactProofRootOuterFailureEndpointBoundedGraph_of_invalid

end FoundationCompactNumericListedDirectProofRootOuterFailureBoundedFormula
