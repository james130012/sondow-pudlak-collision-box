import integration.FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpoint

/-!
# Bounded formula for outer structural-certificate dispatch failure

Seven local endpoint coordinates are existentially bounded by one public value.
The public relation exposes only the shared token-table slice and that bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeOuterFailureBoundedFormula

open FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpoint

def compactCertificateNodeOuterFailureEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      tailBoundary tailCount tailBoundarySize tag : Nat) :
    CompactCertificateNodeOuterFailureEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    tailBoundary := tailBoundary
    tailCount := tailCount
    tailBoundarySize := tailBoundarySize
    tag := tag }

def CompactCertificateNodeOuterFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ tailBoundary, tailBoundary ≤ endpointBound ∧
  ∃ tailCount, tailCount ≤ endpointBound ∧
  ∃ tailBoundarySize, tailBoundarySize ≤ endpointBound ∧
  ∃ tag, tag ≤ endpointBound ∧
    CompactCertificateNodeOuterFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish
        (compactCertificateNodeOuterFailureEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          tailBoundary tailCount tailBoundarySize tag)

def compactCertificateNodeOuterFailureEndpointBoundedGraphDef :
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
      !(compactCertificateNodeOuterFailureEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish tailStart tailFinish
        inputBoundary inputCount inputBoundarySize
        tailBoundary tailCount tailBoundarySize tag”

set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeOuterFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat) :
    compactCertificateNodeOuterFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          tailStart, tailFinish, endpointBound] ↔
      CompactCertificateNodeOuterFailureEndpointBoundedGraph
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
        compactCertificateNodeOuterFailureEndpointGraphDef.val ↔
      CompactCertificateNodeOuterFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish
          (compactCertificateNodeOuterFailureEndpointCoordinatesOfValues
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
          compactCertificateNodeOuterFailureEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              tailStart tailFinish
              (compactCertificateNodeOuterFailureEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                tailBoundary tailCount tailBoundarySize tag) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactCertificateNodeOuterFailureEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish _
  simp [compactCertificateNodeOuterFailureEndpointBoundedGraphDef,
    CompactCertificateNodeOuterFailureEndpointBoundedGraph, hrow]

theorem compactCertificateNodeOuterFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeOuterFailureEndpointBoundedGraphDef.val := by
  simp [compactCertificateNodeOuterFailureEndpointBoundedGraphDef]

theorem CompactCertificateNodeOuterFailureEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat}
    (hbounded : CompactCertificateNodeOuterFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound) :
    ∃ coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates,
      CompactCertificateNodeOuterFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      tailBoundary, _, tailCount, _, tailBoundarySize, _, tag, _, hgraph⟩
  exact ⟨compactCertificateNodeOuterFailureEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    tailBoundary tailCount tailBoundarySize tag, hgraph⟩

theorem CompactCertificateNodeOuterFailureEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat}
    {coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates}
    (hgraph : CompactCertificateNodeOuterFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish coordinates) :
    ∃ endpointBound,
      CompactCertificateNodeOuterFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.tailBoundary +
    coordinates.tailCount + coordinates.tailBoundarySize + coordinates.tag
  refine ⟨endpointBound, ?_⟩
  unfold CompactCertificateNodeOuterFailureEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.tailBoundary, ?_,
    coordinates.tailCount, ?_, coordinates.tailBoundarySize, ?_,
    coordinates.tag, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactCertificateNodeOuterFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound : Nat}
    (hbounded : CompactCertificateNodeOuterFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish endpointBound) :
    ∃ input : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactCertificateNodeOuterFailureEndpointBoundedGraph_of_empty :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish endpointBound,
      CompactCertificateNodeOuterFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish endpointBound := by
  rcases exists_compactCertificateNodeOuterFailureEndpointGraph_of_empty with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, hgraph⟩
  rcases CompactCertificateNodeOuterFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, endpointBound, hbounded⟩

theorem exists_compactCertificateNodeOuterFailureEndpointBoundedGraph_of_empty_with_inputLayout :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish [] ∧
        CompactCertificateNodeOuterFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound := by
  rcases exists_compactCertificateNodeOuterFailureEndpointGraph_of_empty_with_inputLayout with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, hinputLayout, hgraph⟩
  rcases CompactCertificateNodeOuterFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, endpointBound, hinputLayout, hbounded⟩

theorem exists_compactCertificateNodeOuterFailureEndpointBoundedGraph_of_invalid
    (tag : Nat) (tail : List Nat)
    (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) (h3 : tag ≠ 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish endpointBound,
      CompactCertificateNodeOuterFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish endpointBound := by
  rcases exists_compactCertificateNodeOuterFailureEndpointGraph_of_invalid
      tag tail h0 h1 h2 h3 with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, hgraph⟩
  rcases CompactCertificateNodeOuterFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, endpointBound, hbounded⟩

theorem exists_compactCertificateNodeOuterFailureEndpointBoundedGraph_of_invalid_with_inputLayout
    (tag : Nat) (tail : List Nat)
    (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) (h3 : tag ≠ 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: tail) ∧
        CompactCertificateNodeOuterFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound := by
  rcases
      exists_compactCertificateNodeOuterFailureEndpointGraph_of_invalid_with_inputLayout
        tag tail h0 h1 h2 h3 with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      tailStart, tailFinish, coordinates, hinputLayout, hgraph⟩
  rcases CompactCertificateNodeOuterFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    tailStart, tailFinish, endpointBound, hinputLayout, hbounded⟩

#print axioms compactCertificateNodeOuterFailureEndpointBoundedGraphDef_spec
#print axioms compactCertificateNodeOuterFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactCertificateNodeOuterFailureEndpointGraph.exists_bounded
#print axioms CompactCertificateNodeOuterFailureEndpointBoundedGraph.sound
#print axioms exists_compactCertificateNodeOuterFailureEndpointBoundedGraph_of_empty
#print axioms exists_compactCertificateNodeOuterFailureEndpointBoundedGraph_of_invalid

end FoundationCompactNumericListedDirectCertificateNodeOuterFailureBoundedFormula
