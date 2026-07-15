import integration.FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint

/-!
# Bounded formula for immediate PA-certificate failure

The fourteen local endpoint coordinates are quantified below one public bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedFormula

open FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint

def compactCertificateNodePAImmediateFailureEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize paTag : Nat) :
    CompactCertificateNodePAImmediateFailureEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    tailStart := tailStart
    tailFinish := tailFinish
    tailBoundary := tailBoundary
    tailCount := tailCount
    tailBoundarySize := tailBoundarySize
    bodyStart := bodyStart
    bodyFinish := bodyFinish
    bodyBoundary := bodyBoundary
    bodyCount := bodyCount
    bodyBoundarySize := bodyBoundarySize
    paTag := paTag }

def CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ tailStart, tailStart ≤ endpointBound ∧
  ∃ tailFinish, tailFinish ≤ endpointBound ∧
  ∃ tailBoundary, tailBoundary ≤ endpointBound ∧
  ∃ tailCount, tailCount ≤ endpointBound ∧
  ∃ tailBoundarySize, tailBoundarySize ≤ endpointBound ∧
  ∃ bodyStart, bodyStart ≤ endpointBound ∧
  ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
  ∃ bodyBoundary, bodyBoundary ≤ endpointBound ∧
  ∃ bodyCount, bodyCount ≤ endpointBound ∧
  ∃ bodyBoundarySize, bodyBoundarySize ≤ endpointBound ∧
  ∃ paTag, paTag ≤ endpointBound ∧
    CompactCertificateNodePAImmediateFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        (compactCertificateNodePAImmediateFailureEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          tailStart tailFinish tailBoundary tailCount tailBoundarySize
          bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize paTag)

def compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ tailStart <⁺ endpointBound,
    ∃ tailFinish <⁺ endpointBound,
    ∃ tailBoundary <⁺ endpointBound,
    ∃ tailCount <⁺ endpointBound,
    ∃ tailBoundarySize <⁺ endpointBound,
    ∃ bodyStart <⁺ endpointBound,
    ∃ bodyFinish <⁺ endpointBound,
    ∃ bodyBoundary <⁺ endpointBound,
    ∃ bodyCount <⁺ endpointBound,
    ∃ bodyBoundarySize <⁺ endpointBound,
    ∃ paTag <⁺ endpointBound,
      !(compactCertificateNodePAImmediateFailureEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        inputBoundary inputCount inputBoundarySize
        tailStart tailFinish tailBoundary tailCount tailBoundarySize
        bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize paTag”

set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish, endpointBound] ↔
      CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  have hrow
      (paTag bodyBoundarySize bodyCount bodyBoundary bodyFinish bodyStart
        tailBoundarySize tailCount tailBoundary tailFinish tailStart
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![paTag, bodyBoundarySize, bodyCount, bodyBoundary,
                bodyFinish, bodyStart,
                tailBoundarySize, tailCount, tailBoundary,
                tailFinish, tailStart,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#14 : Semiterm ℒₒᵣ Empty 20), #15, #16, #17, #18,
              #13, #12, #11, #10, #9, #8, #7, #6,
              #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactCertificateNodePAImmediateFailureEndpointGraphDef.val ↔
      CompactCertificateNodePAImmediateFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          (compactCertificateNodePAImmediateFailureEndpointCoordinatesOfValues
            inputBoundary inputCount inputBoundarySize
            tailStart tailFinish tailBoundary tailCount tailBoundarySize
            bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize paTag) := by
    have henv :
        (Semiterm.val
            ![paTag, bodyBoundarySize, bodyCount, bodyBoundary,
              bodyFinish, bodyStart,
              tailBoundarySize, tailCount, tailBoundary,
              tailFinish, tailStart,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              endpointBound]
            Empty.elim ∘
          ![(#14 : Semiterm ℒₒᵣ Empty 20), #15, #16, #17, #18,
            #13, #12, #11, #10, #9, #8, #7, #6,
            #5, #4, #3, #2, #1, #0]) =
          compactCertificateNodePAImmediateFailureEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              (compactCertificateNodePAImmediateFailureEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                tailStart tailFinish tailBoundary tailCount tailBoundarySize
                bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
                paTag) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactCertificateNodePAImmediateFailureEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish _
  simp [compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef,
    CompactCertificateNodePAImmediateFailureEndpointBoundedGraph, hrow]

theorem compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef.val := by
  simp [compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef]

theorem CompactCertificateNodePAImmediateFailureEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hbounded : CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates,
      CompactCertificateNodePAImmediateFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      tailStart, _, tailFinish, _, tailBoundary, _, tailCount, _,
      tailBoundarySize, _, bodyStart, _, bodyFinish, _, bodyBoundary, _,
      bodyCount, _, bodyBoundarySize, _, paTag, _, hgraph⟩
  exact ⟨compactCertificateNodePAImmediateFailureEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    tailStart tailFinish tailBoundary tailCount tailBoundarySize
    bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize paTag, hgraph⟩

theorem CompactCertificateNodePAImmediateFailureEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates}
    (hgraph : CompactCertificateNodePAImmediateFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    ∃ endpointBound,
      CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.tailStart +
    coordinates.tailFinish + coordinates.tailBoundary +
    coordinates.tailCount + coordinates.tailBoundarySize +
    coordinates.bodyStart + coordinates.bodyFinish +
    coordinates.bodyBoundary + coordinates.bodyCount +
    coordinates.bodyBoundarySize + coordinates.paTag
  refine ⟨endpointBound, ?_⟩
  unfold CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.tailStart, ?_,
    coordinates.tailFinish, ?_, coordinates.tailBoundary, ?_,
    coordinates.tailCount, ?_, coordinates.tailBoundarySize, ?_,
    coordinates.bodyStart, ?_, coordinates.bodyFinish, ?_,
    coordinates.bodyBoundary, ?_, coordinates.bodyCount, ?_,
    coordinates.bodyBoundarySize, ?_, coordinates.paTag, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactCertificateNodePAImmediateFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hbounded : CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ input : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_empty :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint.exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_empty with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, hgraph⟩
  rcases CompactCertificateNodePAImmediateFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hbounded⟩

theorem exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_empty_with_inputLayout :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish [1] ∧
        CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint.exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_empty_with_inputLayout with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, hinputLayout, hgraph⟩
  rcases CompactCertificateNodePAImmediateFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, hbounded⟩

theorem exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_large
    (paTag : Nat) (body : List Nat) (htag : 22 < paTag) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint.exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_large
        paTag body htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, hgraph⟩
  rcases CompactCertificateNodePAImmediateFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hbounded⟩

theorem exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_large_with_inputLayout
    (paTag : Nat) (body : List Nat) (htag : 22 < paTag) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: paTag :: body) ∧
        CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint.exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_large_with_inputLayout
        paTag body htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, hinputLayout, hgraph⟩
  rcases CompactCertificateNodePAImmediateFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, hbounded⟩

#print axioms compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef_spec
#print axioms compactCertificateNodePAImmediateFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactCertificateNodePAImmediateFailureEndpointGraph.exists_bounded
#print axioms CompactCertificateNodePAImmediateFailureEndpointBoundedGraph.sound
#print axioms exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_empty
#print axioms exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_large

end FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedFormula
