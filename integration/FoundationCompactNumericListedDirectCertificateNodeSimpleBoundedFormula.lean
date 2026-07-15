import integration.FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint

/-!
# Bounded formula for the simple structural-certificate endpoint

The six local list coordinates of the tag 0/2/3 endpoint are existentially
bounded by one public value.  No list, layout, or graph-existence parameter is
left at the public arithmetic boundary.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSimpleBoundedFormula

open FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint

def compactCertificateNodeSimpleEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      suffixBoundary suffixCount suffixBoundarySize : Nat) :
    CompactCertificateNodeSimpleEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    suffixBoundary := suffixBoundary
    suffixCount := suffixCount
    suffixBoundarySize := suffixBoundarySize }

def CompactCertificateNodeSimpleEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ suffixBoundary, suffixBoundary ≤ endpointBound ∧
  ∃ suffixCount, suffixCount ≤ endpointBound ∧
  ∃ suffixBoundarySize, suffixBoundarySize ≤ endpointBound ∧
    CompactCertificateNodeSimpleEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag
        (compactCertificateNodeSimpleEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          suffixBoundary suffixCount suffixBoundarySize)

def compactCertificateNodeSimpleEndpointBoundedGraphDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ suffixBoundary <⁺ endpointBound,
    ∃ suffixCount <⁺ endpointBound,
    ∃ suffixBoundarySize <⁺ endpointBound,
      !(compactCertificateNodeSimpleEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag
        inputBoundary inputCount inputBoundarySize
        suffixBoundary suffixCount suffixBoundarySize”

@[simp] theorem compactCertificateNodeSimpleEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat) :
    compactCertificateNodeSimpleEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          suffixStart, suffixFinish, tag, endpointBound] ↔
      CompactCertificateNodeSimpleEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag endpointBound := by
  have hrow
      (suffixBoundarySize suffixCount suffixBoundary
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![suffixBoundarySize, suffixCount, suffixBoundary,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                suffixStart, suffixFinish, tag, endpointBound]
              Empty.elim ∘
            ![(#6 : Semiterm ℒₒᵣ Empty 15), #7, #8, #9, #10,
              #11, #12, #13, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactCertificateNodeSimpleEndpointGraphDef.val ↔
        CompactCertificateNodeSimpleEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag
            (compactCertificateNodeSimpleEndpointCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              suffixBoundary suffixCount suffixBoundarySize) := by
    have henv :
        (Semiterm.val
            ![suffixBoundarySize, suffixCount, suffixBoundary,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              suffixStart, suffixFinish, tag, endpointBound]
            Empty.elim ∘
          ![(#6 : Semiterm ℒₒᵣ Empty 15), #7, #8, #9, #10,
            #11, #12, #13, #5, #4, #3, #2, #1, #0]) =
          compactCertificateNodeSimpleEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              suffixStart suffixFinish tag
              (compactCertificateNodeSimpleEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                suffixBoundary suffixCount suffixBoundarySize) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactCertificateNodeSimpleEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag _
  simp [compactCertificateNodeSimpleEndpointBoundedGraphDef,
    CompactCertificateNodeSimpleEndpointBoundedGraph, hrow]

theorem compactCertificateNodeSimpleEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeSimpleEndpointBoundedGraphDef.val := by
  simp [compactCertificateNodeSimpleEndpointBoundedGraphDef]

theorem CompactCertificateNodeSimpleEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat}
    (hbounded : CompactCertificateNodeSimpleEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag endpointBound) :
    ∃ coordinates : CompactCertificateNodeSimpleEndpointCoordinates,
      CompactCertificateNodeSimpleEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _hinputBoundary,
      inputCount, _hinputCount,
      inputBoundarySize, _hinputBoundarySize,
      suffixBoundary, _hsuffixBoundary,
      suffixCount, _hsuffixCount,
      suffixBoundarySize, _hsuffixBoundarySize, hgraph⟩
  exact ⟨compactCertificateNodeSimpleEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    suffixBoundary suffixCount suffixBoundarySize, hgraph⟩

theorem CompactCertificateNodeSimpleEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat}
    {coordinates : CompactCertificateNodeSimpleEndpointCoordinates}
    (hgraph : CompactCertificateNodeSimpleEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag coordinates) :
    ∃ endpointBound,
      CompactCertificateNodeSimpleEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.suffixBoundary +
    coordinates.suffixCount + coordinates.suffixBoundarySize
  refine ⟨endpointBound, ?_⟩
  unfold CompactCertificateNodeSimpleEndpointBoundedGraph
  refine
    ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
      coordinates.inputBoundarySize, ?_, coordinates.suffixBoundary, ?_,
      coordinates.suffixCount, ?_, coordinates.suffixBoundarySize, ?_,
      hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactCertificateNodeSimpleEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound : Nat}
    (hbounded : CompactCertificateNodeSimpleEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag endpointBound) :
    ∃ input suffix : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = some (tag, ([], suffix)) := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactCertificateNodeSimpleEndpointBoundedGraph_of_success
    {input : List Nat} {tag : Nat} {axiomTokens suffix : List Nat}
    (hparser :
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = some (tag, (axiomTokens, suffix)))
    (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ suffixStart suffixFinish endpointBound,
      CompactCertificateNodeSimpleEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag endpointBound := by
  rcases exists_compactCertificateNodeSimpleEndpointGraph_of_success
      hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      suffixStart, suffixFinish, coordinates, hgraph⟩
  rcases CompactCertificateNodeSimpleEndpointGraph.exists_bounded hgraph with
    ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    suffixStart, suffixFinish, endpointBound, hbounded⟩

#print axioms compactCertificateNodeSimpleEndpointBoundedGraphDef_spec
#print axioms compactCertificateNodeSimpleEndpointBoundedGraphDef_sigmaZero
#print axioms CompactCertificateNodeSimpleEndpointBoundedGraph.exists_coordinates
#print axioms CompactCertificateNodeSimpleEndpointGraph.exists_bounded
#print axioms CompactCertificateNodeSimpleEndpointBoundedGraph.sound
#print axioms exists_compactCertificateNodeSimpleEndpointBoundedGraph_of_success

end FoundationCompactNumericListedDirectCertificateNodeSimpleBoundedFormula
