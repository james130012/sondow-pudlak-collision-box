import integration.FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint

/-!
# Bounded formula for fixed one-token PA-axiom certificate nodes

All fifteen local coordinates of the fixed-tag endpoint are existentially
bounded by one public value.  The formula therefore exposes only numeric slice
endpoints and the structural certificate tag.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedFormula

open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint

def compactCertificateNodeFixedPAEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      axiomBoundary axiomCount axiomBoundarySize
      suffixBoundary suffixCount suffixBoundarySize paTag : Nat) :
    CompactCertificateNodeFixedPAEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    tailStart := tailStart
    tailFinish := tailFinish
    tailBoundary := tailBoundary
    tailCount := tailCount
    tailBoundarySize := tailBoundarySize
    axiomBoundary := axiomBoundary
    axiomCount := axiomCount
    axiomBoundarySize := axiomBoundarySize
    suffixBoundary := suffixBoundary
    suffixCount := suffixCount
    suffixBoundarySize := suffixBoundarySize
    paTag := paTag }

def CompactCertificateNodeFixedPAEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ tailStart, tailStart ≤ endpointBound ∧
  ∃ tailFinish, tailFinish ≤ endpointBound ∧
  ∃ tailBoundary, tailBoundary ≤ endpointBound ∧
  ∃ tailCount, tailCount ≤ endpointBound ∧
  ∃ tailBoundarySize, tailBoundarySize ≤ endpointBound ∧
  ∃ axiomBoundary, axiomBoundary ≤ endpointBound ∧
  ∃ axiomCount, axiomCount ≤ endpointBound ∧
  ∃ axiomBoundarySize, axiomBoundarySize ≤ endpointBound ∧
  ∃ suffixBoundary, suffixBoundary ≤ endpointBound ∧
  ∃ suffixCount, suffixCount ≤ endpointBound ∧
  ∃ suffixBoundarySize, suffixBoundarySize ≤ endpointBound ∧
  ∃ paTag, paTag ≤ endpointBound ∧
    CompactCertificateNodeFixedPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag
        (compactCertificateNodeFixedPAEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          tailStart tailFinish tailBoundary tailCount tailBoundarySize
          axiomBoundary axiomCount axiomBoundarySize
          suffixBoundary suffixCount suffixBoundarySize paTag)

def compactCertificateNodeFixedPAEndpointBoundedGraphDef :
    𝚺₀.Semisentence 11 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ tailStart <⁺ endpointBound,
    ∃ tailFinish <⁺ endpointBound,
    ∃ tailBoundary <⁺ endpointBound,
    ∃ tailCount <⁺ endpointBound,
    ∃ tailBoundarySize <⁺ endpointBound,
    ∃ axiomBoundary <⁺ endpointBound,
    ∃ axiomCount <⁺ endpointBound,
    ∃ axiomBoundarySize <⁺ endpointBound,
    ∃ suffixBoundary <⁺ endpointBound,
    ∃ suffixCount <⁺ endpointBound,
    ∃ suffixBoundarySize <⁺ endpointBound,
    ∃ paTag <⁺ endpointBound,
      !(compactCertificateNodeFixedPAEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag
        inputBoundary inputCount inputBoundarySize
        tailStart tailFinish tailBoundary tailCount tailBoundarySize
        axiomBoundary axiomCount axiomBoundarySize
        suffixBoundary suffixCount suffixBoundarySize paTag”

set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeFixedPAEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound : Nat) :
    compactCertificateNodeFixedPAEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          axiomStart, axiomFinish, suffixStart, suffixFinish,
          certificateTag, endpointBound] ↔
      CompactCertificateNodeFixedPAEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish certificateTag
          endpointBound := by
  have hrow
      (paTag suffixBoundarySize suffixCount suffixBoundary
        axiomBoundarySize axiomCount axiomBoundary
        tailBoundarySize tailCount tailBoundary tailFinish tailStart
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![paTag, suffixBoundarySize, suffixCount, suffixBoundary,
                axiomBoundarySize, axiomCount, axiomBoundary,
                tailBoundarySize, tailCount, tailBoundary, tailFinish,
                tailStart, inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                axiomStart, axiomFinish, suffixStart, suffixFinish,
                certificateTag, endpointBound]
              Empty.elim ∘
            ![(#15 : Semiterm ℒₒᵣ Empty 26), #16, #17, #18, #19,
              #20, #21, #22, #23, #24,
              #14, #13, #12, #11, #10, #9, #8, #7,
              #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactCertificateNodeFixedPAEndpointGraphDef.val ↔
        CompactCertificateNodeFixedPAEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish suffixStart suffixFinish certificateTag
            (compactCertificateNodeFixedPAEndpointCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              tailStart tailFinish tailBoundary tailCount tailBoundarySize
              axiomBoundary axiomCount axiomBoundarySize
              suffixBoundary suffixCount suffixBoundarySize paTag) := by
    have henv :
        (Semiterm.val
            ![paTag, suffixBoundarySize, suffixCount, suffixBoundary,
              axiomBoundarySize, axiomCount, axiomBoundary,
              tailBoundarySize, tailCount, tailBoundary, tailFinish,
              tailStart, inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              axiomStart, axiomFinish, suffixStart, suffixFinish,
              certificateTag, endpointBound]
            Empty.elim ∘
          ![(#15 : Semiterm ℒₒᵣ Empty 26), #16, #17, #18, #19,
            #20, #21, #22, #23, #24,
            #14, #13, #12, #11, #10, #9, #8, #7,
            #6, #5, #4, #3, #2, #1, #0]) =
          compactCertificateNodeFixedPAEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish suffixStart suffixFinish certificateTag
              (compactCertificateNodeFixedPAEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                tailStart tailFinish tailBoundary tailCount tailBoundarySize
                axiomBoundary axiomCount axiomBoundarySize
                suffixBoundary suffixCount suffixBoundarySize paTag) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactCertificateNodeFixedPAEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag _
  simp [compactCertificateNodeFixedPAEndpointBoundedGraphDef,
    CompactCertificateNodeFixedPAEndpointBoundedGraph, hrow]

theorem compactCertificateNodeFixedPAEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeFixedPAEndpointBoundedGraphDef.val := by
  simp [compactCertificateNodeFixedPAEndpointBoundedGraphDef]

theorem CompactCertificateNodeFixedPAEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound : Nat}
    (hbounded : CompactCertificateNodeFixedPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag
        endpointBound) :
    ∃ coordinates : CompactCertificateNodeFixedPAEndpointCoordinates,
      CompactCertificateNodeFixedPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish certificateTag
          coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _hinputBoundary,
      inputCount, _hinputCount,
      inputBoundarySize, _hinputBoundarySize,
      tailStart, _htailStart,
      tailFinish, _htailFinish,
      tailBoundary, _htailBoundary,
      tailCount, _htailCount,
      tailBoundarySize, _htailBoundarySize,
      axiomBoundary, _haxiomBoundary,
      axiomCount, _haxiomCount,
      axiomBoundarySize, _haxiomBoundarySize,
      suffixBoundary, _hsuffixBoundary,
      suffixCount, _hsuffixCount,
      suffixBoundarySize, _hsuffixBoundarySize,
      paTag, _hpaTag, hgraph⟩
  exact ⟨compactCertificateNodeFixedPAEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    tailStart tailFinish tailBoundary tailCount tailBoundarySize
    axiomBoundary axiomCount axiomBoundarySize
    suffixBoundary suffixCount suffixBoundarySize paTag, hgraph⟩

theorem CompactCertificateNodeFixedPAEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeFixedPAEndpointCoordinates}
    (hgraph : CompactCertificateNodeFixedPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag
        coordinates) :
    ∃ endpointBound,
      CompactCertificateNodeFixedPAEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish certificateTag
          endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.tailStart +
    coordinates.tailFinish + coordinates.tailBoundary +
    coordinates.tailCount + coordinates.tailBoundarySize +
    coordinates.axiomBoundary + coordinates.axiomCount +
    coordinates.axiomBoundarySize + coordinates.suffixBoundary +
    coordinates.suffixCount + coordinates.suffixBoundarySize +
    coordinates.paTag
  refine ⟨endpointBound, ?_⟩
  unfold CompactCertificateNodeFixedPAEndpointBoundedGraph
  refine
    ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
      coordinates.inputBoundarySize, ?_, coordinates.tailStart, ?_,
      coordinates.tailFinish, ?_, coordinates.tailBoundary, ?_,
      coordinates.tailCount, ?_, coordinates.tailBoundarySize, ?_,
      coordinates.axiomBoundary, ?_, coordinates.axiomCount, ?_,
      coordinates.axiomBoundarySize, ?_, coordinates.suffixBoundary, ?_,
      coordinates.suffixCount, ?_, coordinates.suffixBoundarySize, ?_,
      coordinates.paTag, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactCertificateNodeFixedPAEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound : Nat}
    (hbounded : CompactCertificateNodeFixedPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag
        endpointBound) :
    ∃ input axiomTokens suffix : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount axiomStart axiomFinish axiomTokens ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = some (certificateTag, (axiomTokens, suffix)) := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactCertificateNodeFixedPAEndpointBoundedGraph_of_results
    (paTag : Nat) (suffix : List Nat)
    (hfixed : CompactFixedPAAxiomTag paTag) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish suffixStart suffixFinish endpointBound,
      CompactCertificateNodeFixedPAEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish 1 endpointBound := by
  rcases exists_compactCertificateNodeFixedPAEndpointGraph_of_results
      paTag suffix hfixed with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, suffixStart, suffixFinish,
      coordinates, hgraph⟩
  rcases CompactCertificateNodeFixedPAEndpointGraph.exists_bounded hgraph with
    ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, suffixStart, suffixFinish,
    endpointBound, hbounded⟩

#print axioms compactCertificateNodeFixedPAEndpointBoundedGraphDef_spec
#print axioms compactCertificateNodeFixedPAEndpointBoundedGraphDef_sigmaZero
#print axioms CompactCertificateNodeFixedPAEndpointBoundedGraph.exists_coordinates
#print axioms CompactCertificateNodeFixedPAEndpointGraph.exists_bounded
#print axioms CompactCertificateNodeFixedPAEndpointBoundedGraph.sound
#print axioms exists_compactCertificateNodeFixedPAEndpointBoundedGraph_of_results

end FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedFormula
