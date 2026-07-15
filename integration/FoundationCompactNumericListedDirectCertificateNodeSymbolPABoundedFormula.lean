import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint

/-!
# Bounded formula for symbol PA-axiom certificate nodes

The seventeen local coordinates for tags 3 and 4 are bounded by one public
endpoint value.  Function and relation symbol validity remain direct bounded
arithmetic predicates in the same formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedFormula

open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint

def compactCertificateNodeSymbolPAEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      axiomBoundary axiomCount axiomBoundarySize
      suffixBoundary suffixCount suffixBoundarySize
      paTag arity symbolCode : Nat) :
    CompactCertificateNodeSymbolPAEndpointCoordinates :=
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
    paTag := paTag
    arity := arity
    symbolCode := symbolCode }

def CompactCertificateNodeSymbolPAEndpointBoundedGraph
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
  ∃ arity, arity ≤ endpointBound ∧
  ∃ symbolCode, symbolCode ≤ endpointBound ∧
    CompactCertificateNodeSymbolPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag
        (compactCertificateNodeSymbolPAEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          tailStart tailFinish tailBoundary tailCount tailBoundarySize
          axiomBoundary axiomCount axiomBoundarySize
          suffixBoundary suffixCount suffixBoundarySize
          paTag arity symbolCode)

def compactCertificateNodeSymbolPAEndpointBoundedGraphDef :
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
    ∃ arity <⁺ endpointBound,
    ∃ symbolCode <⁺ endpointBound,
      !(compactCertificateNodeSymbolPAEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag
        inputBoundary inputCount inputBoundarySize
        tailStart tailFinish tailBoundary tailCount tailBoundarySize
        axiomBoundary axiomCount axiomBoundarySize
        suffixBoundary suffixCount suffixBoundarySize
        paTag arity symbolCode”

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeSymbolPAEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound : Nat) :
    compactCertificateNodeSymbolPAEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          axiomStart, axiomFinish, suffixStart, suffixFinish,
          certificateTag, endpointBound] ↔
      CompactCertificateNodeSymbolPAEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish certificateTag
          endpointBound := by
  have hrow
      (symbolCode arity paTag suffixBoundarySize suffixCount suffixBoundary
        axiomBoundarySize axiomCount axiomBoundary
        tailBoundarySize tailCount tailBoundary tailFinish tailStart
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![symbolCode, arity, paTag,
                suffixBoundarySize, suffixCount, suffixBoundary,
                axiomBoundarySize, axiomCount, axiomBoundary,
                tailBoundarySize, tailCount, tailBoundary, tailFinish,
                tailStart, inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                axiomStart, axiomFinish, suffixStart, suffixFinish,
                certificateTag, endpointBound]
              Empty.elim ∘
            ![(#17 : Semiterm ℒₒᵣ Empty 28), #18, #19, #20, #21,
              #22, #23, #24, #25, #26,
              #16, #15, #14, #13, #12, #11, #10, #9,
              #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactCertificateNodeSymbolPAEndpointGraphDef.val ↔
        CompactCertificateNodeSymbolPAEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish suffixStart suffixFinish certificateTag
            (compactCertificateNodeSymbolPAEndpointCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              tailStart tailFinish tailBoundary tailCount tailBoundarySize
              axiomBoundary axiomCount axiomBoundarySize
              suffixBoundary suffixCount suffixBoundarySize
              paTag arity symbolCode) := by
    have henv :
        (Semiterm.val
            ![symbolCode, arity, paTag,
              suffixBoundarySize, suffixCount, suffixBoundary,
              axiomBoundarySize, axiomCount, axiomBoundary,
              tailBoundarySize, tailCount, tailBoundary, tailFinish,
              tailStart, inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              axiomStart, axiomFinish, suffixStart, suffixFinish,
              certificateTag, endpointBound]
            Empty.elim ∘
          ![(#17 : Semiterm ℒₒᵣ Empty 28), #18, #19, #20, #21,
            #22, #23, #24, #25, #26,
            #16, #15, #14, #13, #12, #11, #10, #9,
            #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactCertificateNodeSymbolPAEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish suffixStart suffixFinish certificateTag
              (compactCertificateNodeSymbolPAEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                tailStart tailFinish tailBoundary tailCount tailBoundarySize
                axiomBoundary axiomCount axiomBoundarySize
                suffixBoundary suffixCount suffixBoundarySize
                paTag arity symbolCode) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactCertificateNodeSymbolPAEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag _
  simp [compactCertificateNodeSymbolPAEndpointBoundedGraphDef,
    CompactCertificateNodeSymbolPAEndpointBoundedGraph, hrow]

theorem compactCertificateNodeSymbolPAEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeSymbolPAEndpointBoundedGraphDef.val := by
  simp [compactCertificateNodeSymbolPAEndpointBoundedGraphDef]

theorem CompactCertificateNodeSymbolPAEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound : Nat}
    (hbounded : CompactCertificateNodeSymbolPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag
        endpointBound) :
    ∃ coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates,
      CompactCertificateNodeSymbolPAEndpointGraph
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
      paTag, _hpaTag, arity, _harity, symbolCode, _hsymbolCode, hgraph⟩
  exact ⟨compactCertificateNodeSymbolPAEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    tailStart tailFinish tailBoundary tailCount tailBoundarySize
    axiomBoundary axiomCount axiomBoundarySize
    suffixBoundary suffixCount suffixBoundarySize
    paTag arity symbolCode, hgraph⟩

theorem CompactCertificateNodeSymbolPAEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat}
    {coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates}
    (hgraph : CompactCertificateNodeSymbolPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish suffixStart suffixFinish certificateTag
        coordinates) :
    ∃ endpointBound,
      CompactCertificateNodeSymbolPAEndpointBoundedGraph
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
    coordinates.paTag + coordinates.arity + coordinates.symbolCode
  refine ⟨endpointBound, ?_⟩
  unfold CompactCertificateNodeSymbolPAEndpointBoundedGraph
  refine
    ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
      coordinates.inputBoundarySize, ?_, coordinates.tailStart, ?_,
      coordinates.tailFinish, ?_, coordinates.tailBoundary, ?_,
      coordinates.tailCount, ?_, coordinates.tailBoundarySize, ?_,
      coordinates.axiomBoundary, ?_, coordinates.axiomCount, ?_,
      coordinates.axiomBoundarySize, ?_, coordinates.suffixBoundary, ?_,
      coordinates.suffixCount, ?_, coordinates.suffixBoundarySize, ?_,
      coordinates.paTag, ?_, coordinates.arity, ?_,
      coordinates.symbolCode, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactCertificateNodeSymbolPAEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound : Nat}
    (hbounded : CompactCertificateNodeSymbolPAEndpointBoundedGraph
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

theorem exists_compactCertificateNodeSymbolPAEndpointBoundedGraph_of_results
    (paTag arity symbolCode : Nat) (suffix : List Nat)
    (hvalid : CompactSymbolPAAxiomTagValid paTag arity symbolCode) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish suffixStart suffixFinish endpointBound,
      CompactCertificateNodeSymbolPAEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish suffixStart suffixFinish 1 endpointBound := by
  rcases exists_compactCertificateNodeSymbolPAEndpointGraph_of_results
      paTag arity symbolCode suffix hvalid with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      axiomStart, axiomFinish, suffixStart, suffixFinish,
      coordinates, hgraph⟩
  rcases CompactCertificateNodeSymbolPAEndpointGraph.exists_bounded hgraph with
    ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    axiomStart, axiomFinish, suffixStart, suffixFinish,
    endpointBound, hbounded⟩

#print axioms compactCertificateNodeSymbolPAEndpointBoundedGraphDef_spec
#print axioms compactCertificateNodeSymbolPAEndpointBoundedGraphDef_sigmaZero
#print axioms CompactCertificateNodeSymbolPAEndpointBoundedGraph.exists_coordinates
#print axioms CompactCertificateNodeSymbolPAEndpointGraph.exists_bounded
#print axioms CompactCertificateNodeSymbolPAEndpointBoundedGraph.sound
#print axioms exists_compactCertificateNodeSymbolPAEndpointBoundedGraph_of_results

end FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedFormula
