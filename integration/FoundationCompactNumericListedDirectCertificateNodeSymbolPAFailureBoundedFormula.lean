import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureEndpoint

/-!
# Bounded formula for malformed symbol PA certificates

The eleven local endpoint coordinates are quantified below one public bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureBoundedFormula

open FoundationCompactArithmeticSymbolCode
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureEndpoint

def compactCertificateNodeSymbolPAFailureEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      paTag arity symbolCode : Nat) :
    CompactCertificateNodeSymbolPAFailureEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    tailStart := tailStart
    tailFinish := tailFinish
    tailBoundary := tailBoundary
    tailCount := tailCount
    tailBoundarySize := tailBoundarySize
    paTag := paTag
    arity := arity
    symbolCode := symbolCode }

def CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ tailStart, tailStart ≤ endpointBound ∧
  ∃ tailFinish, tailFinish ≤ endpointBound ∧
  ∃ tailBoundary, tailBoundary ≤ endpointBound ∧
  ∃ tailCount, tailCount ≤ endpointBound ∧
  ∃ tailBoundarySize, tailBoundarySize ≤ endpointBound ∧
  ∃ paTag, paTag ≤ endpointBound ∧
  ∃ arity, arity ≤ endpointBound ∧
  ∃ symbolCode, symbolCode ≤ endpointBound ∧
    CompactCertificateNodeSymbolPAFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        (compactCertificateNodeSymbolPAFailureEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          tailStart tailFinish tailBoundary tailCount tailBoundarySize
          paTag arity symbolCode)

def compactCertificateNodeSymbolPAFailureEndpointBoundedGraphDef :
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
    ∃ paTag <⁺ endpointBound,
    ∃ arity <⁺ endpointBound,
    ∃ symbolCode <⁺ endpointBound,
      !(compactCertificateNodeSymbolPAFailureEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        inputBoundary inputCount inputBoundarySize
        tailStart tailFinish tailBoundary tailCount tailBoundarySize
        paTag arity symbolCode”

set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeSymbolPAFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    compactCertificateNodeSymbolPAFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish, endpointBound] ↔
      CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  have hrow
      (symbolCode arity paTag tailBoundarySize tailCount tailBoundary
        tailFinish tailStart inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![symbolCode, arity, paTag, tailBoundarySize, tailCount,
                tailBoundary, tailFinish, tailStart,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#11 : Semiterm ℒₒᵣ Empty 17), #12, #13, #14, #15,
              #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactCertificateNodeSymbolPAFailureEndpointGraphDef.val ↔
      CompactCertificateNodeSymbolPAFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          (compactCertificateNodeSymbolPAFailureEndpointCoordinatesOfValues
            inputBoundary inputCount inputBoundarySize
            tailStart tailFinish tailBoundary tailCount tailBoundarySize
            paTag arity symbolCode) := by
    have henv :
        (Semiterm.val
            ![symbolCode, arity, paTag, tailBoundarySize, tailCount,
              tailBoundary, tailFinish, tailStart,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              endpointBound]
            Empty.elim ∘
          ![(#11 : Semiterm ℒₒᵣ Empty 17), #12, #13, #14, #15,
            #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactCertificateNodeSymbolPAFailureEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              (compactCertificateNodeSymbolPAFailureEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                tailStart tailFinish tailBoundary tailCount tailBoundarySize
                paTag arity symbolCode) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactCertificateNodeSymbolPAFailureEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish _
  simp [compactCertificateNodeSymbolPAFailureEndpointBoundedGraphDef,
    CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph, hrow]

theorem compactCertificateNodeSymbolPAFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeSymbolPAFailureEndpointBoundedGraphDef.val := by
  simp [compactCertificateNodeSymbolPAFailureEndpointBoundedGraphDef]

theorem CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hbounded : CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ coordinates : CompactCertificateNodeSymbolPAFailureEndpointCoordinates,
      CompactCertificateNodeSymbolPAFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      tailStart, _, tailFinish, _, tailBoundary, _, tailCount, _,
      tailBoundarySize, _, paTag, _, arity, _, symbolCode, _, hgraph⟩
  exact ⟨compactCertificateNodeSymbolPAFailureEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    tailStart tailFinish tailBoundary tailCount tailBoundarySize
    paTag arity symbolCode, hgraph⟩

theorem CompactCertificateNodeSymbolPAFailureEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactCertificateNodeSymbolPAFailureEndpointCoordinates}
    (hgraph : CompactCertificateNodeSymbolPAFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    ∃ endpointBound,
      CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.tailStart +
    coordinates.tailFinish + coordinates.tailBoundary +
    coordinates.tailCount + coordinates.tailBoundarySize +
    coordinates.paTag + coordinates.arity + coordinates.symbolCode
  refine ⟨endpointBound, ?_⟩
  unfold CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.tailStart, ?_,
    coordinates.tailFinish, ?_, coordinates.tailBoundary, ?_,
    coordinates.tailCount, ?_, coordinates.tailBoundarySize, ?_,
    coordinates.paTag, ?_, coordinates.arity, ?_,
    coordinates.symbolCode, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hbounded : CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ input : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactCertificateNodeSymbolPAFailureEndpointBoundedGraph
    (paTag : Nat) (body : List Nat)
    (htag : paTag = 3 ∨ paTag = 4)
    (hfailure :
      body.length < 2 ∨
        ((paTag = 3 ∧
            ¬ ArithmeticFuncCodeValid
              (compactTokenAt 0 body) (compactTokenAt 1 body)) ∨
          (paTag = 4 ∧
            ¬ ArithmeticRelCodeValid
              (compactTokenAt 0 body) (compactTokenAt 1 body)))) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureEndpoint.exists_compactCertificateNodeSymbolPAFailureEndpointGraph
        paTag body htag hfailure with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, hgraph⟩
  rcases CompactCertificateNodeSymbolPAFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hbounded⟩

theorem exists_compactCertificateNodeSymbolPAFailureEndpointBoundedGraph_with_inputLayout
    (paTag : Nat) (body : List Nat)
    (htag : paTag = 3 ∨ paTag = 4)
    (hfailure :
      body.length < 2 ∨
        ((paTag = 3 ∧
            ¬ ArithmeticFuncCodeValid
              (compactTokenAt 0 body) (compactTokenAt 1 body)) ∨
          (paTag = 4 ∧
            ¬ ArithmeticRelCodeValid
              (compactTokenAt 0 body) (compactTokenAt 1 body)))) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: paTag :: body) ∧
        CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureEndpoint.exists_compactCertificateNodeSymbolPAFailureEndpointGraph_with_inputLayout
        paTag body htag hfailure with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, hinputLayout, hgraph⟩
  rcases CompactCertificateNodeSymbolPAFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, hbounded⟩

#print axioms compactCertificateNodeSymbolPAFailureEndpointBoundedGraphDef_spec
#print axioms compactCertificateNodeSymbolPAFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactCertificateNodeSymbolPAFailureEndpointGraph.exists_bounded
#print axioms CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph.sound
#print axioms exists_compactCertificateNodeSymbolPAFailureEndpointBoundedGraph

end FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureBoundedFormula
