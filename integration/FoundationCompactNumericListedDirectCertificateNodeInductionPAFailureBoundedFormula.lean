import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureEndpoint

/-!
# Bounded formula for failed induction PA certificates

All seventeen local endpoint coordinates are quantified below one public bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureBoundedFormula

open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureEndpoint

def compactCertificateNodeInductionPAFailureEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      formulaStart formulaFinish
      parserInputBoundary parserInputCount parserInputBoundarySize
      parserStateBoundary parserStateCount parserTableWidth parserValueBound : Nat) :
    CompactCertificateNodeInductionPAFailureEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    tailStart := tailStart
    tailFinish := tailFinish
    tailBoundary := tailBoundary
    tailCount := tailCount
    tailBoundarySize := tailBoundarySize
    formulaStart := formulaStart
    formulaFinish := formulaFinish
    parser :=
      { inputBoundary := parserInputBoundary
        inputCount := parserInputCount
        inputBoundarySize := parserInputBoundarySize
        stateBoundary := parserStateBoundary
        stateCount := parserStateCount
        tableWidth := parserTableWidth
        valueBound := parserValueBound } }

def CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ tailStart, tailStart ≤ endpointBound ∧
  ∃ tailFinish, tailFinish ≤ endpointBound ∧
  ∃ tailBoundary, tailBoundary ≤ endpointBound ∧
  ∃ tailCount, tailCount ≤ endpointBound ∧
  ∃ tailBoundarySize, tailBoundarySize ≤ endpointBound ∧
  ∃ formulaStart, formulaStart ≤ endpointBound ∧
  ∃ formulaFinish, formulaFinish ≤ endpointBound ∧
  ∃ parserInputBoundary, parserInputBoundary ≤ endpointBound ∧
  ∃ parserInputCount, parserInputCount ≤ endpointBound ∧
  ∃ parserInputBoundarySize, parserInputBoundarySize ≤ endpointBound ∧
  ∃ parserStateBoundary, parserStateBoundary ≤ endpointBound ∧
  ∃ parserStateCount, parserStateCount ≤ endpointBound ∧
  ∃ parserTableWidth, parserTableWidth ≤ endpointBound ∧
  ∃ parserValueBound, parserValueBound ≤ endpointBound ∧
    CompactCertificateNodeInductionPAFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        (compactCertificateNodeInductionPAFailureEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          tailStart tailFinish tailBoundary tailCount tailBoundarySize
          formulaStart formulaFinish
          parserInputBoundary parserInputCount parserInputBoundarySize
          parserStateBoundary parserStateCount parserTableWidth parserValueBound)

def compactCertificateNodeInductionPAFailureEndpointBoundedGraphDef :
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
    ∃ formulaStart <⁺ endpointBound,
    ∃ formulaFinish <⁺ endpointBound,
    ∃ parserInputBoundary <⁺ endpointBound,
    ∃ parserInputCount <⁺ endpointBound,
    ∃ parserInputBoundarySize <⁺ endpointBound,
    ∃ parserStateBoundary <⁺ endpointBound,
    ∃ parserStateCount <⁺ endpointBound,
    ∃ parserTableWidth <⁺ endpointBound,
    ∃ parserValueBound <⁺ endpointBound,
      !(compactCertificateNodeInductionPAFailureEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        inputBoundary inputCount inputBoundarySize
        tailStart tailFinish tailBoundary tailCount tailBoundarySize
        formulaStart formulaFinish
        parserInputBoundary parserInputCount parserInputBoundarySize
        parserStateBoundary parserStateCount parserTableWidth parserValueBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeInductionPAFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    compactCertificateNodeInductionPAFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish, endpointBound] ↔
      CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  have hrow
      (parserValueBound parserTableWidth parserStateCount parserStateBoundary
        parserInputBoundarySize parserInputCount parserInputBoundary
        formulaFinish formulaStart
        tailBoundarySize tailCount tailBoundary tailFinish tailStart
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![parserValueBound, parserTableWidth, parserStateCount,
                parserStateBoundary, parserInputBoundarySize,
                parserInputCount, parserInputBoundary,
                formulaFinish, formulaStart,
                tailBoundarySize, tailCount, tailBoundary,
                tailFinish, tailStart,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#17 : Semiterm ℒₒᵣ Empty 23), #18, #19, #20, #21,
              #16, #15, #14, #13, #12, #11, #10, #9, #8, #7,
              #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactCertificateNodeInductionPAFailureEndpointGraphDef.val ↔
      CompactCertificateNodeInductionPAFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          (compactCertificateNodeInductionPAFailureEndpointCoordinatesOfValues
            inputBoundary inputCount inputBoundarySize
            tailStart tailFinish tailBoundary tailCount tailBoundarySize
            formulaStart formulaFinish
            parserInputBoundary parserInputCount parserInputBoundarySize
            parserStateBoundary parserStateCount parserTableWidth
            parserValueBound) := by
    have henv :
        (Semiterm.val
            ![parserValueBound, parserTableWidth, parserStateCount,
              parserStateBoundary, parserInputBoundarySize,
              parserInputCount, parserInputBoundary,
              formulaFinish, formulaStart,
              tailBoundarySize, tailCount, tailBoundary,
              tailFinish, tailStart,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              endpointBound]
            Empty.elim ∘
          ![(#17 : Semiterm ℒₒᵣ Empty 23), #18, #19, #20, #21,
            #16, #15, #14, #13, #12, #11, #10, #9, #8, #7,
            #6, #5, #4, #3, #2, #1, #0]) =
          compactCertificateNodeInductionPAFailureEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              (compactCertificateNodeInductionPAFailureEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                tailStart tailFinish tailBoundary tailCount tailBoundarySize
                formulaStart formulaFinish
                parserInputBoundary parserInputCount parserInputBoundarySize
                parserStateBoundary parserStateCount parserTableWidth
                parserValueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactCertificateNodeInductionPAFailureEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish _
  simp [compactCertificateNodeInductionPAFailureEndpointBoundedGraphDef,
    CompactCertificateNodeInductionPAFailureEndpointBoundedGraph, hrow]

theorem compactCertificateNodeInductionPAFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeInductionPAFailureEndpointBoundedGraphDef.val := by
  simp [compactCertificateNodeInductionPAFailureEndpointBoundedGraphDef]

theorem CompactCertificateNodeInductionPAFailureEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hbounded : CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ coordinates : CompactCertificateNodeInductionPAFailureEndpointCoordinates,
      CompactCertificateNodeInductionPAFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      tailStart, _, tailFinish, _, tailBoundary, _, tailCount, _,
      tailBoundarySize, _, formulaStart, _, formulaFinish, _,
      parserInputBoundary, _, parserInputCount, _, parserInputBoundarySize, _,
      parserStateBoundary, _, parserStateCount, _, parserTableWidth, _,
      parserValueBound, _, hgraph⟩
  exact ⟨compactCertificateNodeInductionPAFailureEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    tailStart tailFinish tailBoundary tailCount tailBoundarySize
    formulaStart formulaFinish
    parserInputBoundary parserInputCount parserInputBoundarySize
    parserStateBoundary parserStateCount parserTableWidth parserValueBound, hgraph⟩

theorem CompactCertificateNodeInductionPAFailureEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactCertificateNodeInductionPAFailureEndpointCoordinates}
    (hgraph : CompactCertificateNodeInductionPAFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    ∃ endpointBound,
      CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.tailStart +
    coordinates.tailFinish + coordinates.tailBoundary +
    coordinates.tailCount + coordinates.tailBoundarySize +
    coordinates.formulaStart + coordinates.formulaFinish +
    coordinates.parser.inputBoundary + coordinates.parser.inputCount +
    coordinates.parser.inputBoundarySize + coordinates.parser.stateBoundary +
    coordinates.parser.stateCount + coordinates.parser.tableWidth +
    coordinates.parser.valueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.tailStart, ?_,
    coordinates.tailFinish, ?_, coordinates.tailBoundary, ?_,
    coordinates.tailCount, ?_, coordinates.tailBoundarySize, ?_,
    coordinates.formulaStart, ?_, coordinates.formulaFinish, ?_,
    coordinates.parser.inputBoundary, ?_, coordinates.parser.inputCount, ?_,
    coordinates.parser.inputBoundarySize, ?_,
    coordinates.parser.stateBoundary, ?_, coordinates.parser.stateCount, ?_,
    coordinates.parser.tableWidth, ?_, coordinates.parser.valueBound, ?_,
    hgraph⟩ <;> dsimp only [endpointBound] <;> omega

theorem CompactCertificateNodeInductionPAFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hbounded : CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ input : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactCertificateNodeInductionPAFailureEndpointBoundedGraph
    (formulaInput : List Nat)
    (hformula :
      FoundationCompactSyntaxTokenMachine.compactFormulaTokenParser
        1 formulaInput = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureEndpoint.exists_compactCertificateNodeInductionPAFailureEndpointGraph
        formulaInput hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, hgraph⟩
  rcases CompactCertificateNodeInductionPAFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hbounded⟩

theorem exists_compactCertificateNodeInductionPAFailureEndpointBoundedGraph_with_inputLayout
    (formulaInput : List Nat)
    (hformula :
      FoundationCompactSyntaxTokenMachine.compactFormulaTokenParser
        1 formulaInput = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: 22 :: formulaInput) ∧
        CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureEndpoint.exists_compactCertificateNodeInductionPAFailureEndpointGraph_with_inputLayout
        formulaInput hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, hinputLayout, hgraph⟩
  rcases CompactCertificateNodeInductionPAFailureEndpointGraph.exists_bounded
      hgraph with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, hbounded⟩

#print axioms compactCertificateNodeInductionPAFailureEndpointBoundedGraphDef_spec
#print axioms compactCertificateNodeInductionPAFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactCertificateNodeInductionPAFailureEndpointGraph.exists_bounded
#print axioms CompactCertificateNodeInductionPAFailureEndpointBoundedGraph.sound
#print axioms exists_compactCertificateNodeInductionPAFailureEndpointBoundedGraph

end FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureBoundedFormula
