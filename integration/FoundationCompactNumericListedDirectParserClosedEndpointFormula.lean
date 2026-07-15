import integration.FoundationCompactNumericListedDirectParserClosedEndpointCompleteness
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula

/-!
# Bounded arithmetic formula for exact closed-formula parser endpoints

The ordinary parser-state rows and every free-variable guard are combined in
one eighteen-column Delta-zero endpoint graph.  The same ten-coordinate bound
shape as the ordinary formula/term endpoint is retained.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedEndpointFormula

open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectParserClosedSuccessTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserClosedEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula

def compactParserClosedEndpointGraphDef : 𝚺₀.Semisentence 18 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity
      inputBoundary inputCount inputBoundarySize
      expectedBoundary expectedCount expectedBoundarySize
      stateBoundary stateCount tableWidth valueBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount expectedStart expectedCount expectedFinish
        expectedBoundary expectedBoundarySize ∧
    !(compactParserClosedSuccessTraceBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      inputBoundary inputCount expectedBoundary expectedCount
      1 binderArity 0 tableWidth valueBound”

def compactParserClosedEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity : Nat)
    (coordinates : CompactParserSyntaxExactEndpointCoordinates) :
    Fin 18 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    expectedStart, expectedFinish, binderArity,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize, coordinates.expectedBoundary,
    coordinates.expectedCount, coordinates.expectedBoundarySize,
    coordinates.stateBoundary, coordinates.stateCount,
    coordinates.tableWidth, coordinates.valueBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactParserClosedEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity : Nat)
    (coordinates : CompactParserSyntaxExactEndpointCoordinates) :
    compactParserClosedEndpointGraphDef.val.Evalb
        (compactParserClosedEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            expectedStart expectedFinish binderArity coordinates) ↔
      CompactParserClosedEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish binderArity coordinates := by
  let env := compactParserClosedEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity coordinates
  change compactParserClosedEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2, #3, #9, #4,
          #8, #10]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hexpectedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2, #5, #12, #6,
          #11, #13]) =
        ![tokenTable, width, tokenCount, expectedStart,
          coordinates.expectedCount, expectedFinish,
          coordinates.expectedBoundary, coordinates.expectedBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hclosedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 18), #1, #2, #14, #15,
          (‘(16 * (#9 + 1) * (#9 + 1) + 8)’ :
            Semiterm ℒₒᵣ Empty 18),
          #8, #9, #11, #12, ‘1’, #7, ‘0’, #16, #17]) =
        ![tokenTable, width, tokenCount,
          coordinates.stateBoundary, coordinates.stateCount,
          16 * (coordinates.inputCount + 1) *
            (coordinates.inputCount + 1) + 8,
          coordinates.inputBoundary, coordinates.inputCount,
          coordinates.expectedBoundary, coordinates.expectedCount,
          1, binderArity, 0, coordinates.tableWidth,
          coordinates.valueBound] := by
    funext index
    fin_cases index <;> simp [env,
      compactParserClosedEndpointEnvironment]
  simp [compactParserClosedEndpointGraphDef,
    CompactParserClosedEndpointGraph,
    hinputEnv, hexpectedEnv, hclosedEnv]

theorem compactParserClosedEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserClosedEndpointGraphDef.val := by
  simp [compactParserClosedEndpointGraphDef]

def CompactParserClosedEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ expectedBoundary, expectedBoundary ≤ endpointBound ∧
  ∃ expectedCount, expectedCount ≤ endpointBound ∧
  ∃ expectedBoundarySize, expectedBoundarySize ≤ endpointBound ∧
  ∃ stateBoundary, stateBoundary ≤ endpointBound ∧
  ∃ stateCount, stateCount ≤ endpointBound ∧
  ∃ tableWidth, tableWidth ≤ endpointBound ∧
  ∃ valueBound, valueBound ≤ endpointBound ∧
    CompactParserClosedEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish binderArity
        (compactParserSyntaxExactEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          expectedBoundary expectedCount expectedBoundarySize
          stateBoundary stateCount tableWidth valueBound)

def compactParserClosedEndpointBoundedGraphDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ expectedBoundary <⁺ endpointBound,
    ∃ expectedCount <⁺ endpointBound,
    ∃ expectedBoundarySize <⁺ endpointBound,
    ∃ stateBoundary <⁺ endpointBound,
    ∃ stateCount <⁺ endpointBound,
    ∃ tableWidth <⁺ endpointBound,
    ∃ valueBound <⁺ endpointBound,
      !(compactParserClosedEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish binderArity
        inputBoundary inputCount inputBoundarySize
        expectedBoundary expectedCount expectedBoundarySize
        stateBoundary stateCount tableWidth valueBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactParserClosedEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity endpointBound : Nat) :
    compactParserClosedEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          expectedStart, expectedFinish, binderArity, endpointBound] ↔
      CompactParserClosedEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish binderArity endpointBound := by
  have hrow
      (valueBound tableWidth stateCount stateBoundary
        expectedBoundarySize expectedCount expectedBoundary
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![valueBound, tableWidth, stateCount, stateBoundary,
                expectedBoundarySize, expectedCount, expectedBoundary,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                expectedStart, expectedFinish, binderArity, endpointBound]
              Empty.elim ∘
            ![(#10 : Semiterm ℒₒᵣ Empty 19), #11, #12, #13, #14,
              #15, #16, #17,
              #9, #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactParserClosedEndpointGraphDef.val ↔
        CompactParserClosedEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            expectedStart expectedFinish binderArity
            (compactParserSyntaxExactEndpointCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              expectedBoundary expectedCount expectedBoundarySize
              stateBoundary stateCount tableWidth valueBound) := by
    have henv :
        (Semiterm.val
            ![valueBound, tableWidth, stateCount, stateBoundary,
              expectedBoundarySize, expectedCount, expectedBoundary,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              expectedStart, expectedFinish, binderArity, endpointBound]
            Empty.elim ∘
          ![(#10 : Semiterm ℒₒᵣ Empty 19), #11, #12, #13, #14,
            #15, #16, #17,
            #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactParserClosedEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              expectedStart expectedFinish binderArity
              (compactParserSyntaxExactEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                expectedBoundary expectedCount expectedBoundarySize
                stateBoundary stateCount tableWidth valueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactParserClosedEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish binderArity _
  simp [compactParserClosedEndpointBoundedGraphDef,
    CompactParserClosedEndpointBoundedGraph, hrow]

theorem compactParserClosedEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserClosedEndpointBoundedGraphDef.val := by
  simp [compactParserClosedEndpointBoundedGraphDef]

theorem CompactParserClosedEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity endpointBound : Nat}
    (hbounded : CompactParserClosedEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish binderArity endpointBound) :
    ∃ coordinates : CompactParserSyntaxExactEndpointCoordinates,
      CompactParserClosedEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish binderArity coordinates := by
  unfold CompactParserClosedEndpointBoundedGraph at hbounded
  rcases hbounded with
    ⟨inputBoundary, _hinputBoundary,
      inputCount, _hinputCount,
      inputBoundarySize, _hinputBoundarySize,
      expectedBoundary, _hexpectedBoundary,
      expectedCount, _hexpectedCount,
      expectedBoundarySize, _hexpectedBoundarySize,
      stateBoundary, _hstateBoundary,
      stateCount, _hstateCount,
      tableWidth, _htableWidth,
      valueBound, _hvalueBound, hgraph⟩
  exact ⟨compactParserSyntaxExactEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    expectedBoundary expectedCount expectedBoundarySize
    stateBoundary stateCount tableWidth valueBound, hgraph⟩

theorem CompactParserClosedEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity : Nat}
    {coordinates : CompactParserSyntaxExactEndpointCoordinates}
    (hgraph : CompactParserClosedEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish binderArity coordinates) :
    ∃ endpointBound,
      CompactParserClosedEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish binderArity endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.expectedBoundary +
    coordinates.expectedCount + coordinates.expectedBoundarySize +
    coordinates.stateBoundary + coordinates.stateCount +
    coordinates.tableWidth + coordinates.valueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactParserClosedEndpointBoundedGraph
  refine
    ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
      coordinates.inputBoundarySize, ?_, coordinates.expectedBoundary, ?_,
      coordinates.expectedCount, ?_, coordinates.expectedBoundarySize, ?_,
      coordinates.stateBoundary, ?_, coordinates.stateCount, ?_,
      coordinates.tableWidth, ?_, coordinates.valueBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactParserClosedEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity endpointBound : Nat}
    (hbounded : CompactParserClosedEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish binderArity endpointBound) :
    ∃ input expected : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount expectedStart expectedFinish expected ∧
      FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParser
        binderArity input = some expected := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactParserClosedEndpointBoundedGraph_of_success
    {binderArity : Nat} {input expected : List Nat}
    (hparser :
      FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParser
        binderArity input = some expected) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ expectedStart expectedFinish endpointBound,
      CompactParserClosedEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish binderArity endpointBound := by
  rcases exists_compactParserClosedEndpointGraph_of_success hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      expectedStart, expectedFinish, coordinates, hgraph⟩
  rcases CompactParserClosedEndpointGraph.exists_bounded hgraph with
    ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    expectedStart, expectedFinish, endpointBound, hbounded⟩

#print axioms compactParserClosedEndpointGraphDef_spec
#print axioms compactParserClosedEndpointGraphDef_sigmaZero
#print axioms compactParserClosedEndpointBoundedGraphDef_spec
#print axioms compactParserClosedEndpointBoundedGraphDef_sigmaZero
#print axioms CompactParserClosedEndpointGraph.exists_bounded
#print axioms CompactParserClosedEndpointBoundedGraph.sound
#print axioms exists_compactParserClosedEndpointBoundedGraph_of_success

end FoundationCompactNumericListedDirectParserClosedEndpointFormula
