import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness

/-!
# Bounded arithmetic formula for exact formula and term parser endpoints

The two public list slices and the complete ordinary parser trace are exposed
by one twenty-column Delta-zero graph.  A ten-witness wrapper supplies the
single public bound needed by larger root-parser formulas.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula

open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness

def compactParserSyntaxExactEndpointGraphDef : 𝚺₀.Semisentence 20 :=
  .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount
      inputBoundary inputCount inputBoundarySize
      expectedBoundary expectedCount expectedBoundarySize
      stateBoundary stateCount tableWidth valueBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount expectedStart expectedCount expectedFinish
        expectedBoundary expectedBoundarySize ∧
    !(compactParserSyntaxExactBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound”

def compactParserSyntaxExactEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount :
      Nat)
    (coordinates : CompactParserSyntaxExactEndpointCoordinates) :
    Fin 20 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    expectedStart, expectedFinish, taskKind, taskBinderArity, taskRepeatCount,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize, coordinates.expectedBoundary,
    coordinates.expectedCount, coordinates.expectedBoundarySize,
    coordinates.stateBoundary, coordinates.stateCount,
    coordinates.tableWidth, coordinates.valueBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactParserSyntaxExactEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount :
      Nat)
    (coordinates : CompactParserSyntaxExactEndpointCoordinates) :
    compactParserSyntaxExactEndpointGraphDef.val.Evalb
        (compactParserSyntaxExactEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            expectedStart expectedFinish taskKind taskBinderArity
            taskRepeatCount coordinates) ↔
      CompactParserSyntaxExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish taskKind taskBinderArity
          taskRepeatCount coordinates := by
  let env := compactParserSyntaxExactEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity
      taskRepeatCount coordinates
  change compactParserSyntaxExactEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2, #3, #11, #4,
          #10, #12]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hexpectedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2, #5, #14, #6,
          #13, #15]) =
        ![tokenTable, width, tokenCount, expectedStart,
          coordinates.expectedCount, expectedFinish,
          coordinates.expectedBoundary, coordinates.expectedBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hexactEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2, #16, #17,
          #10, #11, #13, #14, #7, #8, #9, #18, #19]) =
        ![tokenTable, width, tokenCount,
          coordinates.stateBoundary, coordinates.stateCount,
          coordinates.inputBoundary, coordinates.inputCount,
          coordinates.expectedBoundary, coordinates.expectedCount,
          taskKind, taskBinderArity, taskRepeatCount,
          coordinates.tableWidth, coordinates.valueBound] := by
    funext index
    fin_cases index <;> rfl
  simp [compactParserSyntaxExactEndpointGraphDef,
    CompactParserSyntaxExactEndpointGraph,
    hinputEnv, hexpectedEnv, hexactEnv]

theorem compactParserSyntaxExactEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserSyntaxExactEndpointGraphDef.val := by
  simp [compactParserSyntaxExactEndpointGraphDef]

def compactParserSyntaxExactEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      expectedBoundary expectedCount expectedBoundarySize
      stateBoundary stateCount tableWidth valueBound : Nat) :
    CompactParserSyntaxExactEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    expectedBoundary := expectedBoundary
    expectedCount := expectedCount
    expectedBoundarySize := expectedBoundarySize
    stateBoundary := stateBoundary
    stateCount := stateCount
    tableWidth := tableWidth
    valueBound := valueBound }

def CompactParserSyntaxExactEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount
      endpointBound : Nat) : Prop :=
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
    CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount
        (compactParserSyntaxExactEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          expectedBoundary expectedCount expectedBoundarySize
          stateBoundary stateCount tableWidth valueBound)

def compactParserSyntaxExactEndpointBoundedGraphDef :
    𝚺₀.Semisentence 11 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount
      endpointBound.
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
      !(compactParserSyntaxExactEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount
        inputBoundary inputCount inputBoundarySize
        expectedBoundary expectedCount expectedBoundarySize
        stateBoundary stateCount tableWidth valueBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactParserSyntaxExactEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount
      endpointBound : Nat) :
    compactParserSyntaxExactEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          expectedStart, expectedFinish, taskKind, taskBinderArity,
          taskRepeatCount, endpointBound] ↔
      CompactParserSyntaxExactEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish taskKind taskBinderArity
          taskRepeatCount endpointBound := by
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
                expectedStart, expectedFinish, taskKind, taskBinderArity,
                taskRepeatCount, endpointBound]
              Empty.elim ∘
            ![(#10 : Semiterm ℒₒᵣ Empty 21), #11, #12, #13, #14,
              #15, #16, #17, #18, #19,
              #9, #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactParserSyntaxExactEndpointGraphDef.val ↔
        CompactParserSyntaxExactEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            expectedStart expectedFinish taskKind taskBinderArity
            taskRepeatCount
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
              expectedStart, expectedFinish, taskKind, taskBinderArity,
              taskRepeatCount, endpointBound]
            Empty.elim ∘
          ![(#10 : Semiterm ℒₒᵣ Empty 21), #11, #12, #13, #14,
            #15, #16, #17, #18, #19,
            #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactParserSyntaxExactEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              expectedStart expectedFinish taskKind taskBinderArity
              taskRepeatCount
              (compactParserSyntaxExactEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                expectedBoundary expectedCount expectedBoundarySize
                stateBoundary stateCount tableWidth valueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactParserSyntaxExactEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish taskKind taskBinderArity
        taskRepeatCount _
  simp [compactParserSyntaxExactEndpointBoundedGraphDef,
    CompactParserSyntaxExactEndpointBoundedGraph, hrow]

theorem compactParserSyntaxExactEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserSyntaxExactEndpointBoundedGraphDef.val := by
  simp [compactParserSyntaxExactEndpointBoundedGraphDef]

theorem CompactParserSyntaxExactEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount
      endpointBound : Nat}
    (hbounded : CompactParserSyntaxExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish taskKind taskBinderArity
        taskRepeatCount endpointBound) :
    ∃ coordinates : CompactParserSyntaxExactEndpointCoordinates,
      CompactParserSyntaxExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish taskKind taskBinderArity
          taskRepeatCount coordinates := by
  unfold CompactParserSyntaxExactEndpointBoundedGraph at hbounded
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

theorem CompactParserSyntaxExactEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount :
      Nat}
    {coordinates : CompactParserSyntaxExactEndpointCoordinates}
    (hgraph : CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish taskKind taskBinderArity
        taskRepeatCount coordinates) :
    ∃ endpointBound,
      CompactParserSyntaxExactEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish taskKind taskBinderArity
          taskRepeatCount endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.expectedBoundary +
    coordinates.expectedCount + coordinates.expectedBoundarySize +
    coordinates.stateBoundary + coordinates.stateCount +
    coordinates.tableWidth + coordinates.valueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactParserSyntaxExactEndpointBoundedGraph
  refine
    ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
      coordinates.inputBoundarySize, ?_, coordinates.expectedBoundary, ?_,
      coordinates.expectedCount, ?_, coordinates.expectedBoundarySize, ?_,
      coordinates.stateBoundary, ?_, coordinates.stateCount, ?_,
      coordinates.tableWidth, ?_, coordinates.valueBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactParserSyntaxExactEndpointBoundedGraph.sound_formula
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity endpointBound : Nat}
    (hbounded : CompactParserSyntaxExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish 1 binderArity 0 endpointBound) :
    ∃ input expected : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount expectedStart expectedFinish expected ∧
      FoundationCompactSyntaxTokenMachine.compactFormulaTokenParser
        binderArity input = some expected := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound_formula

theorem CompactParserSyntaxExactEndpointBoundedGraph.sound_term
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity endpointBound : Nat}
    (hbounded : CompactParserSyntaxExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish 0 binderArity 0 endpointBound) :
    ∃ input expected : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount expectedStart expectedFinish expected ∧
      FoundationCompactSyntaxTokenMachine.compactTermTokenParser
        binderArity input = some expected := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound_term

#print axioms compactParserSyntaxExactEndpointGraphDef_spec
#print axioms compactParserSyntaxExactEndpointGraphDef_sigmaZero
#print axioms compactParserSyntaxExactEndpointBoundedGraphDef_spec
#print axioms compactParserSyntaxExactEndpointBoundedGraphDef_sigmaZero
#print axioms CompactParserSyntaxExactEndpointGraph.exists_bounded
#print axioms CompactParserSyntaxExactEndpointBoundedGraph.sound_formula
#print axioms CompactParserSyntaxExactEndpointBoundedGraph.sound_term

end FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
