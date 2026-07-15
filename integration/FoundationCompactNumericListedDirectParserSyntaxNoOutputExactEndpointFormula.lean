import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness

/-!
# Bounded arithmetic formula for syntax-parser no-output endpoints

The input slice and complete parser trace form one fifteen-column Delta-zero
graph.  Seven internal coordinates are quantified below one public bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula

open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness

def compactParserSyntaxNoOutputExactEndpointGraphDef :
    𝚺₀.Semisentence 15 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount
      inputBoundary inputCount inputBoundarySize
      stateBoundary stateCount tableWidth valueBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactParserSyntaxNoOutputExactBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound”

def compactParserSyntaxNoOutputExactEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat)
    (coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates) :
    Fin 15 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    taskKind, taskBinderArity, taskRepeatCount,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize, coordinates.stateBoundary,
    coordinates.stateCount, coordinates.tableWidth, coordinates.valueBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactParserSyntaxNoOutputExactEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat)
    (coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates) :
    compactParserSyntaxNoOutputExactEndpointGraphDef.val.Evalb
        (compactParserSyntaxNoOutputExactEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
          taskKind taskBinderArity taskRepeatCount coordinates) ↔
      CompactParserSyntaxNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount coordinates := by
  let env := compactParserSyntaxNoOutputExactEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
    taskKind taskBinderArity taskRepeatCount coordinates
  change compactParserSyntaxNoOutputExactEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2, #3, #9, #4,
          #8, #10]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hexactEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2, #11, #12,
          #8, #9, #5, #6, #7, #13, #14]) =
        ![tokenTable, width, tokenCount,
          coordinates.stateBoundary, coordinates.stateCount,
          coordinates.inputBoundary, coordinates.inputCount,
          taskKind, taskBinderArity, taskRepeatCount,
          coordinates.tableWidth, coordinates.valueBound] := by
    funext index
    fin_cases index <;> rfl
  simp [compactParserSyntaxNoOutputExactEndpointGraphDef,
    CompactParserSyntaxNoOutputExactEndpointGraph,
    hinputEnv, hexactEnv]

theorem compactParserSyntaxNoOutputExactEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserSyntaxNoOutputExactEndpointGraphDef.val := by
  simp [compactParserSyntaxNoOutputExactEndpointGraphDef]

def compactParserSyntaxNoOutputExactEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      stateBoundary stateCount tableWidth valueBound : Nat) :
    CompactParserSyntaxNoOutputExactEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    stateBoundary := stateBoundary
    stateCount := stateCount
    tableWidth := tableWidth
    valueBound := valueBound }

def CompactParserSyntaxNoOutputExactEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ stateBoundary, stateBoundary ≤ endpointBound ∧
  ∃ stateCount, stateCount ≤ endpointBound ∧
  ∃ tableWidth, tableWidth ≤ endpointBound ∧
  ∃ valueBound, valueBound ≤ endpointBound ∧
    CompactParserSyntaxNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount
        (compactParserSyntaxNoOutputExactEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          stateBoundary stateCount tableWidth valueBound)

def compactParserSyntaxNoOutputExactEndpointBoundedGraphDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ stateBoundary <⁺ endpointBound,
    ∃ stateCount <⁺ endpointBound,
    ∃ tableWidth <⁺ endpointBound,
    ∃ valueBound <⁺ endpointBound,
      !(compactParserSyntaxNoOutputExactEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount
        inputBoundary inputCount inputBoundarySize
        stateBoundary stateCount tableWidth valueBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactParserSyntaxNoOutputExactEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount endpointBound : Nat) :
    compactParserSyntaxNoOutputExactEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          taskKind, taskBinderArity, taskRepeatCount, endpointBound] ↔
      CompactParserSyntaxNoOutputExactEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount endpointBound := by
  have hrow
      (valueBound tableWidth stateCount stateBoundary
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![valueBound, tableWidth, stateCount, stateBoundary,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                taskKind, taskBinderArity, taskRepeatCount, endpointBound]
              Empty.elim ∘
            ![(#7 : Semiterm ℒₒᵣ Empty 16), #8, #9, #10, #11,
              #12, #13, #14, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactParserSyntaxNoOutputExactEndpointGraphDef.val ↔
      CompactParserSyntaxNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount
        (compactParserSyntaxNoOutputExactEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          stateBoundary stateCount tableWidth valueBound) := by
    have henv :
        (Semiterm.val
            ![valueBound, tableWidth, stateCount, stateBoundary,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              taskKind, taskBinderArity, taskRepeatCount, endpointBound]
            Empty.elim ∘
          ![(#7 : Semiterm ℒₒᵣ Empty 16), #8, #9, #10, #11,
            #12, #13, #14, #6, #5, #4, #3, #2, #1, #0]) =
          compactParserSyntaxNoOutputExactEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
            taskKind taskBinderArity taskRepeatCount
            (compactParserSyntaxNoOutputExactEndpointCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              stateBoundary stateCount tableWidth valueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactParserSyntaxNoOutputExactEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount _
  simp [compactParserSyntaxNoOutputExactEndpointBoundedGraphDef,
    CompactParserSyntaxNoOutputExactEndpointBoundedGraph, hrow]

theorem compactParserSyntaxNoOutputExactEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserSyntaxNoOutputExactEndpointBoundedGraphDef.val := by
  simp [compactParserSyntaxNoOutputExactEndpointBoundedGraphDef]

theorem CompactParserSyntaxNoOutputExactEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount endpointBound : Nat}
    (hbounded : CompactParserSyntaxNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount endpointBound) :
    ∃ coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates,
      CompactParserSyntaxNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      stateBoundary, _, stateCount, _, tableWidth, _, valueBound, _, hgraph⟩
  exact ⟨compactParserSyntaxNoOutputExactEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    stateBoundary stateCount tableWidth valueBound, hgraph⟩

theorem CompactParserSyntaxNoOutputExactEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat}
    {coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates}
    (hgraph : CompactParserSyntaxNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount coordinates) :
    ∃ endpointBound,
      CompactParserSyntaxNoOutputExactEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.stateBoundary +
    coordinates.stateCount + coordinates.tableWidth + coordinates.valueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactParserSyntaxNoOutputExactEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.stateBoundary, ?_,
    coordinates.stateCount, ?_, coordinates.tableWidth, ?_,
    coordinates.valueBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactParserSyntaxNoOutputExactEndpointBoundedGraph.sound_formula
    {tokenTable width tokenCount inputStart inputFinish
      binderArity endpointBound : Nat}
    (hbounded : CompactParserSyntaxNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
      1 binderArity 0 endpointBound) :
    ∃ input : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactSyntaxTokenMachine.compactFormulaTokenParser
        binderArity input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound_formula

theorem CompactParserSyntaxNoOutputExactEndpointBoundedGraph.sound_term
    {tokenTable width tokenCount inputStart inputFinish
      binderArity endpointBound : Nat}
    (hbounded : CompactParserSyntaxNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
      0 binderArity 0 endpointBound) :
    ∃ input : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactSyntaxTokenMachine.compactTermTokenParser
        binderArity input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound_term

#print axioms compactParserSyntaxNoOutputExactEndpointGraphDef_spec
#print axioms compactParserSyntaxNoOutputExactEndpointGraphDef_sigmaZero
#print axioms compactParserSyntaxNoOutputExactEndpointBoundedGraphDef_spec
#print axioms compactParserSyntaxNoOutputExactEndpointBoundedGraphDef_sigmaZero
#print axioms CompactParserSyntaxNoOutputExactEndpointGraph.exists_bounded
#print axioms CompactParserSyntaxNoOutputExactEndpointBoundedGraph.sound_formula
#print axioms CompactParserSyntaxNoOutputExactEndpointBoundedGraph.sound_term

end FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula
