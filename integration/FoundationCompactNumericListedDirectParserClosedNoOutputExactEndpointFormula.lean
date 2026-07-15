import integration.FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointCompleteness

/-!
# Bounded arithmetic formula for closed-parser no-output endpoints

The input slice and complete parser trace form one fifteen-column Delta-zero
graph.  Seven internal coordinates are quantified below one public bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointFormula

open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectParserClosedNoOutputExactFormula
open FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointCompleteness

def compactParserClosedNoOutputExactEndpointGraphDef :
    𝚺₀.Semisentence 15 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount
      inputBoundary inputCount inputBoundarySize
      stateBoundary stateCount tableWidth valueBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactParserClosedNoOutputExactBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound”

def compactParserClosedNoOutputExactEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat)
    (coordinates : CompactParserClosedNoOutputExactEndpointCoordinates) :
    Fin 15 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    taskKind, taskBinderArity, taskRepeatCount,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize, coordinates.stateBoundary,
    coordinates.stateCount, coordinates.tableWidth, coordinates.valueBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactParserClosedNoOutputExactEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat)
    (coordinates : CompactParserClosedNoOutputExactEndpointCoordinates) :
    compactParserClosedNoOutputExactEndpointGraphDef.val.Evalb
        (compactParserClosedNoOutputExactEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
          taskKind taskBinderArity taskRepeatCount coordinates) ↔
      CompactParserClosedNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount coordinates := by
  let env := compactParserClosedNoOutputExactEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
    taskKind taskBinderArity taskRepeatCount coordinates
  change compactParserClosedNoOutputExactEndpointGraphDef.val.Evalb env ↔ _
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
  simp [compactParserClosedNoOutputExactEndpointGraphDef,
    CompactParserClosedNoOutputExactEndpointGraph,
    hinputEnv, hexactEnv]

theorem compactParserClosedNoOutputExactEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserClosedNoOutputExactEndpointGraphDef.val := by
  simp [compactParserClosedNoOutputExactEndpointGraphDef]

def compactParserClosedNoOutputExactEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      stateBoundary stateCount tableWidth valueBound : Nat) :
    CompactParserClosedNoOutputExactEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    stateBoundary := stateBoundary
    stateCount := stateCount
    tableWidth := tableWidth
    valueBound := valueBound }

def CompactParserClosedNoOutputExactEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ stateBoundary, stateBoundary ≤ endpointBound ∧
  ∃ stateCount, stateCount ≤ endpointBound ∧
  ∃ tableWidth, tableWidth ≤ endpointBound ∧
  ∃ valueBound, valueBound ≤ endpointBound ∧
    CompactParserClosedNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount
        (compactParserClosedNoOutputExactEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          stateBoundary stateCount tableWidth valueBound)

def compactParserClosedNoOutputExactEndpointBoundedGraphDef :
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
      !(compactParserClosedNoOutputExactEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount
        inputBoundary inputCount inputBoundarySize
        stateBoundary stateCount tableWidth valueBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactParserClosedNoOutputExactEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount endpointBound : Nat) :
    compactParserClosedNoOutputExactEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          taskKind, taskBinderArity, taskRepeatCount, endpointBound] ↔
      CompactParserClosedNoOutputExactEndpointBoundedGraph
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
        compactParserClosedNoOutputExactEndpointGraphDef.val ↔
      CompactParserClosedNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount
        (compactParserClosedNoOutputExactEndpointCoordinatesOfValues
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
          compactParserClosedNoOutputExactEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
            taskKind taskBinderArity taskRepeatCount
            (compactParserClosedNoOutputExactEndpointCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              stateBoundary stateCount tableWidth valueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactParserClosedNoOutputExactEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount _
  simp [compactParserClosedNoOutputExactEndpointBoundedGraphDef,
    CompactParserClosedNoOutputExactEndpointBoundedGraph, hrow]

theorem compactParserClosedNoOutputExactEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserClosedNoOutputExactEndpointBoundedGraphDef.val := by
  simp [compactParserClosedNoOutputExactEndpointBoundedGraphDef]

theorem CompactParserClosedNoOutputExactEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount endpointBound : Nat}
    (hbounded : CompactParserClosedNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount endpointBound) :
    ∃ coordinates : CompactParserClosedNoOutputExactEndpointCoordinates,
      CompactParserClosedNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      stateBoundary, _, stateCount, _, tableWidth, _, valueBound, _, hgraph⟩
  exact ⟨compactParserClosedNoOutputExactEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    stateBoundary stateCount tableWidth valueBound, hgraph⟩

theorem CompactParserClosedNoOutputExactEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat}
    {coordinates : CompactParserClosedNoOutputExactEndpointCoordinates}
    (hgraph : CompactParserClosedNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount coordinates) :
    ∃ endpointBound,
      CompactParserClosedNoOutputExactEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.stateBoundary +
    coordinates.stateCount + coordinates.tableWidth + coordinates.valueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactParserClosedNoOutputExactEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.stateBoundary, ?_,
    coordinates.stateCount, ?_, coordinates.tableWidth, ?_,
    coordinates.valueBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactParserClosedNoOutputExactEndpointBoundedGraph.sound_formula
    {tokenTable width tokenCount inputStart inputFinish
      binderArity endpointBound : Nat}
    (hbounded : CompactParserClosedNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
      1 binderArity 0 endpointBound) :
    ∃ input : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParser
        binderArity input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound_formula

#print axioms compactParserClosedNoOutputExactEndpointGraphDef_spec
#print axioms compactParserClosedNoOutputExactEndpointGraphDef_sigmaZero
#print axioms compactParserClosedNoOutputExactEndpointBoundedGraphDef_spec
#print axioms compactParserClosedNoOutputExactEndpointBoundedGraphDef_sigmaZero
#print axioms CompactParserClosedNoOutputExactEndpointGraph.exists_bounded
#print axioms CompactParserClosedNoOutputExactEndpointBoundedGraph.sound_formula

end FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointFormula
