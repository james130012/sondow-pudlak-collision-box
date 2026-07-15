import integration.FoundationCompactNumericListedDirectParserClosedNoOutputTraceFormula

/-!
# Exact bounded formula for public closed-parser no-output results

The complete no-output trace is fixed at the public quadratic fuel bound.
The closed formula parser is obtained by fixing the initial formula-task tag.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedNoOutputExactFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserClosedNoOutputTraceFormula

def CompactParserClosedNoOutputExactBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) : Prop :=
  CompactParserClosedNoOutputTraceBoundedGraph
    tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound

def compactParserClosedNoOutputExactBoundedGraphDef :
    𝚺₀.Semisentence 12 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound.
    !(compactParserClosedNoOutputTraceBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound”

@[simp] theorem compactParserClosedNoOutputExactBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) :
    compactParserClosedNoOutputExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount,
          inputBoundary, inputCount, taskKind, taskBinderArity,
          taskRepeatCount, tableWidth, valueBound] ↔
      CompactParserClosedNoOutputExactBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
        tableWidth valueBound := by
  let env : Fin 12 → Nat :=
    ![tokenTable, width, tokenCount, stateBoundary, stateCount,
      inputBoundary, inputCount, taskKind, taskBinderArity,
      taskRepeatCount, tableWidth, valueBound]
  change compactParserClosedNoOutputExactBoundedGraphDef.val.Evalb env ↔ _
  have htraceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2, #3, #4,
          (‘(16 * (#6 + 1) * (#6 + 1) + 8)’ :
            Semiterm ℒₒᵣ Empty 12),
          #5, #6, #7, #8, #9, #10, #11]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount,
          16 * (inputCount + 1) * (inputCount + 1) + 8,
          inputBoundary, inputCount, taskKind, taskBinderArity,
          taskRepeatCount, tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have htraceSpec :
      (Semiformula.Eval
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2, #3, #4,
            (‘(16 * (#6 + 1) * (#6 + 1) + 8)’ :
              Semiterm ℒₒᵣ Empty 12),
            #5, #6, #7, #8, #9, #10, #11])
          Empty.elim)
        compactParserClosedNoOutputTraceBoundedGraphDef.val ↔
      CompactParserClosedNoOutputTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount
        (16 * (inputCount + 1) * (inputCount + 1) + 8)
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
        tableWidth valueBound := by
    rw [htraceEnv]
    exact compactParserClosedNoOutputTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  simp [compactParserClosedNoOutputExactBoundedGraphDef,
    CompactParserClosedNoOutputExactBoundedGraph, htraceSpec]

theorem compactParserClosedNoOutputExactBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserClosedNoOutputExactBoundedGraphDef.val := by
  simp [compactParserClosedNoOutputExactBoundedGraphDef]

theorem CompactParserClosedNoOutputExactBoundedGraph.sound_local
    {tokenTable width tokenCount stateBoundary stateCount inputBoundary
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hgraph : CompactParserClosedNoOutputExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound)
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input) :
    CompactParserOutputLocalTraceValid FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states := by
  have htrace : CompactParserClosedNoOutputTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound := by
    simpa [CompactParserClosedNoOutputExactBoundedGraph,
      compactSyntaxRunFuelBound] using hgraph
  exact CompactParserClosedNoOutputTraceBoundedGraph.sound
    htrace hcount hrows hinput

theorem CompactParserClosedNoOutputExactBoundedGraph.sound_formula
    {tokenTable width tokenCount stateBoundary stateCount inputBoundary
      binderArity tableWidth valueBound : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hgraph : CompactParserClosedNoOutputExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary input.length 1 binderArity 0 tableWidth valueBound)
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input) :
    FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParser
      binderArity input = none := by
  have hlocal := hgraph.sound_local hcount hrows hinput
  have houtput :=
    (compactParserOutput_eq_iff_exists_localTrace
      FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep (compactSyntaxRunFuelBound input)
      (compactFormulaParserInitialState binderArity input) none).mpr
      ⟨states, by
        simpa [compactFormulaParserInitialState, compactFormulaTask] using
          hlocal⟩
  simpa [
    FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParser,
    FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParserRun]
    using houtput

theorem localTrace_exists_compactParserClosedNoOutputExactBoundedFormula
    {tokenTable width tokenCount stateBoundary inputBoundary
      taskKind taskBinderArity taskRepeatCount : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    ∃ tableWidth : Nat,
      compactParserClosedNoOutputExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length,
          inputBoundary, input.length, taskKind, taskBinderArity,
          taskRepeatCount, tableWidth, 2 ^ tableWidth] := by
  rcases localTrace_exists_compactParserClosedNoOutputTraceBoundedFormula
      hrows hinput hstartWell hvalid with
    ⟨tableWidth, htrace⟩
  refine ⟨tableWidth,
    (compactParserClosedNoOutputExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mpr ?_⟩
  have hgraph :=
    (compactParserClosedNoOutputTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mp htrace
  simpa [CompactParserClosedNoOutputExactBoundedGraph,
    compactSyntaxRunFuelBound] using hgraph

#print axioms compactParserClosedNoOutputExactBoundedGraphDef_spec
#print axioms compactParserClosedNoOutputExactBoundedGraphDef_sigmaZero
#print axioms CompactParserClosedNoOutputExactBoundedGraph.sound_local
#print axioms CompactParserClosedNoOutputExactBoundedGraph.sound_formula
#print axioms localTrace_exists_compactParserClosedNoOutputExactBoundedFormula

end FoundationCompactNumericListedDirectParserClosedNoOutputExactFormula
