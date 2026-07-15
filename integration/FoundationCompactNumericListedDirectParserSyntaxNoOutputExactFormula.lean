import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputTraceFormula

/-!
# Exact bounded formula for public syntax-parser no-output results

The complete no-output trace is fixed at the public quadratic fuel bound.
Formula and term parsers are obtained by fixing the initial task tag.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxNoOutputExactFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputTraceFormula

def CompactParserSyntaxNoOutputExactBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) : Prop :=
  CompactParserSyntaxNoOutputTraceBoundedGraph
    tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound

def compactParserSyntaxNoOutputExactBoundedGraphDef :
    𝚺₀.Semisentence 12 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound.
    !(compactParserSyntaxNoOutputTraceBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound”

@[simp] theorem compactParserSyntaxNoOutputExactBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) :
    compactParserSyntaxNoOutputExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount,
          inputBoundary, inputCount, taskKind, taskBinderArity,
          taskRepeatCount, tableWidth, valueBound] ↔
      CompactParserSyntaxNoOutputExactBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
        tableWidth valueBound := by
  let env : Fin 12 → Nat :=
    ![tokenTable, width, tokenCount, stateBoundary, stateCount,
      inputBoundary, inputCount, taskKind, taskBinderArity,
      taskRepeatCount, tableWidth, valueBound]
  change compactParserSyntaxNoOutputExactBoundedGraphDef.val.Evalb env ↔ _
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
        compactParserSyntaxNoOutputTraceBoundedGraphDef.val ↔
      CompactParserSyntaxNoOutputTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount
        (16 * (inputCount + 1) * (inputCount + 1) + 8)
        inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
        tableWidth valueBound := by
    rw [htraceEnv]
    exact compactParserSyntaxNoOutputTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      inputBoundary inputCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  simp [compactParserSyntaxNoOutputExactBoundedGraphDef,
    CompactParserSyntaxNoOutputExactBoundedGraph, htraceSpec]

theorem compactParserSyntaxNoOutputExactBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserSyntaxNoOutputExactBoundedGraphDef.val := by
  simp [compactParserSyntaxNoOutputExactBoundedGraphDef]

theorem CompactParserSyntaxNoOutputExactBoundedGraph.sound_local
    {tokenTable width tokenCount stateBoundary stateCount inputBoundary
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hgraph : CompactParserSyntaxNoOutputExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound)
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input) :
    CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states := by
  have htrace : CompactParserSyntaxNoOutputTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound := by
    simpa [CompactParserSyntaxNoOutputExactBoundedGraph,
      compactSyntaxRunFuelBound] using hgraph
  exact CompactParserSyntaxNoOutputTraceBoundedGraph.sound
    htrace hcount hrows hinput

theorem CompactParserSyntaxNoOutputExactBoundedGraph.sound_formula
    {tokenTable width tokenCount stateBoundary stateCount inputBoundary
      binderArity tableWidth valueBound : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hgraph : CompactParserSyntaxNoOutputExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary input.length 1 binderArity 0 tableWidth valueBound)
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input) :
    compactFormulaTokenParser binderArity input = none := by
  have hlocal := hgraph.sound_local hcount hrows hinput
  have houtput :=
    (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound input)
      (compactFormulaParserInitialState binderArity input) none).mpr
      ⟨states, by
        simpa [compactFormulaParserInitialState, compactFormulaTask] using
          hlocal⟩
  simpa [compactFormulaTokenParser, compactFormulaTokenParserRun] using
    houtput

theorem CompactParserSyntaxNoOutputExactBoundedGraph.sound_term
    {tokenTable width tokenCount stateBoundary stateCount inputBoundary
      binderArity tableWidth valueBound : Nat}
    {states : List CompactUnifiedParserState}
    {input : List Nat}
    (hgraph : CompactParserSyntaxNoOutputExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary input.length 0 binderArity 0 tableWidth valueBound)
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input) :
    compactTermTokenParser binderArity input = none := by
  have hlocal := hgraph.sound_local hcount hrows hinput
  have houtput :=
    (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound input)
      (compactTermParserInitialState binderArity input) none).mpr
      ⟨states, by
        simpa [compactTermParserInitialState, compactTermTask] using hlocal⟩
  simpa [compactTermTokenParser, compactTermTokenParserRun] using houtput

theorem localTrace_exists_compactParserSyntaxNoOutputExactBoundedFormula
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
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    ∃ tableWidth : Nat,
      compactParserSyntaxNoOutputExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length,
          inputBoundary, input.length, taskKind, taskBinderArity,
          taskRepeatCount, tableWidth, 2 ^ tableWidth] := by
  rcases localTrace_exists_compactParserSyntaxNoOutputTraceBoundedFormula
      hrows hinput hstartWell hvalid with
    ⟨tableWidth, htrace⟩
  refine ⟨tableWidth,
    (compactParserSyntaxNoOutputExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mpr ?_⟩
  have hgraph :=
    (compactParserSyntaxNoOutputTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mp htrace
  simpa [CompactParserSyntaxNoOutputExactBoundedGraph,
    compactSyntaxRunFuelBound] using hgraph

#print axioms compactParserSyntaxNoOutputExactBoundedGraphDef_spec
#print axioms compactParserSyntaxNoOutputExactBoundedGraphDef_sigmaZero
#print axioms CompactParserSyntaxNoOutputExactBoundedGraph.sound_local
#print axioms CompactParserSyntaxNoOutputExactBoundedGraph.sound_formula
#print axioms CompactParserSyntaxNoOutputExactBoundedGraph.sound_term
#print axioms localTrace_exists_compactParserSyntaxNoOutputExactBoundedFormula

end FoundationCompactNumericListedDirectParserSyntaxNoOutputExactFormula
