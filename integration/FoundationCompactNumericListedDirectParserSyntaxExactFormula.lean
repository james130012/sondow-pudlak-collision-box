import integration.FoundationCompactNumericListedDirectParserSyntaxTraceFormula

/-!
# Exact bounded formula for the public syntax parser

The complete syntax-trace graph is fixed at the public quadratic fuel bound.
Formula and term parsers are obtained by fixing the initial task tag, while all
state rows and the final suffix remain part of the same checked token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxExactFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula

def CompactParserSyntaxExactBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) : Prop :=
  CompactParserSyntaxTraceBoundedGraph
    tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound

def compactParserSyntaxExactBoundedGraphDef :
    𝚺₀.Semisentence 14 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound.
    !(compactParserSyntaxTraceBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound”

@[simp] theorem compactParserSyntaxExactBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) :
    compactParserSyntaxExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount,
          inputBoundary, inputCount, expectedBoundary, expectedCount,
          taskKind, taskBinderArity, taskRepeatCount, tableWidth, valueBound] ↔
      CompactParserSyntaxExactBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount
        tableWidth valueBound := by
  let env : Fin 14 → Nat :=
    ![tokenTable, width, tokenCount, stateBoundary, stateCount,
      inputBoundary, inputCount, expectedBoundary, expectedCount,
      taskKind, taskBinderArity, taskRepeatCount, tableWidth, valueBound]
  change compactParserSyntaxExactBoundedGraphDef.val.Evalb env ↔ _
  have htraceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #3, #4,
          (‘(16 * (#6 + 1) * (#6 + 1) + 8)’ : Semiterm ℒₒᵣ Empty 14),
          #5, #6, #7, #8, #9, #10, #11, #12, #13]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount,
          16 * (inputCount + 1) * (inputCount + 1) + 8,
          inputBoundary, inputCount, expectedBoundary, expectedCount,
          taskKind, taskBinderArity, taskRepeatCount,
          tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have htraceSpec :
      (Semiformula.Eval
        (Semiterm.val env Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #3, #4,
            (‘(16 * (#6 + 1) * (#6 + 1) + 8)’ :
              Semiterm ℒₒᵣ Empty 14),
            #5, #6, #7, #8, #9, #10, #11, #12, #13])
          Empty.elim)
        compactParserSyntaxTraceBoundedGraphDef.val ↔
      CompactParserSyntaxTraceBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount
        (16 * (inputCount + 1) * (inputCount + 1) + 8)
        inputBoundary inputCount expectedBoundary expectedCount
        taskKind taskBinderArity taskRepeatCount
        tableWidth valueBound := by
    rw [htraceEnv]
    exact compactParserSyntaxTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary stateCount
      (16 * (inputCount + 1) * (inputCount + 1) + 8)
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound
  simp [compactParserSyntaxExactBoundedGraphDef,
    CompactParserSyntaxExactBoundedGraph, htraceSpec]

theorem compactParserSyntaxExactBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactParserSyntaxExactBoundedGraphDef.val := by
  simp [compactParserSyntaxExactBoundedGraphDef]

theorem CompactParserSyntaxExactBoundedGraph.sound_local
    {tokenTable width tokenCount stateBoundary stateCount
      inputBoundary expectedBoundary taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat}
    {states : List CompactUnifiedParserState}
    {input expected : List Nat}
    (hgraph : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound)
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedBoundary expected) :
    CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states := by
  have htrace : CompactParserSyntaxTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound := by
    simpa [CompactParserSyntaxExactBoundedGraph,
      compactSyntaxRunFuelBound] using hgraph
  exact CompactParserSyntaxTraceBoundedGraph.sound
    htrace hcount hrows hinput hexpected

theorem CompactParserSyntaxExactBoundedGraph.sound_formula
    {tokenTable width tokenCount stateBoundary stateCount
      inputBoundary expectedBoundary binderArity tableWidth valueBound : Nat}
    {states : List CompactUnifiedParserState}
    {input expected : List Nat}
    (hgraph : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary input.length expectedBoundary expected.length
      1 binderArity 0 tableWidth valueBound)
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedBoundary expected) :
    compactFormulaTokenParser binderArity input = some expected := by
  apply (compactFormulaTokenParser_eq_some_iff_exists_directTrace
    binderArity input expected).mpr
  refine ⟨states, ?_⟩
  simpa [CompactFormulaTokenParserDirectTraceValid,
    compactFormulaParserInitialState, compactFormulaTask] using
      hgraph.sound_local hcount hrows hinput hexpected

theorem localTrace_exists_compactParserSyntaxExactBoundedFormula
    {tokenTable width tokenCount stateBoundary
      inputBoundary expectedBoundary taskKind taskBinderArity taskRepeatCount :
      Nat}
    {states : List CompactUnifiedParserState}
    {input expected : List Nat}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        expectedBoundary expected)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states) :
    ∃ tableWidth : Nat,
      compactParserSyntaxExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length,
          inputBoundary, input.length, expectedBoundary, expected.length,
          taskKind, taskBinderArity, taskRepeatCount,
          tableWidth, 2 ^ tableWidth] := by
  rcases localTrace_exists_compactParserSyntaxTraceBoundedFormula
      hrows hinput hexpected hstartWell hvalid with
    ⟨tableWidth, htrace⟩
  refine ⟨tableWidth,
    (compactParserSyntaxExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mpr ?_⟩
  have hgraph :=
    (compactParserSyntaxTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mp htrace
  simpa [CompactParserSyntaxExactBoundedGraph,
    compactSyntaxRunFuelBound] using hgraph

#print axioms compactParserSyntaxExactBoundedGraphDef_spec
#print axioms compactParserSyntaxExactBoundedGraphDef_sigmaZero
#print axioms CompactParserSyntaxExactBoundedGraph.sound_local
#print axioms CompactParserSyntaxExactBoundedGraph.sound_formula
#print axioms localTrace_exists_compactParserSyntaxExactBoundedFormula

end FoundationCompactNumericListedDirectParserSyntaxExactFormula
