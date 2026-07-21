import integration.FoundationCompactNumericListedDirectFormulaTransformExactFormula
import integration.FoundationCompactNumericListedDirectListFvSupRows

/-!
# Exact direct formula for formula free-variable supremum

The endpoint joins the complete mode-four formula-transform trace to the
direct maximum relation on its emitted free-variable list.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaFvSupExactFormula

open FoundationCompactSyntaxTransformationTraceCore
open FoundationCompactNumericFormulaFvSup
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformExactFormula
open FoundationCompactNumericListedDirectListFvSupRows

def CompactFormulaFvSupExactBoundedGraph
    (tokenTable width tokenCount stateBoundary stateCount
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount outputBoundary outputCount
      emptySuffixBoundary binderArity tableWidth valueBound maximum : Nat) :
    Prop :=
  CompactFormulaTransformExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount 4
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount outputBoundary outputCount
      emptySuffixBoundary binderArity tableWidth valueBound /\
    CompactAdditiveNatListFvSupRows
      tokenTable width tokenCount outputBoundary outputCount maximum

def compactFormulaFvSupExactBoundedGraphDef :
    𝚺₀.Semisentence 17 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount outputBoundary outputCount
      emptySuffixBoundary binderArity tableWidth valueBound maximum.
    !(compactFormulaTransformExactBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount 4
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount outputBoundary outputCount
      emptySuffixBoundary binderArity tableWidth valueBound ∧
    !(compactAdditiveNatListFvSupRowsDef)
      tokenTable width tokenCount outputBoundary outputCount maximum”

@[simp] theorem compactFormulaFvSupExactBoundedGraphDef_spec
    (tokenTable width tokenCount stateBoundary stateCount
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount outputBoundary outputCount
      emptySuffixBoundary binderArity tableWidth valueBound maximum : Nat) :
    compactFormulaFvSupExactBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, stateCount,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, inputCount, outputBoundary, outputCount,
          emptySuffixBoundary, binderArity, tableWidth, valueBound, maximum] ↔
      CompactFormulaFvSupExactBoundedGraph
        tokenTable width tokenCount stateBoundary stateCount
        witnessStart witnessFinish witnessCount
        inputBoundary inputCount outputBoundary outputCount
        emptySuffixBoundary binderArity tableWidth valueBound maximum := by
  let env : Fin 17 -> Nat :=
    ![tokenTable, width, tokenCount, stateBoundary, stateCount,
      witnessStart, witnessFinish, witnessCount,
      inputBoundary, inputCount, outputBoundary, outputCount,
      emptySuffixBoundary, binderArity, tableWidth, valueBound, maximum]
  change compactFormulaFvSupExactBoundedGraphDef.val.Evalb env ↔ _
  have hexactEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #3, #4, ‘4’,
          #5, #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, 4,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, inputCount, outputBoundary, outputCount,
          emptySuffixBoundary, binderArity, tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hsupEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #10, #11, #16]) =
        ![tokenTable, width, tokenCount,
          outputBoundary, outputCount, maximum] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hexact :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #3, #4, ‘4’,
              #5, #6, #7, #8, #9, #10, #11, #12, #13, #14, #15])
          Empty.elim) compactFormulaTransformExactBoundedGraphDef.val ↔
        CompactFormulaTransformExactBoundedGraph
          tokenTable width tokenCount stateBoundary stateCount 4
          witnessStart witnessFinish witnessCount
          inputBoundary inputCount outputBoundary outputCount
          emptySuffixBoundary binderArity tableWidth valueBound := by
    rw [hexactEnv]
    exact compactFormulaTransformExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary stateCount 4
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      outputBoundary outputCount emptySuffixBoundary binderArity
      tableWidth valueBound
  have hsup :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 17), #1, #2, #10, #11, #16])
          Empty.elim) compactAdditiveNatListFvSupRowsDef.val ↔
        CompactAdditiveNatListFvSupRows
          tokenTable width tokenCount outputBoundary outputCount maximum := by
    rw [hsupEnv]
    exact compactAdditiveNatListFvSupRowsDef_spec
      tokenTable width tokenCount outputBoundary outputCount maximum
  simp [compactFormulaFvSupExactBoundedGraphDef,
    CompactFormulaFvSupExactBoundedGraph, hexact, hsup]

theorem compactFormulaFvSupExactBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaFvSupExactBoundedGraphDef.val := by
  simp [compactFormulaFvSupExactBoundedGraphDef]

theorem CompactFormulaFvSupExactBoundedGraph.sound
    {tokenTable width tokenCount stateBoundary stateCount
      witnessStart witnessFinish witnessCount
      inputBoundary outputBoundary emptySuffixBoundary
      binderArity tableWidth valueBound maximum : Nat}
    {states : List CompactFormulaTransformState}
    {witness input output : List Nat}
    (hgraph : CompactFormulaFvSupExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      witnessStart witnessFinish witnessCount
      inputBoundary input.length outputBoundary output.length
      emptySuffixBoundary binderArity tableWidth valueBound maximum)
    (hcount : states.length = stateCount)
    (hstates : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (houtput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        outputBoundary output)
    (hemptySuffix : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptySuffixBoundary []) :
    compactFormulaFvSupTokenTransform binderArity input =
      some (maximum, []) := by
  have hlist : compactFormulaFvListTokenTransform binderArity input =
      some (output, []) := by
    simpa using CompactFormulaTransformExactBoundedGraph.sound_result
      hgraph.1 hcount hstates hwitness hwitnessCount
        hinput houtput hemptySuffix
  have hmaximum : maximum = listFvSup output :=
    (compactAdditiveNatListFvSupRows_iff houtput maximum).mp hgraph.2
  simp [compactFormulaFvSupTokenTransform, hlist, hmaximum]

#print axioms compactFormulaFvSupExactBoundedGraphDef_spec
#print axioms compactFormulaFvSupExactBoundedGraphDef_sigmaZero
#print axioms CompactFormulaFvSupExactBoundedGraph.sound

end FoundationCompactNumericListedDirectFormulaFvSupExactFormula
