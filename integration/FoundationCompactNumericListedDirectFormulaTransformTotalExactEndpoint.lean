import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
import integration.FoundationCompactNumericListedDirectNatListWitnessRows
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

/-!
# Self-contained total exact formula-transform endpoint

The endpoint includes direct rows for the control witness, input, output, and
empty default.  Its bounded trace therefore decodes to the public transform
result without external layout or state-list premises.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula

def CompactFormulaTransformTotalExactEndpoint
    (tokenTable width tokenCount mode binderArity
      witnessStart witnessFinish witnessBoundary witnessCount witnessBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      outputStart outputFinish outputBoundary outputCount outputBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      stateBoundary stateCount tableWidth valueBound : Nat) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount witnessStart witnessCount witnessFinish
        witnessBoundary witnessBoundarySize /\
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize /\
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount outputStart outputCount outputFinish
        outputBoundary outputBoundarySize /\
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary emptyBoundarySize /\
    CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount outputBoundary outputCount emptyBoundary
      binderArity tableWidth valueBound

def compactFormulaTransformTotalExactEndpointDef :
    𝚺₀.Semisentence 28 := .mkSigma
  “tokenTable width tokenCount mode binderArity
      witnessStart witnessFinish witnessBoundary witnessCount witnessBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      outputStart outputFinish outputBoundary outputCount outputBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      stateBoundary stateCount tableWidth valueBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount witnessStart witnessCount witnessFinish
        witnessBoundary witnessBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount outputStart outputCount outputFinish
        outputBoundary outputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary emptyBoundarySize ∧
    !(compactFormulaTransformTotalExactBoundedGraphDef)
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount outputBoundary outputCount emptyBoundary
      binderArity tableWidth valueBound”

@[simp] theorem compactFormulaTransformTotalExactEndpointDef_spec
    (tokenTable width tokenCount mode binderArity
      witnessStart witnessFinish witnessBoundary witnessCount witnessBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      outputStart outputFinish outputBoundary outputCount outputBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      stateBoundary stateCount tableWidth valueBound : Nat) :
    compactFormulaTransformTotalExactEndpointDef.val.Evalb
        ![tokenTable, width, tokenCount, mode, binderArity,
          witnessStart, witnessFinish, witnessBoundary,
          witnessCount, witnessBoundarySize,
          inputStart, inputFinish, inputBoundary, inputCount, inputBoundarySize,
          outputStart, outputFinish, outputBoundary,
          outputCount, outputBoundarySize,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          stateBoundary, stateCount, tableWidth, valueBound] ↔
      CompactFormulaTransformTotalExactEndpoint
        tokenTable width tokenCount mode binderArity
        witnessStart witnessFinish witnessBoundary witnessCount witnessBoundarySize
        inputStart inputFinish inputBoundary inputCount inputBoundarySize
        outputStart outputFinish outputBoundary outputCount outputBoundarySize
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        stateBoundary stateCount tableWidth valueBound := by
  let env : Fin 28 -> Nat :=
    ![tokenTable, width, tokenCount, mode, binderArity,
      witnessStart, witnessFinish, witnessBoundary,
      witnessCount, witnessBoundarySize,
      inputStart, inputFinish, inputBoundary, inputCount, inputBoundarySize,
      outputStart, outputFinish, outputBoundary,
      outputCount, outputBoundarySize,
      emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
      stateBoundary, stateCount, tableWidth, valueBound]
  change compactFormulaTransformTotalExactEndpointDef.val.Evalb env ↔ _
  have hwitnessEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
          #5, #8, #6, #7, #9]) =
        ![tokenTable, width, tokenCount,
          witnessStart, witnessCount, witnessFinish,
          witnessBoundary, witnessBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
          #10, #13, #11, #12, #14]) =
        ![tokenTable, width, tokenCount,
          inputStart, inputCount, inputFinish,
          inputBoundary, inputBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have houtputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
          #15, #18, #16, #17, #19]) =
        ![tokenTable, width, tokenCount,
          outputStart, outputCount, outputFinish,
          outputBoundary, outputBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hemptyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
          #20, ‘0’, #21, #22, #23]) =
        ![tokenTable, width, tokenCount,
          emptyStart, 0, emptyFinish, emptyBoundary, emptyBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have htraceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2, #24, #25, #3,
          #5, #6, #8, #12, #13, #17, #18, #22, #4, #26, #27]) =
        ![tokenTable, width, tokenCount, stateBoundary, stateCount, mode,
          witnessStart, witnessFinish, witnessCount,
          inputBoundary, inputCount, outputBoundary, outputCount,
          emptyBoundary, binderArity, tableWidth, valueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hwitnessSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
              #5, #8, #6, #7, #9])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount witnessStart witnessCount witnessFinish
            witnessBoundary witnessBoundarySize := by
    rw [hwitnessEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount witnessStart witnessCount witnessFinish
      witnessBoundary witnessBoundarySize
  have hinputSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
              #10, #13, #11, #12, #14])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount inputStart inputCount inputFinish
            inputBoundary inputBoundarySize := by
    rw [hinputEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount inputStart inputCount inputFinish
      inputBoundary inputBoundarySize
  have houtputSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
              #15, #18, #16, #17, #19])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount outputStart outputCount outputFinish
            outputBoundary outputBoundarySize := by
    rw [houtputEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount outputStart outputCount outputFinish
      outputBoundary outputBoundarySize
  have hemptySpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
              #20, ‘0’, #21, #22, #23])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount emptyStart 0 emptyFinish
            emptyBoundary emptyBoundarySize := by
    rw [hemptyEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount emptyStart 0 emptyFinish
      emptyBoundary emptyBoundarySize
  have htraceSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2, #24, #25, #3,
              #5, #6, #8, #12, #13, #17, #18, #22, #4, #26, #27])
          Empty.elim) compactFormulaTransformTotalExactBoundedGraphDef.val ↔
        CompactFormulaTransformTotalExactBoundedGraph
          tokenTable width tokenCount stateBoundary stateCount mode
          witnessStart witnessFinish witnessCount
          inputBoundary inputCount outputBoundary outputCount emptyBoundary
          binderArity tableWidth valueBound := by
    rw [htraceEnv]
    exact compactFormulaTransformTotalExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount
      inputBoundary inputCount outputBoundary outputCount emptyBoundary
      binderArity tableWidth valueBound
  simp [compactFormulaTransformTotalExactEndpointDef,
    CompactFormulaTransformTotalExactEndpoint,
    hwitnessSpec, hinputSpec, houtputSpec, hemptySpec, htraceSpec]

theorem compactFormulaTransformTotalExactEndpointDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformTotalExactEndpointDef.val := by
  simp [compactFormulaTransformTotalExactEndpointDef]

theorem CompactFormulaTransformTotalExactEndpoint.sound
    {tokenTable width tokenCount mode binderArity
      witnessStart witnessFinish witnessBoundary witnessCount witnessBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      outputStart outputFinish outputBoundary outputCount outputBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      stateBoundary stateCount tableWidth valueBound : Nat}
    (hendpoint : CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount mode binderArity
      witnessStart witnessFinish witnessBoundary witnessCount witnessBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      outputStart outputFinish outputBoundary outputCount outputBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      stateBoundary stateCount tableWidth valueBound) :
    exists witness input output : List Nat,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        witnessStart witnessFinish witness /\
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        inputStart inputFinish input /\
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        outputStart outputFinish output /\
      output =
        (compactExactFormulaTransformResult
          (compactFormulaTransformResult
            (mode, witness) (binderArity, input))).getD [] := by
  rcases hendpoint with
    ⟨hwitnessRows, hinputRows, houtputRows, hemptyRows, htrace⟩
  rcases hwitnessRows.realize with
    ⟨witness, hwitnessCountEq, hwitnessLayout, hwitnessElementRows⟩
  rcases hinputRows.realize with
    ⟨input, hinputCountEq, hinputLayout, hinputElementRows⟩
  rcases houtputRows.realize with
    ⟨output, houtputCountEq, houtputLayout, houtputElementRows⟩
  rcases hemptyRows.realize with
    ⟨empty, hemptyCountEq, hemptyLayout, hemptyElementRows⟩
  have hempty : empty = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using hemptyCountEq
  subst empty
  have htrace' : CompactFormulaTransformTotalExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witness.length
      inputBoundary input.length outputBoundary output.length emptyBoundary
      binderArity tableWidth valueBound := by
    simpa only [hwitnessCountEq, hinputCountEq, houtputCountEq] using htrace
  have hresult := htrace'.sound_selfContained
    hwitnessLayout rfl hinputElementRows houtputElementRows hemptyElementRows
  exact ⟨witness, input, output,
    hwitnessLayout, hinputLayout, houtputLayout, hresult⟩

theorem CompactFormulaTransformTotalExactEndpoint.sound_of_layouts
    {tokenTable width tokenCount mode binderArity
      witnessStart witnessFinish witnessBoundary witnessCount witnessBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      outputStart outputFinish outputBoundary outputCount outputBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      stateBoundary stateCount tableWidth valueBound : Nat}
    {witness input output : List Nat}
    (hendpoint : CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount mode binderArity
      witnessStart witnessFinish witnessBoundary witnessCount witnessBoundarySize
      inputStart inputFinish inputBoundary inputCount inputBoundarySize
      outputStart outputFinish outputBoundary outputCount outputBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      stateBoundary stateCount tableWidth valueBound)
    (hwitness : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      witnessStart witnessFinish witness)
    (hinput : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      inputStart inputFinish input)
    (houtput : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      outputStart outputFinish output) :
    output =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (mode, witness) (binderArity, input))).getD [] := by
  rcases hendpoint.sound with
    ⟨decodedWitness, decodedInput, decodedOutput,
      hdecodedWitness, hdecodedInput, hdecodedOutput, hresult⟩
  have hwitnessEq : witness = decodedWitness :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hdecodedWitness hwitness).1
  have hinputEq : input = decodedInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hdecodedInput hinput).1
  have houtputEq : output = decodedOutput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hdecodedOutput houtput).1
  simpa [hwitnessEq, hinputEq, houtputEq] using hresult

#print axioms compactFormulaTransformTotalExactEndpointDef_spec
#print axioms compactFormulaTransformTotalExactEndpointDef_sigmaZero
#print axioms CompactFormulaTransformTotalExactEndpoint.sound
#print axioms CompactFormulaTransformTotalExactEndpoint.sound_of_layouts

end FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
