import integration.FoundationCompactNumericListedDirectSequentFormulaFailureBoundedFormula

/-!
# Total bounded arithmetic endpoint for sequent-parser no-output

The public parser returns `none` either because its input is empty or because
one of the requested formula parses is the first failed call.  Both cases are
represented by one Delta-zero formula with one public witness bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaNoOutputBoundedFormula

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectSequentFormulaFailureBoundedFormula

def CompactSequentFormulaNoOutputEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    Prop :=
  (∃ inputBoundary, inputBoundary ≤ endpointBound ∧
   ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart 0 inputFinish
        inputBoundary inputBoundarySize) ∨
  CompactSequentFormulaFailureEndpointBoundedGraph
    tokenTable width tokenCount inputStart inputFinish endpointBound

def compactSequentFormulaNoOutputEndpointBoundedGraphDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish endpointBound.
    (∃ inputBoundary <⁺ endpointBound,
     ∃ inputBoundarySize <⁺ endpointBound,
      !(compactAdditiveNatListWitnessRowsDef)
        tokenTable width tokenCount inputStart 0 inputFinish
        inputBoundary inputBoundarySize) ∨
    !(compactSequentFormulaFailureEndpointBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish endpointBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactSequentFormulaNoOutputEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    compactSequentFormulaNoOutputEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound] ↔
      CompactSequentFormulaNoOutputEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  have hemptyRow (inputBoundarySize inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![inputBoundarySize, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#2 : Semiterm ℒₒᵣ Empty 8), #3, #4, #5,
              ‘0’, #6, #1, #0])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount inputStart 0 inputFinish
            inputBoundary inputBoundarySize := by
    have henv :
        (Semiterm.val
            ![inputBoundarySize, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              endpointBound]
            Empty.elim ∘
          ![(#2 : Semiterm ℒₒᵣ Empty 8), #3, #4, #5,
            ‘0’, #6, #1, #0]) =
          ![tokenTable, width, tokenCount, inputStart, 0, inputFinish,
            inputBoundary, inputBoundarySize] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount inputStart 0 inputFinish
        inputBoundary inputBoundarySize
  have hfailureEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount, inputStart, inputFinish,
            endpointBound]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 6), #1, #2, #3, #4, #5]) =
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactSequentFormulaNoOutputEndpointBoundedGraphDef,
    CompactSequentFormulaNoOutputEndpointBoundedGraph,
    hemptyRow, hfailureEnv]

theorem compactSequentFormulaNoOutputEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSequentFormulaNoOutputEndpointBoundedGraphDef.val := by
  simp [compactSequentFormulaNoOutputEndpointBoundedGraphDef]

theorem CompactSequentFormulaNoOutputEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hgraph : CompactSequentFormulaNoOutputEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactSequentTokenValueParser input = none := by
  rcases hgraph with
    (⟨inputBoundary, _hinputBoundary,
      inputBoundarySize, _hinputBoundarySize, hinputWitness⟩ | hfailure)
  · rcases hinputWitness.realize with
      ⟨input, hinputCount, hinputLayout, _hinputRows⟩
    have hinputEq : input = [] :=
      List.eq_nil_of_length_eq_zero hinputCount
    subst input
    exact ⟨[], hinputLayout, by simp [compactSequentTokenValueParser]⟩
  · exact hfailure.sound

theorem exists_compactSequentFormulaNoOutputEndpointBoundedGraph_of_none
    {input : List Nat}
    (hparser : compactSequentTokenValueParser input = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactSequentFormulaNoOutputEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  cases input with
  | nil =>
      let inputTokens := compactAdditiveEncode ([] : List Nat)
      let width := (compactBinaryNatPayloadBits inputTokens).length
      let tokenTable := compactFixedWidthTableCode width inputTokens
      have hinputRaw := compactAdditiveNatListDirectLayout_canonical
        [] ([] : List Nat) []
      dsimp only at hinputRaw
      have htokenEq : [] ++ compactAdditiveEncode ([] : List Nat) ++ [] =
          inputTokens := by
        simp [inputTokens]
      rw [htokenEq] at hinputRaw
      have hinputLayout : CompactAdditiveNatListDirectLayout
          tokenTable width inputTokens.length 0 inputTokens.length [] := by
        simpa only [tokenTable, width, List.length_nil, Nat.zero_add,
          inputTokens] using hinputRaw
      rcases hinputLayout with
        ⟨inputBoundary, hinputStructure, hinputRows, hinputSize⟩
      have hinputWitness : CompactAdditiveNatListWitnessRows
          tokenTable width inputTokens.length 0 0 inputTokens.length
            inputBoundary (Nat.size inputBoundary) :=
        ⟨hinputStructure,
          CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
            hinputRows,
          rfl, hinputSize⟩
      let endpointBound := inputBoundary + Nat.size inputBoundary
      refine ⟨tokenTable, width, inputTokens.length, 0,
        inputTokens.length, endpointBound, Or.inl ?_⟩
      exact ⟨inputBoundary, by dsimp [endpointBound]; omega,
        Nat.size inputBoundary, by dsimp [endpointBound]; omega,
        hinputWitness⟩
  | cons count inputTail =>
      rcases
          exists_compactSequentFormulaFailureEndpointBoundedGraph_of_cons_none
            count inputTail hparser with
        ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound, hfailure⟩
      exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        endpointBound, Or.inr hfailure⟩

#print axioms compactSequentFormulaNoOutputEndpointBoundedGraphDef_spec
#print axioms compactSequentFormulaNoOutputEndpointBoundedGraphDef_sigmaZero
#print axioms CompactSequentFormulaNoOutputEndpointBoundedGraph.sound
#print axioms exists_compactSequentFormulaNoOutputEndpointBoundedGraph_of_none

end FoundationCompactNumericListedDirectSequentFormulaNoOutputBoundedFormula
