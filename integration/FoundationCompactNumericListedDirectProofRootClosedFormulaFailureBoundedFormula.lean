import integration.FoundationCompactNumericListedDirectProofRootOneFormulaFailureCompleteness
import integration.FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointFormula

/-!
# Bounded proof-root endpoint for a failed closed formula

Tag one parses a sequent followed by a closed formula.  Its second parser may
fail specifically because of free variables, so this endpoint uses the exact
closed-parser no-output relation rather than the ordinary formula relation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootClosedFormulaFailureBoundedFormula

open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectProofRootFailureSemantics
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointFormula

structure CompactProofRootClosedFormulaFailureEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  bodyBoundary : Nat
  bodyCount : Nat
  bodyBoundarySize : Nat
  valueStart : Nat
  valueFinish : Nat
  finalStart : Nat
  finalFinish : Nat
  sequentBound : Nat
  failureBound : Nat

def CompactProofRootClosedFormulaFailureEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootClosedFormulaFailureEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount bodyStart coordinates.bodyCount bodyFinish
        coordinates.bodyBoundary coordinates.bodyBoundarySize ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.bodyBoundary coordinates.bodyCount
        coordinates.inputBoundary coordinates.inputCount 1 ∧
    CompactSequentFormulaEndpointBoundedGraph
      tokenTable width tokenCount bodyStart bodyFinish
        coordinates.valueStart coordinates.valueFinish
        coordinates.finalStart coordinates.finalFinish
        coordinates.sequentBound ∧
    CompactParserClosedNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount coordinates.finalStart
        coordinates.finalFinish 1 0 0 coordinates.failureBound

def compactProofRootClosedFormulaFailureEndpointGraphDef :
    𝚺₀.Semisentence 19 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
      inputBoundary inputCount inputBoundarySize
      bodyBoundary bodyCount bodyBoundarySize
      valueStart valueFinish finalStart finalFinish sequentBound failureBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount bodyStart bodyCount bodyFinish
        bodyBoundary bodyBoundarySize ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        bodyBoundary bodyCount inputBoundary inputCount 1 ∧
    !(compactSequentFormulaEndpointBoundedGraphDef)
      tokenTable width tokenCount bodyStart bodyFinish
        valueStart valueFinish finalStart finalFinish sequentBound ∧
    !(compactParserClosedNoOutputExactEndpointBoundedGraphDef)
      tokenTable width tokenCount finalStart finalFinish 1 0 0 failureBound”

def compactProofRootClosedFormulaFailureEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootClosedFormulaFailureEndpointCoordinates) :
    Fin 19 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.bodyBoundary, coordinates.bodyCount,
    coordinates.bodyBoundarySize, coordinates.valueStart,
    coordinates.valueFinish, coordinates.finalStart,
    coordinates.finalFinish, coordinates.sequentBound,
    coordinates.failureBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootClosedFormulaFailureEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootClosedFormulaFailureEndpointCoordinates) :
    compactProofRootClosedFormulaFailureEndpointGraphDef.val.Evalb
        (compactProofRootClosedFormulaFailureEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish coordinates) ↔
      CompactProofRootClosedFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  let env := compactProofRootClosedFormulaFailureEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish coordinates
  change compactProofRootClosedFormulaFailureEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #3, #8, #4, #7, #9]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hbodyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #5, #11, #6, #10, #12]) =
        ![tokenTable, width, tokenCount, bodyStart,
          coordinates.bodyCount, bodyFinish,
          coordinates.bodyBoundary, coordinates.bodyBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #10, #11, #7, #8, ‘1’]) =
        ![tokenTable, width, tokenCount,
          coordinates.bodyBoundary, coordinates.bodyCount,
          coordinates.inputBoundary, coordinates.inputCount, 1] := by
    dsimp only [env,
      compactProofRootClosedFormulaFailureEndpointEnvironment]
    funext index
    fin_cases index <;> simp
  have hsequentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #5, #6,
          #13, #14, #15, #16, #17]) =
        ![tokenTable, width, tokenCount, bodyStart, bodyFinish,
          coordinates.valueStart, coordinates.valueFinish,
          coordinates.finalStart, coordinates.finalFinish,
          coordinates.sequentBound] := by
    funext index
    fin_cases index <;> rfl
  have hfailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #15, #16,
          ‘1’, ‘0’, ‘0’, #18]) =
        ![tokenTable, width, tokenCount,
          coordinates.finalStart, coordinates.finalFinish,
          1, 0, 0, coordinates.failureBound] := by
    dsimp only [env,
      compactProofRootClosedFormulaFailureEndpointEnvironment]
    funext index
    fin_cases index <;> simp
  simp [compactProofRootClosedFormulaFailureEndpointGraphDef,
    CompactProofRootClosedFormulaFailureEndpointGraph,
    hinputEnv, hbodyEnv, hconsEnv, hsequentEnv, hfailureEnv]

theorem compactProofRootClosedFormulaFailureEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootClosedFormulaFailureEndpointGraphDef.val := by
  simp [compactProofRootClosedFormulaFailureEndpointGraphDef]

theorem CompactProofRootClosedFormulaFailureEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootClosedFormulaFailureEndpointCoordinates}
    (hgraph : CompactProofRootClosedFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hgraph with
    ⟨hinputRows, hbodyRows, hconsRows, hsequent, hfailure⟩
  rcases hinputRows.realize with
    ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
  rcases hbodyRows.realize with
    ⟨body, hbodyCount, hbodyLayout, hbodyElementRows⟩
  rcases hsequent.sound with
    ⟨parsedBody, values, suffix, hparsedBodyLayout,
      _hvaluesLayout, hsuffixLayout, hsequentParser⟩
  have hparsedBodyEq : parsedBody = body :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hbodyLayout hparsedBodyLayout).1
  rw [hparsedBodyEq] at hsequentParser
  rcases hfailure.sound_formula with
    ⟨failureInput, hfailureInputLayout, hclosedParser⟩
  have hfailureInputEq : failureInput = suffix :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hsuffixLayout hfailureInputLayout).1
  rw [hfailureInputEq] at hclosedParser
  have hclosedValueParser : compactClosedFormulaTokenValueParser
      suffix = none :=
    (compactClosedFormulaTokenValueParser_eq_none_iff suffix).mpr
      hclosedParser
  have hnodeFailure : compactNodeSequentClosedFormulaFields body = none := by
    simp [compactNodeSequentClosedFormulaFields, hsequentParser,
      hclosedValueParser]
  have hrootFailure : CompactProofRootFailure (1 :: body) :=
    .tag1 body hnodeFailure
  have hconsRows' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.bodyBoundary body.length
        coordinates.inputBoundary input.length 1 := by
    simpa only [hinputCount, hbodyCount] using hconsRows
  have hinputEq : input = 1 :: body :=
    hconsRows'.eq_cons_of_rows hbodyElementRows hinputElementRows
  have hparser : compactListedProofNodeFieldsParser (1 :: body) = none :=
    (compactListedProofNodeFieldsParser_eq_none_iff (1 :: body)).mpr
      hrootFailure
  exact ⟨input, hinputLayout, by simpa only [hinputEq] using hparser⟩

def compactProofRootClosedFormulaFailureEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      bodyBoundary bodyCount bodyBoundarySize
      valueStart valueFinish finalStart finalFinish
      sequentBound failureBound : Nat) :
    CompactProofRootClosedFormulaFailureEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    bodyBoundary := bodyBoundary
    bodyCount := bodyCount
    bodyBoundarySize := bodyBoundarySize
    valueStart := valueStart
    valueFinish := valueFinish
    finalStart := finalStart
    finalFinish := finalFinish
    sequentBound := sequentBound
    failureBound := failureBound }

def CompactProofRootClosedFormulaFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ bodyBoundary, bodyBoundary ≤ endpointBound ∧
  ∃ bodyCount, bodyCount ≤ endpointBound ∧
  ∃ bodyBoundarySize, bodyBoundarySize ≤ endpointBound ∧
  ∃ valueStart, valueStart ≤ endpointBound ∧
  ∃ valueFinish, valueFinish ≤ endpointBound ∧
  ∃ finalStart, finalStart ≤ endpointBound ∧
  ∃ finalFinish, finalFinish ≤ endpointBound ∧
  ∃ sequentBound, sequentBound ≤ endpointBound ∧
  ∃ failureBound, failureBound ≤ endpointBound ∧
    CompactProofRootClosedFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish
        (compactProofRootClosedFormulaFailureEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          bodyBoundary bodyCount bodyBoundarySize
          valueStart valueFinish finalStart finalFinish
          sequentBound failureBound)

def compactProofRootClosedFormulaFailureEndpointBoundedGraphDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
      endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ bodyBoundary <⁺ endpointBound,
    ∃ bodyCount <⁺ endpointBound,
    ∃ bodyBoundarySize <⁺ endpointBound,
    ∃ valueStart <⁺ endpointBound,
    ∃ valueFinish <⁺ endpointBound,
    ∃ finalStart <⁺ endpointBound,
    ∃ finalFinish <⁺ endpointBound,
    ∃ sequentBound <⁺ endpointBound,
    ∃ failureBound <⁺ endpointBound,
      !(compactProofRootClosedFormulaFailureEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
        inputBoundary inputCount inputBoundarySize
        bodyBoundary bodyCount bodyBoundarySize
        valueStart valueFinish finalStart finalFinish
        sequentBound failureBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootClosedFormulaFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat) :
    compactProofRootClosedFormulaFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          bodyStart, bodyFinish, endpointBound] ↔
      CompactProofRootClosedFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  have hrow
      (failureBound sequentBound finalFinish finalStart
        valueFinish valueStart bodyBoundarySize bodyCount bodyBoundary
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![failureBound, sequentBound, finalFinish, finalStart,
                valueFinish, valueStart, bodyBoundarySize, bodyCount,
                bodyBoundary, inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                bodyStart, bodyFinish, endpointBound]
              Empty.elim ∘
            ![(#12 : Semiterm ℒₒᵣ Empty 20), #13, #14, #15, #16,
              #17, #18, #11, #10, #9, #8, #7,
              #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactProofRootClosedFormulaFailureEndpointGraphDef.val ↔
      CompactProofRootClosedFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish
          (compactProofRootClosedFormulaFailureEndpointCoordinatesOfValues
            inputBoundary inputCount inputBoundarySize
            bodyBoundary bodyCount bodyBoundarySize
            valueStart valueFinish finalStart finalFinish
            sequentBound failureBound) := by
    have henv :
        (Semiterm.val
            ![failureBound, sequentBound, finalFinish, finalStart,
              valueFinish, valueStart, bodyBoundarySize, bodyCount,
              bodyBoundary, inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              bodyStart, bodyFinish, endpointBound]
            Empty.elim ∘
          ![(#12 : Semiterm ℒₒᵣ Empty 20), #13, #14, #15, #16,
            #17, #18, #11, #10, #9, #8, #7,
            #6, #5, #4, #3, #2, #1, #0]) =
          compactProofRootClosedFormulaFailureEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              bodyStart bodyFinish
              (compactProofRootClosedFormulaFailureEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                bodyBoundary bodyCount bodyBoundarySize
                valueStart valueFinish finalStart finalFinish
                sequentBound failureBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactProofRootClosedFormulaFailureEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish _
  simp [compactProofRootClosedFormulaFailureEndpointBoundedGraphDef,
    CompactProofRootClosedFormulaFailureEndpointBoundedGraph, hrow]

theorem compactProofRootClosedFormulaFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootClosedFormulaFailureEndpointBoundedGraphDef.val := by
  simp [compactProofRootClosedFormulaFailureEndpointBoundedGraphDef]

theorem CompactProofRootClosedFormulaFailureEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootClosedFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish endpointBound) :
    ∃ coordinates : CompactProofRootClosedFormulaFailureEndpointCoordinates,
      CompactProofRootClosedFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      bodyBoundary, _, bodyCount, _, bodyBoundarySize, _,
      valueStart, _, valueFinish, _, finalStart, _, finalFinish, _,
      sequentBound, _, failureBound, _, hgraph⟩
  exact ⟨compactProofRootClosedFormulaFailureEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    bodyBoundary bodyCount bodyBoundarySize
    valueStart valueFinish finalStart finalFinish
    sequentBound failureBound, hgraph⟩

theorem CompactProofRootClosedFormulaFailureEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootClosedFormulaFailureEndpointCoordinates}
    (hgraph : CompactProofRootClosedFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish coordinates) :
    ∃ endpointBound,
      CompactProofRootClosedFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.bodyBoundary +
    coordinates.bodyCount + coordinates.bodyBoundarySize +
    coordinates.valueStart + coordinates.valueFinish +
    coordinates.finalStart + coordinates.finalFinish +
    coordinates.sequentBound + coordinates.failureBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactProofRootClosedFormulaFailureEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.bodyBoundary, ?_,
    coordinates.bodyCount, ?_, coordinates.bodyBoundarySize, ?_,
    coordinates.valueStart, ?_, coordinates.valueFinish, ?_,
    coordinates.finalStart, ?_, coordinates.finalFinish, ?_,
    coordinates.sequentBound, ?_, coordinates.failureBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactProofRootClosedFormulaFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootClosedFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish endpointBound) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

#print axioms compactProofRootClosedFormulaFailureEndpointGraphDef_spec
#print axioms compactProofRootClosedFormulaFailureEndpointGraphDef_sigmaZero
#print axioms CompactProofRootClosedFormulaFailureEndpointGraph.sound
#print axioms compactProofRootClosedFormulaFailureEndpointBoundedGraphDef_spec
#print axioms compactProofRootClosedFormulaFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactProofRootClosedFormulaFailureEndpointGraph.exists_bounded
#print axioms CompactProofRootClosedFormulaFailureEndpointBoundedGraph.sound

end FoundationCompactNumericListedDirectProofRootClosedFormulaFailureBoundedFormula
