import integration.FoundationCompactNumericListedDirectProofRootSequentFailureCompleteness
import integration.FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint
import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula

/-!
# Bounded proof-root endpoint for a failed trailing formula

Tags zero, three, four, five, six, and nine first parse a sequent and then a
formula.  This graph records a successful sequent endpoint followed by a
complete no-output formula trace on the same outer proof-root input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootOneFormulaFailureBoundedFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectProofRootFailureSemantics
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula
open FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint

structure CompactProofRootOneFormulaFailureEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  bodyBoundary : Nat
  bodyCount : Nat
  bodyBoundarySize : Nat
  tag : Nat
  binderArity : Nat
  valueStart : Nat
  valueFinish : Nat
  finalStart : Nat
  finalFinish : Nat
  sequentBound : Nat
  failureBound : Nat

def CompactProofRootFormulaFailureTagBinder
    (tag binderArity : Nat) : Prop :=
  (((tag = 0 ∨ tag = 3 ∨ tag = 4 ∨ tag = 9) ∧ binderArity = 0) ∨
    ((tag = 5 ∨ tag = 6) ∧ binderArity = 1))

def CompactProofRootOneFormulaFailureEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootOneFormulaFailureEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount bodyStart coordinates.bodyCount bodyFinish
        coordinates.bodyBoundary coordinates.bodyBoundarySize ∧
    CompactProofRootFormulaFailureTagBinder
      coordinates.tag coordinates.binderArity ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.bodyBoundary coordinates.bodyCount
        coordinates.inputBoundary coordinates.inputCount coordinates.tag ∧
    CompactSequentFormulaEndpointBoundedGraph
      tokenTable width tokenCount bodyStart bodyFinish
        coordinates.valueStart coordinates.valueFinish
        coordinates.finalStart coordinates.finalFinish
        coordinates.sequentBound ∧
    CompactParserSyntaxNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount coordinates.finalStart
        coordinates.finalFinish 1 coordinates.binderArity 0
        coordinates.failureBound

def compactProofRootOneFormulaFailureEndpointGraphDef :
    𝚺₀.Semisentence 21 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
      inputBoundary inputCount inputBoundarySize
      bodyBoundary bodyCount bodyBoundarySize tag binderArity
      valueStart valueFinish finalStart finalFinish sequentBound failureBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount bodyStart bodyCount bodyFinish
        bodyBoundary bodyBoundarySize ∧
    (((tag = 0 ∨ tag = 3 ∨ tag = 4 ∨ tag = 9) ∧ binderArity = 0) ∨
      ((tag = 5 ∨ tag = 6) ∧ binderArity = 1)) ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        bodyBoundary bodyCount inputBoundary inputCount tag ∧
    !(compactSequentFormulaEndpointBoundedGraphDef)
      tokenTable width tokenCount bodyStart bodyFinish
        valueStart valueFinish finalStart finalFinish sequentBound ∧
    !(compactParserSyntaxNoOutputExactEndpointBoundedGraphDef)
      tokenTable width tokenCount finalStart finalFinish
        1 binderArity 0 failureBound”

def compactProofRootOneFormulaFailureEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootOneFormulaFailureEndpointCoordinates) :
    Fin 21 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.bodyBoundary, coordinates.bodyCount,
    coordinates.bodyBoundarySize, coordinates.tag,
    coordinates.binderArity, coordinates.valueStart,
    coordinates.valueFinish, coordinates.finalStart,
    coordinates.finalFinish, coordinates.sequentBound,
    coordinates.failureBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootOneFormulaFailureEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootOneFormulaFailureEndpointCoordinates) :
    compactProofRootOneFormulaFailureEndpointGraphDef.val.Evalb
        (compactProofRootOneFormulaFailureEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish coordinates) ↔
      CompactProofRootOneFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  let env := compactProofRootOneFormulaFailureEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish coordinates
  change compactProofRootOneFormulaFailureEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #3, #8, #4, #7, #9]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hbodyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #5, #11, #6, #10, #12]) =
        ![tokenTable, width, tokenCount, bodyStart,
          coordinates.bodyCount, bodyFinish,
          coordinates.bodyBoundary, coordinates.bodyBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #10, #11, #7, #8, #13]) =
        ![tokenTable, width, tokenCount,
          coordinates.bodyBoundary, coordinates.bodyCount,
          coordinates.inputBoundary, coordinates.inputCount,
          coordinates.tag] := by
    funext index
    fin_cases index <;> rfl
  have hsequentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #5, #6,
          #15, #16, #17, #18, #19]) =
        ![tokenTable, width, tokenCount, bodyStart, bodyFinish,
          coordinates.valueStart, coordinates.valueFinish,
          coordinates.finalStart, coordinates.finalFinish,
          coordinates.sequentBound] := by
    funext index
    fin_cases index <;> rfl
  have hfailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 21), #1, #2, #17, #18,
          ‘1’, #14, ‘0’, #20]) =
        ![tokenTable, width, tokenCount,
          coordinates.finalStart, coordinates.finalFinish,
          1, coordinates.binderArity, 0, coordinates.failureBound] := by
    dsimp only [env,
      compactProofRootOneFormulaFailureEndpointEnvironment]
    funext index
    fin_cases index <;> simp
  have htag : env 13 = coordinates.tag := rfl
  have hbinder : env 14 = coordinates.binderArity := rfl
  simp [compactProofRootOneFormulaFailureEndpointGraphDef,
    CompactProofRootOneFormulaFailureEndpointGraph,
    CompactProofRootFormulaFailureTagBinder,
    hinputEnv, hbodyEnv, hconsEnv, hsequentEnv, hfailureEnv,
    htag, hbinder] <;> tauto

theorem compactProofRootOneFormulaFailureEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootOneFormulaFailureEndpointGraphDef.val := by
  simp [compactProofRootOneFormulaFailureEndpointGraphDef]

theorem CompactProofRootOneFormulaFailureEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootOneFormulaFailureEndpointCoordinates}
    (hgraph : CompactProofRootOneFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hgraph with
    ⟨hinputRows, hbodyRows, htagBinder, hconsRows,
      hsequent, hfailure⟩
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
    ⟨failureInput, hfailureInputLayout, hformulaParser⟩
  have hfailureInputEq : failureInput = suffix :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hsuffixLayout hfailureInputLayout).1
  rw [hfailureInputEq] at hformulaParser
  have hformulaValueParser : compactFormulaTokenValueParser
      coordinates.binderArity suffix = none :=
    (compactFormulaTokenValueParser_eq_none_iff
      coordinates.binderArity suffix).mpr hformulaParser
  have hnodeFailure : compactNodeSequentFormulaFields
      coordinates.binderArity body = none := by
    simp [compactNodeSequentFormulaFields, hsequentParser,
      hformulaValueParser]
  have hrootFailure : CompactProofRootFailure
      (coordinates.tag :: body) := by
    rcases htagBinder with hzeroArityCase | honeArityCase
    · rcases hzeroArityCase with ⟨htags, hbinder⟩
      rw [hbinder] at hnodeFailure
      rcases htags with htagZero | htagThree | htagFour | htagNine
      · rw [htagZero]
        exact .tag0 body hnodeFailure
      · rw [htagThree]
        exact .tag3 body (by
          simp [compactNodeSequentTwoFormulaFields, hnodeFailure])
      · rw [htagFour]
        exact .tag4 body (by
          simp [compactNodeSequentTwoFormulaFields, hnodeFailure])
      · rw [htagNine]
        exact .tag9 body hnodeFailure
    · rcases honeArityCase with ⟨htags, hbinder⟩
      rw [hbinder] at hnodeFailure
      rcases htags with htagFive | htagSix
      · rw [htagFive]
        exact .tag5 body hnodeFailure
      · rw [htagSix]
        exact .tag6 body (by
          simp [compactNodeSequentFormulaTermFields, hnodeFailure])
  have hconsRows' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.bodyBoundary body.length
        coordinates.inputBoundary input.length coordinates.tag := by
    simpa only [hinputCount, hbodyCount] using hconsRows
  have hinputEq : input = coordinates.tag :: body :=
    hconsRows'.eq_cons_of_rows hbodyElementRows hinputElementRows
  have hparser : compactListedProofNodeFieldsParser
      (coordinates.tag :: body) = none :=
    (compactListedProofNodeFieldsParser_eq_none_iff
      (coordinates.tag :: body)).mpr hrootFailure
  exact ⟨input, hinputLayout, by simpa only [hinputEq] using hparser⟩

def compactProofRootOneFormulaFailureEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      bodyBoundary bodyCount bodyBoundarySize tag binderArity
      valueStart valueFinish finalStart finalFinish
      sequentBound failureBound : Nat) :
    CompactProofRootOneFormulaFailureEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    bodyBoundary := bodyBoundary
    bodyCount := bodyCount
    bodyBoundarySize := bodyBoundarySize
    tag := tag
    binderArity := binderArity
    valueStart := valueStart
    valueFinish := valueFinish
    finalStart := finalStart
    finalFinish := finalFinish
    sequentBound := sequentBound
    failureBound := failureBound }

def CompactProofRootOneFormulaFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ bodyBoundary, bodyBoundary ≤ endpointBound ∧
  ∃ bodyCount, bodyCount ≤ endpointBound ∧
  ∃ bodyBoundarySize, bodyBoundarySize ≤ endpointBound ∧
  ∃ tag, tag ≤ endpointBound ∧
  ∃ binderArity, binderArity ≤ endpointBound ∧
  ∃ valueStart, valueStart ≤ endpointBound ∧
  ∃ valueFinish, valueFinish ≤ endpointBound ∧
  ∃ finalStart, finalStart ≤ endpointBound ∧
  ∃ finalFinish, finalFinish ≤ endpointBound ∧
  ∃ sequentBound, sequentBound ≤ endpointBound ∧
  ∃ failureBound, failureBound ≤ endpointBound ∧
    CompactProofRootOneFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish
        (compactProofRootOneFormulaFailureEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          bodyBoundary bodyCount bodyBoundarySize tag binderArity
          valueStart valueFinish finalStart finalFinish
          sequentBound failureBound)

def compactProofRootOneFormulaFailureEndpointBoundedGraphDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
      endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ bodyBoundary <⁺ endpointBound,
    ∃ bodyCount <⁺ endpointBound,
    ∃ bodyBoundarySize <⁺ endpointBound,
    ∃ tag <⁺ endpointBound,
    ∃ binderArity <⁺ endpointBound,
    ∃ valueStart <⁺ endpointBound,
    ∃ valueFinish <⁺ endpointBound,
    ∃ finalStart <⁺ endpointBound,
    ∃ finalFinish <⁺ endpointBound,
    ∃ sequentBound <⁺ endpointBound,
    ∃ failureBound <⁺ endpointBound,
      !(compactProofRootOneFormulaFailureEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
        inputBoundary inputCount inputBoundarySize
        bodyBoundary bodyCount bodyBoundarySize tag binderArity
        valueStart valueFinish finalStart finalFinish
        sequentBound failureBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootOneFormulaFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat) :
    compactProofRootOneFormulaFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          bodyStart, bodyFinish, endpointBound] ↔
      CompactProofRootOneFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  have hrow
      (failureBound sequentBound finalFinish finalStart
        valueFinish valueStart binderArity tag
        bodyBoundarySize bodyCount bodyBoundary
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![failureBound, sequentBound, finalFinish, finalStart,
                valueFinish, valueStart, binderArity, tag,
                bodyBoundarySize, bodyCount, bodyBoundary,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                bodyStart, bodyFinish, endpointBound]
              Empty.elim ∘
            ![(#14 : Semiterm ℒₒᵣ Empty 22), #15, #16, #17, #18,
              #19, #20, #13, #12, #11, #10, #9, #8,
              #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactProofRootOneFormulaFailureEndpointGraphDef.val ↔
      CompactProofRootOneFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish
          (compactProofRootOneFormulaFailureEndpointCoordinatesOfValues
            inputBoundary inputCount inputBoundarySize
            bodyBoundary bodyCount bodyBoundarySize tag binderArity
            valueStart valueFinish finalStart finalFinish
            sequentBound failureBound) := by
    have henv :
        (Semiterm.val
            ![failureBound, sequentBound, finalFinish, finalStart,
              valueFinish, valueStart, binderArity, tag,
              bodyBoundarySize, bodyCount, bodyBoundary,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              bodyStart, bodyFinish, endpointBound]
            Empty.elim ∘
          ![(#14 : Semiterm ℒₒᵣ Empty 22), #15, #16, #17, #18,
            #19, #20, #13, #12, #11, #10, #9, #8,
            #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactProofRootOneFormulaFailureEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              bodyStart bodyFinish
              (compactProofRootOneFormulaFailureEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                bodyBoundary bodyCount bodyBoundarySize tag binderArity
                valueStart valueFinish finalStart finalFinish
                sequentBound failureBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactProofRootOneFormulaFailureEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish _
  simp [compactProofRootOneFormulaFailureEndpointBoundedGraphDef,
    CompactProofRootOneFormulaFailureEndpointBoundedGraph, hrow]

theorem compactProofRootOneFormulaFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootOneFormulaFailureEndpointBoundedGraphDef.val := by
  simp [compactProofRootOneFormulaFailureEndpointBoundedGraphDef]

theorem CompactProofRootOneFormulaFailureEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootOneFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish endpointBound) :
    ∃ coordinates : CompactProofRootOneFormulaFailureEndpointCoordinates,
      CompactProofRootOneFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      bodyBoundary, _, bodyCount, _, bodyBoundarySize, _,
      tag, _, binderArity, _, valueStart, _, valueFinish, _,
      finalStart, _, finalFinish, _, sequentBound, _, failureBound, _, hgraph⟩
  exact ⟨compactProofRootOneFormulaFailureEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    bodyBoundary bodyCount bodyBoundarySize tag binderArity
    valueStart valueFinish finalStart finalFinish
    sequentBound failureBound, hgraph⟩

theorem CompactProofRootOneFormulaFailureEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootOneFormulaFailureEndpointCoordinates}
    (hgraph : CompactProofRootOneFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish coordinates) :
    ∃ endpointBound,
      CompactProofRootOneFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.bodyBoundary +
    coordinates.bodyCount + coordinates.bodyBoundarySize +
    coordinates.tag + coordinates.binderArity + coordinates.valueStart +
    coordinates.valueFinish + coordinates.finalStart +
    coordinates.finalFinish + coordinates.sequentBound +
    coordinates.failureBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactProofRootOneFormulaFailureEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.bodyBoundary, ?_,
    coordinates.bodyCount, ?_, coordinates.bodyBoundarySize, ?_,
    coordinates.tag, ?_, coordinates.binderArity, ?_,
    coordinates.valueStart, ?_, coordinates.valueFinish, ?_,
    coordinates.finalStart, ?_, coordinates.finalFinish, ?_,
    coordinates.sequentBound, ?_, coordinates.failureBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactProofRootOneFormulaFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootOneFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish endpointBound) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

#print axioms compactProofRootOneFormulaFailureEndpointGraphDef_spec
#print axioms compactProofRootOneFormulaFailureEndpointGraphDef_sigmaZero
#print axioms CompactProofRootOneFormulaFailureEndpointGraph.sound
#print axioms compactProofRootOneFormulaFailureEndpointBoundedGraphDef_spec
#print axioms compactProofRootOneFormulaFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactProofRootOneFormulaFailureEndpointGraph.exists_bounded
#print axioms CompactProofRootOneFormulaFailureEndpointBoundedGraph.sound

end FoundationCompactNumericListedDirectProofRootOneFormulaFailureBoundedFormula
