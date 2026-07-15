import integration.FoundationCompactNumericListedDirectProofRootClosedFormulaFailureCompleteness
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula

/-!
# Bounded proof-root endpoint for a failed second formula

Tags three and four parse a sequent and then two formulas.  This graph joins a
successful sequent endpoint, a successful first-formula endpoint, and the
complete no-output trace of the second formula in one token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootTwoFormulaFailureBoundedFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectProofRootFailureSemantics
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula

structure CompactProofRootTwoFormulaFailureEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  bodyBoundary : Nat
  bodyCount : Nat
  bodyBoundarySize : Nat
  tag : Nat
  valueStart : Nat
  valueFinish : Nat
  firstStart : Nat
  firstFinish : Nat
  secondStart : Nat
  secondFinish : Nat
  sequentBound : Nat
  firstBound : Nat
  failureBound : Nat

def CompactProofRootTwoFormulaFailureEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootTwoFormulaFailureEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount bodyStart coordinates.bodyCount bodyFinish
        coordinates.bodyBoundary coordinates.bodyBoundarySize ∧
    (coordinates.tag = 3 ∨ coordinates.tag = 4) ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.bodyBoundary coordinates.bodyCount
        coordinates.inputBoundary coordinates.inputCount coordinates.tag ∧
    CompactSequentFormulaEndpointBoundedGraph
      tokenTable width tokenCount bodyStart bodyFinish
        coordinates.valueStart coordinates.valueFinish
        coordinates.firstStart coordinates.firstFinish
        coordinates.sequentBound ∧
    CompactParserSyntaxExactEndpointBoundedGraph
      tokenTable width tokenCount coordinates.firstStart coordinates.firstFinish
        coordinates.secondStart coordinates.secondFinish 1 0 0
        coordinates.firstBound ∧
    CompactParserSyntaxNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount coordinates.secondStart
        coordinates.secondFinish 1 0 0 coordinates.failureBound

def compactProofRootTwoFormulaFailureEndpointGraphDef :
    𝚺₀.Semisentence 23 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
      inputBoundary inputCount inputBoundarySize
      bodyBoundary bodyCount bodyBoundarySize tag
      valueStart valueFinish firstStart firstFinish secondStart secondFinish
      sequentBound firstBound failureBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount bodyStart bodyCount bodyFinish
        bodyBoundary bodyBoundarySize ∧
    (tag = 3 ∨ tag = 4) ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        bodyBoundary bodyCount inputBoundary inputCount tag ∧
    !(compactSequentFormulaEndpointBoundedGraphDef)
      tokenTable width tokenCount bodyStart bodyFinish
        valueStart valueFinish firstStart firstFinish sequentBound ∧
    !(compactParserSyntaxExactEndpointBoundedGraphDef)
      tokenTable width tokenCount firstStart firstFinish
        secondStart secondFinish 1 0 0 firstBound ∧
    !(compactParserSyntaxNoOutputExactEndpointBoundedGraphDef)
      tokenTable width tokenCount secondStart secondFinish
        1 0 0 failureBound”

def compactProofRootTwoFormulaFailureEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootTwoFormulaFailureEndpointCoordinates) :
    Fin 23 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.bodyBoundary, coordinates.bodyCount,
    coordinates.bodyBoundarySize, coordinates.tag,
    coordinates.valueStart, coordinates.valueFinish,
    coordinates.firstStart, coordinates.firstFinish,
    coordinates.secondStart, coordinates.secondFinish,
    coordinates.sequentBound, coordinates.firstBound,
    coordinates.failureBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootTwoFormulaFailureEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootTwoFormulaFailureEndpointCoordinates) :
    compactProofRootTwoFormulaFailureEndpointGraphDef.val.Evalb
        (compactProofRootTwoFormulaFailureEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish coordinates) ↔
      CompactProofRootTwoFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  let env := compactProofRootTwoFormulaFailureEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
      coordinates
  change compactProofRootTwoFormulaFailureEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2, #3, #8, #4, #7, #9]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hbodyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2, #5, #11, #6, #10, #12]) =
        ![tokenTable, width, tokenCount, bodyStart,
          coordinates.bodyCount, bodyFinish,
          coordinates.bodyBoundary, coordinates.bodyBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2, #10, #11, #7, #8, #13]) =
        ![tokenTable, width, tokenCount,
          coordinates.bodyBoundary, coordinates.bodyCount,
          coordinates.inputBoundary, coordinates.inputCount,
          coordinates.tag] := by
    funext index
    fin_cases index <;> rfl
  have hsequentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2, #5, #6,
          #14, #15, #16, #17, #20]) =
        ![tokenTable, width, tokenCount, bodyStart, bodyFinish,
          coordinates.valueStart, coordinates.valueFinish,
          coordinates.firstStart, coordinates.firstFinish,
          coordinates.sequentBound] := by
    funext index
    fin_cases index <;> rfl
  have hfirstEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2, #16, #17,
          #18, #19, ‘1’, ‘0’, ‘0’, #21]) =
        ![tokenTable, width, tokenCount,
          coordinates.firstStart, coordinates.firstFinish,
          coordinates.secondStart, coordinates.secondFinish,
          1, 0, 0, coordinates.firstBound] := by
    dsimp only [env,
      compactProofRootTwoFormulaFailureEndpointEnvironment]
    funext index
    fin_cases index <;> simp
  have hfailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 23), #1, #2, #18, #19,
          ‘1’, ‘0’, ‘0’, #22]) =
        ![tokenTable, width, tokenCount,
          coordinates.secondStart, coordinates.secondFinish,
          1, 0, 0, coordinates.failureBound] := by
    dsimp only [env,
      compactProofRootTwoFormulaFailureEndpointEnvironment]
    funext index
    fin_cases index <;> simp
  have htag : env 13 = coordinates.tag := rfl
  simp [compactProofRootTwoFormulaFailureEndpointGraphDef,
    CompactProofRootTwoFormulaFailureEndpointGraph,
    hinputEnv, hbodyEnv, hconsEnv, hsequentEnv,
    hfirstEnv, hfailureEnv, htag] <;> tauto

theorem compactProofRootTwoFormulaFailureEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootTwoFormulaFailureEndpointGraphDef.val := by
  simp [compactProofRootTwoFormulaFailureEndpointGraphDef]

theorem CompactProofRootTwoFormulaFailureEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootTwoFormulaFailureEndpointCoordinates}
    (hgraph : CompactProofRootTwoFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hgraph with
    ⟨hinputRows, hbodyRows, htag, hconsRows,
      hsequent, hfirst, hfailure⟩
  rcases hinputRows.realize with
    ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
  rcases hbodyRows.realize with
    ⟨body, hbodyCount, hbodyLayout, hbodyElementRows⟩
  rcases hsequent.sound with
    ⟨parsedBody, values, firstInput, hparsedBodyLayout,
      _hvaluesLayout, hfirstInputLayout, hsequentParser⟩
  have hparsedBodyEq : parsedBody = body :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hbodyLayout hparsedBodyLayout).1
  rw [hparsedBodyEq] at hsequentParser
  rcases hfirst.sound_formula with
    ⟨decodedFirstInput, secondInput,
      hdecodedFirstInputLayout, hsecondInputLayout, hfirstParser⟩
  have hdecodedFirstInputEq : decodedFirstInput = firstInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfirstInputLayout hdecodedFirstInputLayout).1
  rw [hdecodedFirstInputEq] at hfirstParser
  rcases hfailure.sound_formula with
    ⟨decodedSecondInput, hdecodedSecondInputLayout, hsecondParser⟩
  have hdecodedSecondInputEq : decodedSecondInput = secondInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hsecondInputLayout hdecodedSecondInputLayout).1
  rw [hdecodedSecondInputEq] at hsecondParser
  let firstValue := consumedTokenPrefix firstInput secondInput
  have hfirstValueParser : compactFormulaTokenValueParser 0 firstInput =
      some (firstValue, secondInput) := by
    simp [compactFormulaTokenValueParser, hfirstParser, firstValue]
  have hsecondValueParser : compactFormulaTokenValueParser 0 secondInput =
      none :=
    (compactFormulaTokenValueParser_eq_none_iff 0 secondInput).mpr
      hsecondParser
  let firstFields : CompactNumericNodeFields :=
    (values, (firstValue, ([], ([], secondInput))))
  have hfirstFields : compactNodeSequentFormulaFields 0 body =
      some firstFields := by
    simp [compactNodeSequentFormulaFields, hsequentParser,
      hfirstValueParser, firstFields]
  have hnodeFailure : compactNodeSequentTwoFormulaFields 0 body = none := by
    simp [compactNodeSequentTwoFormulaFields, hfirstFields,
      compactNumericNodeFieldsSuffix, hsecondValueParser, firstFields]
  have hrootFailure : CompactProofRootFailure
      (coordinates.tag :: body) := by
    rcases htag with htagThree | htagFour
    · rw [htagThree]
      exact .tag3 body hnodeFailure
    · rw [htagFour]
      exact .tag4 body hnodeFailure
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

def compactProofRootTwoFormulaFailureEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      bodyBoundary bodyCount bodyBoundarySize tag
      valueStart valueFinish firstStart firstFinish secondStart secondFinish
      sequentBound firstBound failureBound : Nat) :
    CompactProofRootTwoFormulaFailureEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    bodyBoundary := bodyBoundary
    bodyCount := bodyCount
    bodyBoundarySize := bodyBoundarySize
    tag := tag
    valueStart := valueStart
    valueFinish := valueFinish
    firstStart := firstStart
    firstFinish := firstFinish
    secondStart := secondStart
    secondFinish := secondFinish
    sequentBound := sequentBound
    firstBound := firstBound
    failureBound := failureBound }

def CompactProofRootTwoFormulaFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ bodyBoundary, bodyBoundary ≤ endpointBound ∧
  ∃ bodyCount, bodyCount ≤ endpointBound ∧
  ∃ bodyBoundarySize, bodyBoundarySize ≤ endpointBound ∧
  ∃ tag, tag ≤ endpointBound ∧
  ∃ valueStart, valueStart ≤ endpointBound ∧
  ∃ valueFinish, valueFinish ≤ endpointBound ∧
  ∃ firstStart, firstStart ≤ endpointBound ∧
  ∃ firstFinish, firstFinish ≤ endpointBound ∧
  ∃ secondStart, secondStart ≤ endpointBound ∧
  ∃ secondFinish, secondFinish ≤ endpointBound ∧
  ∃ sequentBound, sequentBound ≤ endpointBound ∧
  ∃ firstBound, firstBound ≤ endpointBound ∧
  ∃ failureBound, failureBound ≤ endpointBound ∧
    CompactProofRootTwoFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish
        (compactProofRootTwoFormulaFailureEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          bodyBoundary bodyCount bodyBoundarySize tag
          valueStart valueFinish firstStart firstFinish
          secondStart secondFinish sequentBound firstBound failureBound)

def compactProofRootTwoFormulaFailureEndpointBoundedGraphDef :
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
    ∃ valueStart <⁺ endpointBound,
    ∃ valueFinish <⁺ endpointBound,
    ∃ firstStart <⁺ endpointBound,
    ∃ firstFinish <⁺ endpointBound,
    ∃ secondStart <⁺ endpointBound,
    ∃ secondFinish <⁺ endpointBound,
    ∃ sequentBound <⁺ endpointBound,
    ∃ firstBound <⁺ endpointBound,
    ∃ failureBound <⁺ endpointBound,
      !(compactProofRootTwoFormulaFailureEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
        inputBoundary inputCount inputBoundarySize
        bodyBoundary bodyCount bodyBoundarySize tag
        valueStart valueFinish firstStart firstFinish secondStart secondFinish
        sequentBound firstBound failureBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootTwoFormulaFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat) :
    compactProofRootTwoFormulaFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          bodyStart, bodyFinish, endpointBound] ↔
      CompactProofRootTwoFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  have hrow
      (failureBound firstBound sequentBound secondFinish secondStart
        firstFinish firstStart valueFinish valueStart tag
        bodyBoundarySize bodyCount bodyBoundary
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![failureBound, firstBound, sequentBound,
                secondFinish, secondStart, firstFinish, firstStart,
                valueFinish, valueStart, tag,
                bodyBoundarySize, bodyCount, bodyBoundary,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                bodyStart, bodyFinish, endpointBound]
              Empty.elim ∘
            ![(#16 : Semiterm ℒₒᵣ Empty 24), #17, #18, #19, #20,
              #21, #22, #15, #14, #13, #12, #11, #10, #9,
              #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactProofRootTwoFormulaFailureEndpointGraphDef.val ↔
      CompactProofRootTwoFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish
          (compactProofRootTwoFormulaFailureEndpointCoordinatesOfValues
            inputBoundary inputCount inputBoundarySize
            bodyBoundary bodyCount bodyBoundarySize tag
            valueStart valueFinish firstStart firstFinish
            secondStart secondFinish sequentBound firstBound failureBound) := by
    have henv :
        (Semiterm.val
            ![failureBound, firstBound, sequentBound,
              secondFinish, secondStart, firstFinish, firstStart,
              valueFinish, valueStart, tag,
              bodyBoundarySize, bodyCount, bodyBoundary,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              bodyStart, bodyFinish, endpointBound]
            Empty.elim ∘
          ![(#16 : Semiterm ℒₒᵣ Empty 24), #17, #18, #19, #20,
            #21, #22, #15, #14, #13, #12, #11, #10, #9,
            #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactProofRootTwoFormulaFailureEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              bodyStart bodyFinish
              (compactProofRootTwoFormulaFailureEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                bodyBoundary bodyCount bodyBoundarySize tag
                valueStart valueFinish firstStart firstFinish
                secondStart secondFinish sequentBound firstBound
                failureBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactProofRootTwoFormulaFailureEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish _
  simp [compactProofRootTwoFormulaFailureEndpointBoundedGraphDef,
    CompactProofRootTwoFormulaFailureEndpointBoundedGraph, hrow]

theorem compactProofRootTwoFormulaFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootTwoFormulaFailureEndpointBoundedGraphDef.val := by
  simp [compactProofRootTwoFormulaFailureEndpointBoundedGraphDef]

theorem CompactProofRootTwoFormulaFailureEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootTwoFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish endpointBound) :
    ∃ coordinates : CompactProofRootTwoFormulaFailureEndpointCoordinates,
      CompactProofRootTwoFormulaFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      bodyBoundary, _, bodyCount, _, bodyBoundarySize, _, tag, _,
      valueStart, _, valueFinish, _, firstStart, _, firstFinish, _,
      secondStart, _, secondFinish, _, sequentBound, _, firstBound, _,
      failureBound, _, hgraph⟩
  exact ⟨compactProofRootTwoFormulaFailureEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    bodyBoundary bodyCount bodyBoundarySize tag
    valueStart valueFinish firstStart firstFinish
    secondStart secondFinish sequentBound firstBound failureBound, hgraph⟩

theorem CompactProofRootTwoFormulaFailureEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootTwoFormulaFailureEndpointCoordinates}
    (hgraph : CompactProofRootTwoFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish coordinates) :
    ∃ endpointBound,
      CompactProofRootTwoFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.bodyBoundary +
    coordinates.bodyCount + coordinates.bodyBoundarySize + coordinates.tag +
    coordinates.valueStart + coordinates.valueFinish +
    coordinates.firstStart + coordinates.firstFinish +
    coordinates.secondStart + coordinates.secondFinish +
    coordinates.sequentBound + coordinates.firstBound +
    coordinates.failureBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactProofRootTwoFormulaFailureEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.bodyBoundary, ?_,
    coordinates.bodyCount, ?_, coordinates.bodyBoundarySize, ?_,
    coordinates.tag, ?_, coordinates.valueStart, ?_,
    coordinates.valueFinish, ?_, coordinates.firstStart, ?_,
    coordinates.firstFinish, ?_, coordinates.secondStart, ?_,
    coordinates.secondFinish, ?_, coordinates.sequentBound, ?_,
    coordinates.firstBound, ?_, coordinates.failureBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactProofRootTwoFormulaFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootTwoFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish endpointBound) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

#print axioms compactProofRootTwoFormulaFailureEndpointGraphDef_spec
#print axioms compactProofRootTwoFormulaFailureEndpointGraphDef_sigmaZero
#print axioms CompactProofRootTwoFormulaFailureEndpointGraph.sound
#print axioms compactProofRootTwoFormulaFailureEndpointBoundedGraphDef_spec
#print axioms compactProofRootTwoFormulaFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactProofRootTwoFormulaFailureEndpointGraph.exists_bounded
#print axioms CompactProofRootTwoFormulaFailureEndpointBoundedGraph.sound

end FoundationCompactNumericListedDirectProofRootTwoFormulaFailureBoundedFormula
