import integration.FoundationCompactNumericListedDirectProofRootOuterFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectSequentFormulaNoOutputBoundedFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

/-!
# Bounded proof-root endpoint for a failed sequent parser

Every valid proof-root tag first parses a sequent from the tag tail.  This
endpoint keeps the whole input, its exact tail, and the complete sequent
no-output graph in one fixed-width token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootSequentFailureBoundedFormula

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectProofRootFailureSemantics
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectSequentFormulaNoOutputBoundedFormula

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

structure CompactProofRootSequentFailureEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  bodyBoundary : Nat
  bodyCount : Nat
  bodyBoundarySize : Nat
  tag : Nat
  sequentBound : Nat

def CompactProofRootSequentFailureEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootSequentFailureEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount bodyStart coordinates.bodyCount bodyFinish
        coordinates.bodyBoundary coordinates.bodyBoundarySize ∧
    coordinates.tag ≤ 9 ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.bodyBoundary coordinates.bodyCount
        coordinates.inputBoundary coordinates.inputCount coordinates.tag ∧
    CompactSequentFormulaNoOutputEndpointBoundedGraph
      tokenTable width tokenCount bodyStart bodyFinish
        coordinates.sequentBound

def compactProofRootSequentFailureEndpointGraphDef :
    𝚺₀.Semisentence 15 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
      inputBoundary inputCount inputBoundarySize
      bodyBoundary bodyCount bodyBoundarySize tag sequentBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount bodyStart bodyCount bodyFinish
        bodyBoundary bodyBoundarySize ∧
    tag ≤ 9 ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        bodyBoundary bodyCount inputBoundary inputCount tag ∧
    !(compactSequentFormulaNoOutputEndpointBoundedGraphDef)
      tokenTable width tokenCount bodyStart bodyFinish sequentBound”

def compactProofRootSequentFailureEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootSequentFailureEndpointCoordinates) :
    Fin 15 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.bodyBoundary, coordinates.bodyCount,
    coordinates.bodyBoundarySize, coordinates.tag,
    coordinates.sequentBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootSequentFailureEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat)
    (coordinates : CompactProofRootSequentFailureEndpointCoordinates) :
    compactProofRootSequentFailureEndpointGraphDef.val.Evalb
        (compactProofRootSequentFailureEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish coordinates) ↔
      CompactProofRootSequentFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  let env := compactProofRootSequentFailureEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish coordinates
  change compactProofRootSequentFailureEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2, #3, #8, #4, #7, #9]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hbodyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2, #5, #11, #6, #10, #12]) =
        ![tokenTable, width, tokenCount, bodyStart,
          coordinates.bodyCount, bodyFinish,
          coordinates.bodyBoundary, coordinates.bodyBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2, #10, #11, #7, #8, #13]) =
        ![tokenTable, width, tokenCount,
          coordinates.bodyBoundary, coordinates.bodyCount,
          coordinates.inputBoundary, coordinates.inputCount,
          coordinates.tag] := by
    funext index
    fin_cases index <;> rfl
  have hsequentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2, #5, #6, #14]) =
        ![tokenTable, width, tokenCount, bodyStart, bodyFinish,
          coordinates.sequentBound] := by
    funext index
    fin_cases index <;> rfl
  have htag : env 13 = coordinates.tag := rfl
  simp [compactProofRootSequentFailureEndpointGraphDef,
    CompactProofRootSequentFailureEndpointGraph,
    hinputEnv, hbodyEnv, hconsEnv, hsequentEnv, htag]

theorem compactProofRootSequentFailureEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootSequentFailureEndpointGraphDef.val := by
  simp [compactProofRootSequentFailureEndpointGraphDef]

theorem CompactProofRootSequentFailureEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootSequentFailureEndpointCoordinates}
    (hgraph : CompactProofRootSequentFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hgraph with
    ⟨hinputRows, hbodyRows, htag, hconsRows, hsequent⟩
  rcases hinputRows.realize with
    ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
  rcases hbodyRows.realize with
    ⟨body, hbodyCount, hbodyLayout, hbodyElementRows⟩
  rcases hsequent.sound with
    ⟨parsedBody, hparsedBodyLayout, hsequentParser⟩
  have hparsedBodyEq : parsedBody = body :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hbodyLayout hparsedBodyLayout).1
  rw [hparsedBodyEq] at hsequentParser
  have hconsRows' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.bodyBoundary body.length
        coordinates.inputBoundary input.length coordinates.tag := by
    simpa only [hinputCount, hbodyCount] using hconsRows
  have hinputEq : input = coordinates.tag :: body :=
    hconsRows'.eq_cons_of_rows hbodyElementRows hinputElementRows
  have hfailure : CompactProofRootFailure
      (coordinates.tag :: body) := by
    by_cases h0 : coordinates.tag = 0
    · rw [h0]
      exact .tag0 body (by
        simp [compactNodeSequentFormulaFields, hsequentParser])
    by_cases h1 : coordinates.tag = 1
    · rw [h1]
      exact .tag1 body (by
        simp [compactNodeSequentClosedFormulaFields, hsequentParser])
    by_cases h2 : coordinates.tag = 2
    · rw [h2]
      exact .tag2 body (by
        simp [compactNodeSequentOnlyFields, hsequentParser])
    by_cases h3 : coordinates.tag = 3
    · rw [h3]
      exact .tag3 body (by
        simp [compactNodeSequentTwoFormulaFields,
          compactNodeSequentFormulaFields, hsequentParser])
    by_cases h4 : coordinates.tag = 4
    · rw [h4]
      exact .tag4 body (by
        simp [compactNodeSequentTwoFormulaFields,
          compactNodeSequentFormulaFields, hsequentParser])
    by_cases h5 : coordinates.tag = 5
    · rw [h5]
      exact .tag5 body (by
        simp [compactNodeSequentFormulaFields, hsequentParser])
    by_cases h6 : coordinates.tag = 6
    · rw [h6]
      exact .tag6 body (by
        simp [compactNodeSequentFormulaTermFields,
          compactNodeSequentFormulaFields, hsequentParser])
    by_cases h7 : coordinates.tag = 7
    · rw [h7]
      exact .tag7 body (by
        simp [compactNodeSequentOnlyFields, hsequentParser])
    by_cases h8 : coordinates.tag = 8
    · rw [h8]
      exact .tag8 body (by
        simp [compactNodeSequentOnlyFields, hsequentParser])
    by_cases h9 : coordinates.tag = 9
    · rw [h9]
      exact .tag9 body (by
        simp [compactNodeSequentFormulaFields, hsequentParser])
    omega
  have hparser : compactListedProofNodeFieldsParser
      (coordinates.tag :: body) = none :=
    (compactListedProofNodeFieldsParser_eq_none_iff
      (coordinates.tag :: body)).mpr hfailure
  exact ⟨input, hinputLayout, by simpa only [hinputEq] using hparser⟩

def compactProofRootSequentFailureEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      bodyBoundary bodyCount bodyBoundarySize tag sequentBound : Nat) :
    CompactProofRootSequentFailureEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    bodyBoundary := bodyBoundary
    bodyCount := bodyCount
    bodyBoundarySize := bodyBoundarySize
    tag := tag
    sequentBound := sequentBound }

def CompactProofRootSequentFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ bodyBoundary, bodyBoundary ≤ endpointBound ∧
  ∃ bodyCount, bodyCount ≤ endpointBound ∧
  ∃ bodyBoundarySize, bodyBoundarySize ≤ endpointBound ∧
  ∃ tag, tag ≤ endpointBound ∧
  ∃ sequentBound, sequentBound ≤ endpointBound ∧
    CompactProofRootSequentFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish
        (compactProofRootSequentFailureEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          bodyBoundary bodyCount bodyBoundarySize tag sequentBound)

def compactProofRootSequentFailureEndpointBoundedGraphDef :
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
    ∃ sequentBound <⁺ endpointBound,
      !(compactProofRootSequentFailureEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish
        inputBoundary inputCount inputBoundarySize
        bodyBoundary bodyCount bodyBoundarySize tag sequentBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootSequentFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat) :
    compactProofRootSequentFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          bodyStart, bodyFinish, endpointBound] ↔
      CompactProofRootSequentFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  have hrow
      (sequentBound tag bodyBoundarySize bodyCount bodyBoundary
        inputBoundarySize inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![sequentBound, tag, bodyBoundarySize, bodyCount, bodyBoundary,
                inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                bodyStart, bodyFinish, endpointBound]
              Empty.elim ∘
            ![(#8 : Semiterm ℒₒᵣ Empty 16), #9, #10, #11, #12, #13, #14,
              #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim)
        compactProofRootSequentFailureEndpointGraphDef.val ↔
      CompactProofRootSequentFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish
          (compactProofRootSequentFailureEndpointCoordinatesOfValues
            inputBoundary inputCount inputBoundarySize
            bodyBoundary bodyCount bodyBoundarySize tag sequentBound) := by
    have henv :
        (Semiterm.val
            ![sequentBound, tag, bodyBoundarySize, bodyCount, bodyBoundary,
              inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              bodyStart, bodyFinish, endpointBound]
            Empty.elim ∘
          ![(#8 : Semiterm ℒₒᵣ Empty 16), #9, #10, #11, #12, #13, #14,
            #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactProofRootSequentFailureEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              bodyStart bodyFinish
              (compactProofRootSequentFailureEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                bodyBoundary bodyCount bodyBoundarySize tag sequentBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactProofRootSequentFailureEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish bodyStart bodyFinish _
  simp [compactProofRootSequentFailureEndpointBoundedGraphDef,
    CompactProofRootSequentFailureEndpointBoundedGraph, hrow]

theorem compactProofRootSequentFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootSequentFailureEndpointBoundedGraphDef.val := by
  simp [compactProofRootSequentFailureEndpointBoundedGraphDef]

theorem CompactProofRootSequentFailureEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootSequentFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish endpointBound) :
    ∃ coordinates : CompactProofRootSequentFailureEndpointCoordinates,
      CompactProofRootSequentFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      bodyBoundary, _, bodyCount, _, bodyBoundarySize, _,
      tag, _, sequentBound, _, hgraph⟩
  exact ⟨compactProofRootSequentFailureEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    bodyBoundary bodyCount bodyBoundarySize tag sequentBound, hgraph⟩

theorem CompactProofRootSequentFailureEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish : Nat}
    {coordinates : CompactProofRootSequentFailureEndpointCoordinates}
    (hgraph : CompactProofRootSequentFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish coordinates) :
    ∃ endpointBound,
      CompactProofRootSequentFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.bodyBoundary +
    coordinates.bodyCount + coordinates.bodyBoundarySize +
    coordinates.tag + coordinates.sequentBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactProofRootSequentFailureEndpointBoundedGraph
  refine ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
    coordinates.inputBoundarySize, ?_, coordinates.bodyBoundary, ?_,
    coordinates.bodyCount, ?_, coordinates.bodyBoundarySize, ?_,
    coordinates.tag, ?_, coordinates.sequentBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem CompactProofRootSequentFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish endpointBound : Nat}
    (hbounded : CompactProofRootSequentFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish endpointBound) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem exists_compactProofRootSequentFailureEndpointGraph_of_empty_body_with_inputLayout
    (tag : Nat) (htag : tag ≤ 9) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootSequentFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish [tag] ∧
        CompactProofRootSequentFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish coordinates := by
  let input := [tag]
  let body := ([] : List Nat)
  let inputTokens := compactAdditiveEncode input
  let bodyTokens := compactAdditiveEncode body
  let tokens := inputTokens ++ bodyTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input bodyTokens
  dsimp only at hinputRaw
  have hinputTokenEq :
      [] ++ compactAdditiveEncode input ++ bodyTokens = tokens := by
    simp [inputTokens, tokens]
  rw [hinputTokenEq] at hinputRaw
  have hbodyRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens body []
  dsimp only at hbodyRaw
  have hbodyTokenEq :
      inputTokens ++ compactAdditiveEncode body ++ [] = tokens := by
    simp [bodyTokens, tokens]
  rw [hbodyTokenEq] at hbodyRaw
  have hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length 0 inputTokens.length input := by
    simpa only [tokenTable, width, inputTokens,
      List.length_nil, Nat.zero_add] using hinputRaw
  have hbodyLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length inputTokens.length tokens.length body := by
    simpa only [tokenTable, width, tokens, bodyTokens,
      List.length_append, List.length_nil, Nat.add_zero] using hbodyRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  rcases hbodyLayout with
    ⟨bodyBoundary, hbodyStructure, hbodyElementRows, hbodySize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputSize⟩
  have hbodyRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length body.length tokens.length
        bodyBoundary (Nat.size bodyBoundary) :=
    ⟨hbodyStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hbodyElementRows,
      rfl, hbodySize⟩
  have hconsRows : CompactAdditiveNatListConsRows
      tokenTable width tokens.length bodyBoundary body.length
        inputBoundary input.length tag := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hbodyElementRows hinputElementRows
    rfl
  let sequentBound := bodyBoundary + Nat.size bodyBoundary
  have hsequent : CompactSequentFormulaNoOutputEndpointBoundedGraph
      tokenTable width tokens.length inputTokens.length tokens.length
        sequentBound := by
    apply Or.inl
    exact ⟨bodyBoundary, by dsimp only [sequentBound]; omega,
      Nat.size bodyBoundary, by dsimp only [sequentBound]; omega,
      by simpa only [body, List.length_nil] using hbodyRows⟩
  let coordinates : CompactProofRootSequentFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      bodyBoundary := bodyBoundary
      bodyCount := body.length
      bodyBoundarySize := Nat.size bodyBoundary
      tag := tag
      sequentBound := sequentBound }
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length, tokens.length, coordinates,
    by simpa [input] using hinputLayoutExact, ?_⟩
  exact ⟨hinputRows, hbodyRows, htag, hconsRows, hsequent⟩

theorem exists_compactProofRootSequentFailureEndpointGraph_of_empty_body
    (tag : Nat) (htag : tag ≤ 9) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish,
    ∃ coordinates : CompactProofRootSequentFailureEndpointCoordinates,
      CompactProofRootSequentFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish coordinates := by
  rcases
      exists_compactProofRootSequentFailureEndpointGraph_of_empty_body_with_inputLayout
        tag htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, coordinates, hgraph⟩

theorem exists_compactProofRootSequentFailureEndpointBoundedGraph_of_empty_body
    (tag : Nat) (htag : tag ≤ 9) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactProofRootSequentFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish endpointBound := by
  rcases exists_compactProofRootSequentFailureEndpointGraph_of_empty_body
      tag htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, endpointBound, hbounded⟩

theorem exists_compactProofRootSequentFailureEndpointBoundedGraph_of_empty_body_with_inputLayout
    (tag : Nat) (htag : tag ≤ 9) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish [tag] ∧
        CompactProofRootSequentFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish endpointBound := by
  rcases
      exists_compactProofRootSequentFailureEndpointGraph_of_empty_body_with_inputLayout
        tag htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, coordinates, hinputLayout, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    bodyStart, bodyFinish, endpointBound, hinputLayout, hbounded⟩

#print axioms compactProofRootSequentFailureEndpointGraphDef_spec
#print axioms compactProofRootSequentFailureEndpointGraphDef_sigmaZero
#print axioms CompactProofRootSequentFailureEndpointGraph.sound
#print axioms compactProofRootSequentFailureEndpointBoundedGraphDef_spec
#print axioms compactProofRootSequentFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactProofRootSequentFailureEndpointGraph.exists_bounded
#print axioms CompactProofRootSequentFailureEndpointBoundedGraph.sound
#print axioms exists_compactProofRootSequentFailureEndpointGraph_of_empty_body
#print axioms exists_compactProofRootSequentFailureEndpointBoundedGraph_of_empty_body

end FoundationCompactNumericListedDirectProofRootSequentFailureBoundedFormula
