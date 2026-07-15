import integration.FoundationCompactNumericListedDirectProofRootOuterFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootSequentFailureCompleteness
import integration.FoundationCompactNumericListedDirectProofRootOneFormulaFailureCompleteness
import integration.FoundationCompactNumericListedDirectProofRootClosedFormulaFailureCompleteness
import integration.FoundationCompactNumericListedDirectProofRootTwoFormulaFailureCompleteness
import integration.FoundationCompactNumericListedDirectProofRootFormulaTermFailureCompleteness

/-!
# Total bounded failure endpoint for the proof-root parser

The six branches below exhaust empty/invalid input, sequent failure, first
formula failure, closed-formula failure, second-formula failure, and trailing
term failure.  Every branch is an already verified bounded endpoint graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootFailureBoundedFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectProofRootFailureSemantics
open FoundationCompactNumericListedDirectProofRootOuterFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootSequentFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootSequentFailureCompleteness
open FoundationCompactNumericListedDirectProofRootOneFormulaFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootOneFormulaFailureCompleteness
open FoundationCompactNumericListedDirectProofRootClosedFormulaFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootClosedFormulaFailureCompleteness
open FoundationCompactNumericListedDirectProofRootTwoFormulaFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootTwoFormulaFailureCompleteness
open FoundationCompactNumericListedDirectProofRootFormulaTermFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootFormulaTermFailureCompleteness

def CompactProofRootFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    Prop :=
  (∃ tailStart, tailStart ≤ endpointBound ∧
    ∃ tailFinish, tailFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootOuterFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish branchBound) ∨
  (∃ bodyStart, bodyStart ≤ endpointBound ∧
    ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootSequentFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound) ∨
  (∃ bodyStart, bodyStart ≤ endpointBound ∧
    ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootOneFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound) ∨
  (∃ bodyStart, bodyStart ≤ endpointBound ∧
    ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootClosedFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound) ∨
  (∃ bodyStart, bodyStart ≤ endpointBound ∧
    ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootTwoFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound) ∨
  (∃ bodyStart, bodyStart ≤ endpointBound ∧
    ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootFormulaTermFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound)

def compactProofRootFailureEndpointBoundedGraphDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish endpointBound.
    (∃ tailStart <⁺ endpointBound,
      ∃ tailFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootOuterFailureEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish branchBound) ∨
    (∃ bodyStart <⁺ endpointBound,
      ∃ bodyFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootSequentFailureEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish branchBound) ∨
    (∃ bodyStart <⁺ endpointBound,
      ∃ bodyFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootOneFormulaFailureEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish branchBound) ∨
    (∃ bodyStart <⁺ endpointBound,
      ∃ bodyFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootClosedFormulaFailureEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish branchBound) ∨
    (∃ bodyStart <⁺ endpointBound,
      ∃ bodyFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootTwoFormulaFailureEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish branchBound) ∨
    (∃ bodyStart <⁺ endpointBound,
      ∃ bodyFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootFormulaTermFailureEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            bodyStart bodyFinish branchBound)”

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    compactProofRootFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound] ↔
      CompactProofRootFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  have henv (branchStart branchFinish branchBound : Nat) :
      (Semiterm.val
          ![branchBound, branchFinish, branchStart,
            tokenTable, width, tokenCount, inputStart, inputFinish,
            endpointBound]
          Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 9), #4, #5, #6, #7, #2, #1, #0]) =
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          branchStart, branchFinish, branchBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have houter (branchBound tailFinish tailStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, tailFinish, tailStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 9), #4, #5, #6, #7, #2, #1, #0])
          Empty.elim)
        compactProofRootOuterFailureEndpointBoundedGraphDef.val ↔
      CompactProofRootOuterFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish branchBound := by
    rw [henv tailStart tailFinish branchBound]
    exact compactProofRootOuterFailureEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish branchBound
  have hsequent (branchBound bodyFinish bodyStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, bodyFinish, bodyStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 9), #4, #5, #6, #7, #2, #1, #0])
          Empty.elim)
        compactProofRootSequentFailureEndpointBoundedGraphDef.val ↔
      CompactProofRootSequentFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound := by
    rw [henv bodyStart bodyFinish branchBound]
    exact compactProofRootSequentFailureEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound
  have hformula (branchBound bodyFinish bodyStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, bodyFinish, bodyStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 9), #4, #5, #6, #7, #2, #1, #0])
          Empty.elim)
        compactProofRootOneFormulaFailureEndpointBoundedGraphDef.val ↔
      CompactProofRootOneFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound := by
    rw [henv bodyStart bodyFinish branchBound]
    exact compactProofRootOneFormulaFailureEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound
  have hclosed (branchBound bodyFinish bodyStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, bodyFinish, bodyStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 9), #4, #5, #6, #7, #2, #1, #0])
          Empty.elim)
        compactProofRootClosedFormulaFailureEndpointBoundedGraphDef.val ↔
      CompactProofRootClosedFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound := by
    rw [henv bodyStart bodyFinish branchBound]
    exact compactProofRootClosedFormulaFailureEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound
  have htwo (branchBound bodyFinish bodyStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, bodyFinish, bodyStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 9), #4, #5, #6, #7, #2, #1, #0])
          Empty.elim)
        compactProofRootTwoFormulaFailureEndpointBoundedGraphDef.val ↔
      CompactProofRootTwoFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound := by
    rw [henv bodyStart bodyFinish branchBound]
    exact compactProofRootTwoFormulaFailureEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound
  have hterm (branchBound bodyFinish bodyStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, bodyFinish, bodyStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 9), #4, #5, #6, #7, #2, #1, #0])
          Empty.elim)
        compactProofRootFormulaTermFailureEndpointBoundedGraphDef.val ↔
      CompactProofRootFormulaTermFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound := by
    rw [henv bodyStart bodyFinish branchBound]
    exact compactProofRootFormulaTermFailureEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound
  simp [compactProofRootFailureEndpointBoundedGraphDef,
    CompactProofRootFailureEndpointBoundedGraph,
    houter, hsequent, hformula, hclosed, htwo, hterm]

theorem compactProofRootFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootFailureEndpointBoundedGraphDef.val := by
  simp [compactProofRootFailureEndpointBoundedGraphDef]

theorem CompactProofRootFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hgraph : CompactProofRootFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactListedProofNodeFieldsParser input = none := by
  rcases hgraph with houter | hsequent | hformula | hclosed | htwo | hterm
  · rcases houter with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound
  · rcases hsequent with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound
  · rcases hformula with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound
  · rcases hclosed with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound
  · rcases htwo with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound
  · rcases hterm with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound

private theorem aggregate_outer
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish branchBound : Nat}
    (hbranch : CompactProofRootOuterFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  let endpointBound := tailStart + tailFinish + branchBound
  refine ⟨endpointBound, Or.inl ⟨tailStart, ?_, tailFinish, ?_,
    branchBound, ?_, hbranch⟩⟩ <;>
    dsimp only [endpointBound] <;> omega

private theorem aggregate_sequent
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish branchBound : Nat}
    (hbranch : CompactProofRootSequentFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  refine ⟨endpointBound, Or.inr (Or.inl
    ⟨bodyStart, ?_, bodyFinish, ?_, branchBound, ?_, hbranch⟩)⟩ <;>
    dsimp only [endpointBound] <;> omega

private theorem aggregate_formula
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish branchBound : Nat}
    (hbranch : CompactProofRootOneFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  refine ⟨endpointBound, Or.inr (Or.inr (Or.inl
    ⟨bodyStart, ?_, bodyFinish, ?_, branchBound, ?_, hbranch⟩))⟩ <;>
    dsimp only [endpointBound] <;> omega

private theorem aggregate_closed
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish branchBound : Nat}
    (hbranch : CompactProofRootClosedFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  refine ⟨endpointBound, Or.inr (Or.inr (Or.inr (Or.inl
    ⟨bodyStart, ?_, bodyFinish, ?_, branchBound, ?_, hbranch⟩)))⟩ <;>
    dsimp only [endpointBound] <;> omega

private theorem aggregate_two
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish branchBound : Nat}
    (hbranch : CompactProofRootTwoFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  refine ⟨endpointBound, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨bodyStart, ?_, bodyFinish, ?_, branchBound, ?_, hbranch⟩))))⟩ <;>
    dsimp only [endpointBound] <;> omega

private theorem aggregate_term
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish branchBound : Nat}
    (hbranch : CompactProofRootFormulaTermFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  refine ⟨endpointBound, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨bodyStart, ?_, bodyFinish, ?_, branchBound, ?_, hbranch⟩))))⟩ <;>
    dsimp only [endpointBound] <;> omega

private theorem compactNodeSequentFormulaFields_some_results
    {binderArity : Nat} {body : List Nat} {fields : CompactNumericNodeFields}
    (hfields : compactNodeSequentFormulaFields binderArity body =
      some fields) :
    ∃ values afterSequent secondInput,
      compactSequentTokenValueParser body = some (values, afterSequent) ∧
      compactFormulaTokenParser binderArity afterSequent =
        some secondInput ∧
      compactNumericNodeFieldsSuffix fields = secondInput := by
  cases hsequent : compactSequentTokenValueParser body with
  | none =>
      simp [compactNodeSequentFormulaFields, hsequent] at hfields
  | some parsedSequent =>
      rcases parsedSequent with ⟨values, afterSequent⟩
      cases hformula : compactFormulaTokenParser binderArity afterSequent with
      | none =>
          simp [compactNodeSequentFormulaFields,
            compactFormulaTokenValueParser, hsequent, hformula] at hfields
      | some secondInput =>
          have hfieldsEq : fields =
              (values,
                (consumedTokenPrefix afterSequent secondInput,
                  ([], ([], secondInput)))) := by
            simpa [compactNodeSequentFormulaFields,
              compactFormulaTokenValueParser, hsequent, hformula] using
                hfields.symm
          subst fields
          exact ⟨values, afterSequent, secondInput,
            rfl, hformula, rfl⟩

private theorem exists_aggregate_sequent_with_inputLayout
    (tag : Nat) (body : List Nat) (htag : tag ≤ 9)
    (hsequent : compactSequentTokenValueParser body = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: body) ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      exists_compactProofRootSequentFailureEndpointBoundedGraph_of_none_with_inputLayout
      tag body htag hsequent with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, branchBound, hinputLayout, hbranch⟩
  rcases aggregate_sequent hbranch with ⟨endpointBound, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, hgraph⟩

private theorem exists_aggregate_formula_with_inputLayout
    (tag binderArity : Nat) (body : List Nat) (values : List (List Nat))
    (afterSequent : List Nat)
    (htagBinder : CompactProofRootFormulaFailureTagBinder tag binderArity)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hformula : compactFormulaTokenParser binderArity afterSequent = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: body) ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      exists_compactProofRootOneFormulaFailureEndpointBoundedGraph_of_results_with_inputLayout
      tag binderArity body values afterSequent
        htagBinder hsequent hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, branchBound, hinputLayout, hbranch⟩
  rcases aggregate_formula hbranch with ⟨endpointBound, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinputLayout, hgraph⟩

theorem exists_compactProofRootFailureEndpointBoundedGraph_of_none_with_inputLayout
    (input : List Nat)
    (hparser : compactListedProofNodeFieldsParser input = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound := by
  have hfailure :=
    (compactListedProofNodeFieldsParser_eq_none_iff input).mp hparser
  cases hfailure with
  | empty =>
      rcases
          exists_compactProofRootOuterFailureEndpointBoundedGraph_of_empty_with_inputLayout with
        ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          tailStart, tailFinish, branchBound, hinputLayout, hbranch⟩
      rcases aggregate_outer hbranch with ⟨endpointBound, hgraph⟩
      exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        endpointBound, hinputLayout, hgraph⟩
  | invalid tag body htag =>
      rcases
          exists_compactProofRootOuterFailureEndpointBoundedGraph_of_invalid_with_inputLayout
          tag body htag with
        ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          tailStart, tailFinish, branchBound, hinputLayout, hbranch⟩
      rcases aggregate_outer hbranch with ⟨endpointBound, hgraph⟩
      exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        endpointBound, hinputLayout, hgraph⟩
  | tag0 body hnode =>
      rcases (compactNodeSequentFormulaFields_eq_none_iff 0 body).mp hnode with
        hsequent | ⟨values, suffix, hsequent, hformula⟩
      · exact exists_aggregate_sequent_with_inputLayout 0 body (by omega) hsequent
      · exact exists_aggregate_formula_with_inputLayout 0 0 body values suffix
          (by simp [CompactProofRootFormulaFailureTagBinder])
          hsequent hformula
  | tag1 body hnode =>
      rcases (compactNodeSequentClosedFormulaFields_eq_none_iff body).mp hnode with
        hsequent | ⟨values, suffix, hsequent, hformula⟩
      · exact exists_aggregate_sequent_with_inputLayout 1 body (by omega) hsequent
      · rcases
            exists_compactProofRootClosedFormulaFailureEndpointBoundedGraph_of_results_with_inputLayout
            body values suffix hsequent hformula with
          ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
            bodyStart, bodyFinish, branchBound, hinputLayout, hbranch⟩
        rcases aggregate_closed hbranch with ⟨endpointBound, hgraph⟩
        exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound, hinputLayout, hgraph⟩
  | tag2 body hnode =>
      exact exists_aggregate_sequent_with_inputLayout 2 body (by omega) (by
        simpa [compactNodeSequentOnlyFields] using hnode)
  | tag3 body hnode =>
      rcases (compactNodeSequentTwoFormulaFields_eq_none_iff 0 body).mp hnode with
        hfirst | ⟨firstFields, hfirst, hsecond⟩
      · rcases (compactNodeSequentFormulaFields_eq_none_iff 0 body).mp hfirst with
          hsequent | ⟨values, suffix, hsequent, hformula⟩
        · exact exists_aggregate_sequent_with_inputLayout 3 body (by omega) hsequent
        · exact exists_aggregate_formula_with_inputLayout 3 0 body values suffix
            (by simp [CompactProofRootFormulaFailureTagBinder])
            hsequent hformula
      · rcases compactNodeSequentFormulaFields_some_results hfirst with
          ⟨values, afterSequent, secondInput,
            hsequent, hfirstParser, hsuffix⟩
        rw [hsuffix] at hsecond
        rcases
            exists_compactProofRootTwoFormulaFailureEndpointBoundedGraph_of_results_with_inputLayout
            3 body values afterSequent secondInput (Or.inl rfl)
              hsequent hfirstParser hsecond with
          ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
            bodyStart, bodyFinish, branchBound, hinputLayout, hbranch⟩
        rcases aggregate_two hbranch with ⟨endpointBound, hgraph⟩
        exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound, hinputLayout, hgraph⟩
  | tag4 body hnode =>
      rcases (compactNodeSequentTwoFormulaFields_eq_none_iff 0 body).mp hnode with
        hfirst | ⟨firstFields, hfirst, hsecond⟩
      · rcases (compactNodeSequentFormulaFields_eq_none_iff 0 body).mp hfirst with
          hsequent | ⟨values, suffix, hsequent, hformula⟩
        · exact exists_aggregate_sequent_with_inputLayout 4 body (by omega) hsequent
        · exact exists_aggregate_formula_with_inputLayout 4 0 body values suffix
            (by simp [CompactProofRootFormulaFailureTagBinder])
            hsequent hformula
      · rcases compactNodeSequentFormulaFields_some_results hfirst with
          ⟨values, afterSequent, secondInput,
            hsequent, hfirstParser, hsuffix⟩
        rw [hsuffix] at hsecond
        rcases
            exists_compactProofRootTwoFormulaFailureEndpointBoundedGraph_of_results_with_inputLayout
            4 body values afterSequent secondInput (Or.inr rfl)
              hsequent hfirstParser hsecond with
          ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
            bodyStart, bodyFinish, branchBound, hinputLayout, hbranch⟩
        rcases aggregate_two hbranch with ⟨endpointBound, hgraph⟩
        exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound, hinputLayout, hgraph⟩
  | tag5 body hnode =>
      rcases (compactNodeSequentFormulaFields_eq_none_iff 1 body).mp hnode with
        hsequent | ⟨values, suffix, hsequent, hformula⟩
      · exact exists_aggregate_sequent_with_inputLayout 5 body (by omega) hsequent
      · exact exists_aggregate_formula_with_inputLayout 5 1 body values suffix
          (by simp [CompactProofRootFormulaFailureTagBinder])
          hsequent hformula
  | tag6 body hnode =>
      rcases (compactNodeSequentFormulaTermFields_eq_none_iff 1 0 body).mp hnode with
        hfirst | ⟨firstFields, hfirst, hterm⟩
      · rcases (compactNodeSequentFormulaFields_eq_none_iff 1 body).mp hfirst with
          hsequent | ⟨values, suffix, hsequent, hformula⟩
        · exact exists_aggregate_sequent_with_inputLayout 6 body (by omega) hsequent
        · exact exists_aggregate_formula_with_inputLayout 6 1 body values suffix
            (by simp [CompactProofRootFormulaFailureTagBinder])
            hsequent hformula
      · rcases compactNodeSequentFormulaFields_some_results hfirst with
          ⟨values, afterSequent, secondInput,
            hsequent, hfirstParser, hsuffix⟩
        rw [hsuffix] at hterm
        rcases
            exists_compactProofRootFormulaTermFailureEndpointBoundedGraph_of_results_with_inputLayout
            body values afterSequent secondInput
              hsequent hfirstParser hterm with
          ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
            bodyStart, bodyFinish, branchBound, hinputLayout, hbranch⟩
        rcases aggregate_term hbranch with ⟨endpointBound, hgraph⟩
        exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound, hinputLayout, hgraph⟩
  | tag7 body hnode =>
      exact exists_aggregate_sequent_with_inputLayout 7 body (by omega) (by
        simpa [compactNodeSequentOnlyFields] using hnode)
  | tag8 body hnode =>
      exact exists_aggregate_sequent_with_inputLayout 8 body (by omega) (by
        simpa [compactNodeSequentOnlyFields] using hnode)
  | tag9 body hnode =>
      rcases (compactNodeSequentFormulaFields_eq_none_iff 0 body).mp hnode with
        hsequent | ⟨values, suffix, hsequent, hformula⟩
      · exact exists_aggregate_sequent_with_inputLayout 9 body (by omega) hsequent
      · exact exists_aggregate_formula_with_inputLayout 9 0 body values suffix
          (by simp [CompactProofRootFormulaFailureTagBinder])
          hsequent hformula

theorem exists_compactProofRootFailureEndpointBoundedGraph_of_none
    (input : List Nat)
    (hparser : compactListedProofNodeFieldsParser input = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactProofRootFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases
      exists_compactProofRootFailureEndpointBoundedGraph_of_none_with_inputLayout
        input hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      endpointBound, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hgraph⟩

#print axioms compactProofRootFailureEndpointBoundedGraphDef_spec
#print axioms compactProofRootFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactProofRootFailureEndpointBoundedGraph.sound
#print axioms exists_compactProofRootFailureEndpointBoundedGraph_of_none

end FoundationCompactNumericListedDirectProofRootFailureBoundedFormula
