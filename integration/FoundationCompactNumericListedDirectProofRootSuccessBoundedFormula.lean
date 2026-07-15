import integration.FoundationCompactNumericListedDirectProofRootSequentOnlyBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootOneFormulaBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootClosedFormulaBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootTwoFormulaBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootFormulaTermBoundedFormula

/-!
# Unified bounded success endpoint for the proof-root parser

The five successful parser families share input and decoded-root coordinates.
Their private body coordinates and endpoint bounds are existentially bounded.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectProofRootSequentOnlyBoundedFormula
open FoundationCompactNumericListedDirectProofRootOneFormulaBoundedFormula
open FoundationCompactNumericListedDirectProofRootClosedFormulaBoundedFormula
open FoundationCompactNumericListedDirectProofRootTwoFormulaBoundedFormula
open FoundationCompactNumericListedDirectProofRootFormulaTermBoundedFormula

def CompactProofRootSuccessBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish endpointBound : Nat) : Prop :=
  (∃ bodyStart, bodyStart ≤ endpointBound ∧
    ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootSequentOnlyEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish branchBound) ∨
  (∃ bodyStart, bodyStart ≤ endpointBound ∧
    ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootOneFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish branchBound) ∨
  (∃ bodyStart, bodyStart ≤ endpointBound ∧
    ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootClosedFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish branchBound) ∨
  (∃ bodyStart, bodyStart ≤ endpointBound ∧
    ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootTwoFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish branchBound) ∨
  (∃ bodyStart, bodyStart ≤ endpointBound ∧
    ∃ bodyFinish, bodyFinish ≤ endpointBound ∧
    ∃ branchBound, branchBound ≤ endpointBound ∧
      CompactProofRootFormulaTermEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish branchBound)

def compactProofRootSuccessBoundedGraphDef : 𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish endpointBound.
    (∃ bodyStart <⁺ endpointBound,
      ∃ bodyFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootSequentOnlyEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish branchBound) ∨
    (∃ bodyStart <⁺ endpointBound,
      ∃ bodyFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootOneFormulaEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish branchBound) ∨
    (∃ bodyStart <⁺ endpointBound,
      ∃ bodyFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootClosedFormulaEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish branchBound) ∨
    (∃ bodyStart <⁺ endpointBound,
      ∃ bodyFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootTwoFormulaEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish branchBound) ∨
    (∃ bodyStart <⁺ endpointBound,
      ∃ bodyFinish <⁺ endpointBound,
      ∃ branchBound <⁺ endpointBound,
        !(compactProofRootFormulaTermEndpointBoundedGraphDef)
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish branchBound)”

set_option maxRecDepth 4096 in
@[simp] theorem compactProofRootSuccessBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish endpointBound : Nat) :
    compactProofRootSuccessBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          rootStart, rootFinish, endpointBound] ↔
      CompactProofRootSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish endpointBound := by
  have henv (bodyStart bodyFinish branchBound : Nat) :
      (Semiterm.val
          ![branchBound, bodyFinish, bodyStart,
            tokenTable, width, tokenCount, inputStart, inputFinish,
            rootStart, rootFinish, endpointBound]
          Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 11), #4, #5, #6, #7,
          #8, #9, #2, #1, #0]) =
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          rootStart, rootFinish, bodyStart, bodyFinish, branchBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsequent (branchBound bodyFinish bodyStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, bodyFinish, bodyStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                rootStart, rootFinish, endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 11), #4, #5, #6, #7,
              #8, #9, #2, #1, #0])
          Empty.elim)
        compactProofRootSequentOnlyEndpointBoundedGraphDef.val ↔
      CompactProofRootSequentOnlyEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish branchBound := by
    rw [henv bodyStart bodyFinish branchBound]
    exact compactProofRootSequentOnlyEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound
  have hone (branchBound bodyFinish bodyStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, bodyFinish, bodyStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                rootStart, rootFinish, endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 11), #4, #5, #6, #7,
              #8, #9, #2, #1, #0])
          Empty.elim)
        compactProofRootOneFormulaEndpointBoundedGraphDef.val ↔
      CompactProofRootOneFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish branchBound := by
    rw [henv bodyStart bodyFinish branchBound]
    exact compactProofRootOneFormulaEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound
  have hclosed (branchBound bodyFinish bodyStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, bodyFinish, bodyStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                rootStart, rootFinish, endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 11), #4, #5, #6, #7,
              #8, #9, #2, #1, #0])
          Empty.elim)
        compactProofRootClosedFormulaEndpointBoundedGraphDef.val ↔
      CompactProofRootClosedFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish branchBound := by
    rw [henv bodyStart bodyFinish branchBound]
    exact compactProofRootClosedFormulaEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound
  have htwo (branchBound bodyFinish bodyStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, bodyFinish, bodyStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                rootStart, rootFinish, endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 11), #4, #5, #6, #7,
              #8, #9, #2, #1, #0])
          Empty.elim)
        compactProofRootTwoFormulaEndpointBoundedGraphDef.val ↔
      CompactProofRootTwoFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish branchBound := by
    rw [henv bodyStart bodyFinish branchBound]
    exact compactProofRootTwoFormulaEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound
  have hterm (branchBound bodyFinish bodyStart : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![branchBound, bodyFinish, bodyStart,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                rootStart, rootFinish, endpointBound]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 11), #4, #5, #6, #7,
              #8, #9, #2, #1, #0])
          Empty.elim)
        compactProofRootFormulaTermEndpointBoundedGraphDef.val ↔
      CompactProofRootFormulaTermEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish branchBound := by
    rw [henv bodyStart bodyFinish branchBound]
    exact compactProofRootFormulaTermEndpointBoundedGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound
  simp [compactProofRootSuccessBoundedGraphDef,
    CompactProofRootSuccessBoundedGraph,
    hsequent, hone, hclosed, htwo, hterm]

theorem compactProofRootSuccessBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootSuccessBoundedGraphDef.val := by
  simp [compactProofRootSuccessBoundedGraphDef]

theorem CompactProofRootSuccessBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish endpointBound : Nat}
    (hgraph : CompactProofRootSuccessBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish endpointBound) :
    ∃ input : List Nat, ∃ root : CompactNumericProofRoot,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount rootStart rootFinish root ∧
      compactListedProofNodeFieldsParser input = some root := by
  rcases hgraph with hsequent | hone | hclosed | htwo | hterm
  · rcases hsequent with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound
  · rcases hone with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound
  · rcases hclosed with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound
  · rcases htwo with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound
  · rcases hterm with ⟨_, _, _, _, _, _, hbranch⟩
    exact hbranch.sound

private theorem compactProofRootParser_success_tag_cases
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root) :
    root.1 = 0 ∨ root.1 = 1 ∨ root.1 = 2 ∨ root.1 = 3 ∨
      root.1 = 4 ∨ root.1 = 5 ∨ root.1 = 6 ∨ root.1 = 7 ∨
      root.1 = 8 ∨ root.1 = 9 := by
  have hvalid :=
    (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).mp hparser
  cases input with
  | nil =>
      simp [CompactNumericProofRootBranchValid] at hvalid
  | cons tag body =>
      by_cases h0 : tag = 0
      · have hbranch : root.1 = 0 ∧
            compactNodeSequentFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, h0] using hvalid
        exact Or.inl hbranch.1
      by_cases h1 : tag = 1
      · have hbranch : root.1 = 1 ∧
            compactNodeSequentClosedFormulaFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, h0, h1] using hvalid
        exact Or.inr (Or.inl hbranch.1)
      by_cases h2 : tag = 2
      · have hbranch : root.1 = 2 ∧
            compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, h0, h1, h2] using hvalid
        exact Or.inr (Or.inr (Or.inl hbranch.1))
      by_cases h3 : tag = 3
      · have hbranch : root.1 = 3 ∧
            compactNodeSequentTwoFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inl hbranch.1)))
      by_cases h4 : tag = 4
      · have hbranch : root.1 = 4 ∧
            compactNodeSequentTwoFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbranch.1))))
      by_cases h5 : tag = 5
      · have hbranch : root.1 = 5 ∧
            compactNodeSequentFormulaFields 1 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hbranch.1)))))
      by_cases h6 : tag = 6
      · have hbranch : root.1 = 6 ∧
            compactNodeSequentFormulaTermFields 1 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl hbranch.1))))))
      by_cases h7 : tag = 7
      · have hbranch : root.1 = 7 ∧
            compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6, h7] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl hbranch.1)))))))
      by_cases h8 : tag = 8
      · have hbranch : root.1 = 8 ∧
            compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6, h7, h8] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbranch.1))))))))
      by_cases h9 : tag = 9
      · have hbranch : root.1 = 9 ∧
            compactNodeSequentFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbranch.1))))))))
      simp [CompactNumericProofRootBranchValid,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at hvalid

private theorem lift_sequent
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish branchBound : Nat}
    (hbranch : CompactProofRootSequentOnlyEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish endpointBound := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  refine ⟨endpointBound, Or.inl
    ⟨bodyStart, ?_, bodyFinish, ?_, branchBound, ?_, hbranch⟩⟩ <;>
    dsimp only [endpointBound] <;> omega

private theorem lift_one
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish branchBound : Nat}
    (hbranch : CompactProofRootOneFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish endpointBound := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  refine ⟨endpointBound, Or.inr (Or.inl
    ⟨bodyStart, ?_, bodyFinish, ?_, branchBound, ?_, hbranch⟩)⟩ <;>
    dsimp only [endpointBound] <;> omega

private theorem lift_closed
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish branchBound : Nat}
    (hbranch : CompactProofRootClosedFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish endpointBound := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  refine ⟨endpointBound, Or.inr (Or.inr (Or.inl
    ⟨bodyStart, ?_, bodyFinish, ?_, branchBound, ?_, hbranch⟩))⟩ <;>
    dsimp only [endpointBound] <;> omega

private theorem lift_two
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish branchBound : Nat}
    (hbranch : CompactProofRootTwoFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish endpointBound := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  refine ⟨endpointBound, Or.inr (Or.inr (Or.inr (Or.inl
    ⟨bodyStart, ?_, bodyFinish, ?_, branchBound, ?_, hbranch⟩)))⟩ <;>
    dsimp only [endpointBound] <;> omega

private theorem lift_term
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish branchBound : Nat}
    (hbranch : CompactProofRootFormulaTermEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound) :
    ∃ endpointBound,
      CompactProofRootSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish endpointBound := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  refine ⟨endpointBound, Or.inr (Or.inr (Or.inr (Or.inr
    ⟨bodyStart, ?_, bodyFinish, ?_, branchBound, ?_, hbranch⟩)))⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_inputLayout
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSuccessBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound := by
  rcases compactProofRootParser_success_tag_cases hparser with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · rcases
        FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint.exists_compactProofRootOneFormulaEndpointGraph_of_success_with_inputLayout
        hparser (Or.inl h0) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, _coordinates,
        hinputLayout, hbranchRaw⟩
    rcases CompactProofRootOneFormulaEndpointGraph.exists_bounded hbranchRaw with
      ⟨branchBound, hbranch⟩
    rcases lift_one hbranch with ⟨endpointBound, hgraph⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinputLayout, hgraph⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootClosedFormulaEndpoint.exists_compactProofRootClosedFormulaEndpointGraph_of_success_with_inputLayout
        hparser h1 with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, _coordinates,
        hinputLayout, hbranchRaw⟩
    rcases CompactProofRootClosedFormulaEndpointGraph.exists_bounded hbranchRaw with
      ⟨branchBound, hbranch⟩
    rcases lift_closed hbranch with ⟨endpointBound, hgraph⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinputLayout, hgraph⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootSequentOnlyEndpoint.exists_compactProofRootSequentOnlyEndpointGraph_of_success_with_inputLayout
        hparser (Or.inl h2) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, _coordinates,
        hinputLayout, hbranchRaw⟩
    rcases CompactProofRootSequentOnlyEndpointGraph.exists_bounded hbranchRaw with
      ⟨branchBound, hbranch⟩
    rcases lift_sequent hbranch with ⟨endpointBound, hgraph⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinputLayout, hgraph⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootTwoFormulaEndpoint.exists_compactProofRootTwoFormulaEndpointGraph_of_success_with_inputLayout
        hparser (Or.inl h3) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, _coordinates,
        hinputLayout, hbranchRaw⟩
    rcases CompactProofRootTwoFormulaEndpointGraph.exists_bounded hbranchRaw with
      ⟨branchBound, hbranch⟩
    rcases lift_two hbranch with ⟨endpointBound, hgraph⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinputLayout, hgraph⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootTwoFormulaEndpoint.exists_compactProofRootTwoFormulaEndpointGraph_of_success_with_inputLayout
        hparser (Or.inr h4) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, _coordinates,
        hinputLayout, hbranchRaw⟩
    rcases CompactProofRootTwoFormulaEndpointGraph.exists_bounded hbranchRaw with
      ⟨branchBound, hbranch⟩
    rcases lift_two hbranch with ⟨endpointBound, hgraph⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinputLayout, hgraph⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint.exists_compactProofRootOneFormulaEndpointGraph_of_success_with_inputLayout
        hparser (Or.inr (Or.inl h5)) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, _coordinates,
        hinputLayout, hbranchRaw⟩
    rcases CompactProofRootOneFormulaEndpointGraph.exists_bounded hbranchRaw with
      ⟨branchBound, hbranch⟩
    rcases lift_one hbranch with ⟨endpointBound, hgraph⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinputLayout, hgraph⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootFormulaTermEndpoint.exists_compactProofRootFormulaTermEndpointGraph_of_success_with_inputLayout
        hparser h6 with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, _coordinates,
        hinputLayout, hbranchRaw⟩
    rcases CompactProofRootFormulaTermEndpointGraph.exists_bounded hbranchRaw with
      ⟨branchBound, hbranch⟩
    rcases lift_term hbranch with ⟨endpointBound, hgraph⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinputLayout, hgraph⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootSequentOnlyEndpoint.exists_compactProofRootSequentOnlyEndpointGraph_of_success_with_inputLayout
        hparser (Or.inr (Or.inl h7)) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, _coordinates,
        hinputLayout, hbranchRaw⟩
    rcases CompactProofRootSequentOnlyEndpointGraph.exists_bounded hbranchRaw with
      ⟨branchBound, hbranch⟩
    rcases lift_sequent hbranch with ⟨endpointBound, hgraph⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinputLayout, hgraph⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootSequentOnlyEndpoint.exists_compactProofRootSequentOnlyEndpointGraph_of_success_with_inputLayout
        hparser (Or.inr (Or.inr h8)) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, _coordinates,
        hinputLayout, hbranchRaw⟩
    rcases CompactProofRootSequentOnlyEndpointGraph.exists_bounded hbranchRaw with
      ⟨branchBound, hbranch⟩
    rcases lift_sequent hbranch with ⟨endpointBound, hgraph⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinputLayout, hgraph⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootOneFormulaEndpoint.exists_compactProofRootOneFormulaEndpointGraph_of_success_with_inputLayout
        hparser (Or.inr (Or.inr h9)) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, _coordinates,
        hinputLayout, hbranchRaw⟩
    rcases CompactProofRootOneFormulaEndpointGraph.exists_bounded hbranchRaw with
      ⟨branchBound, hbranch⟩
    rcases lift_one hbranch with ⟨endpointBound, hgraph⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinputLayout, hgraph⟩

theorem exists_compactProofRootSuccessBoundedGraph_of_parser_success
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish endpointBound,
      CompactProofRootSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish endpointBound := by
  rcases
      exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_inputLayout
        hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    rootStart, rootFinish, endpointBound, hgraph⟩

#print axioms compactProofRootSuccessBoundedGraphDef_spec
#print axioms compactProofRootSuccessBoundedGraphDef_sigmaZero
#print axioms CompactProofRootSuccessBoundedGraph.sound
#print axioms exists_compactProofRootSuccessBoundedGraph_of_parser_success

end FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula
