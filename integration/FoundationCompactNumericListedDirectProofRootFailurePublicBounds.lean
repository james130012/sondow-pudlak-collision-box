import integration.FoundationCompactNumericListedDirectProofRootOuterFailurePublicBounds
import integration.FoundationCompactNumericListedDirectProofRootSequentFailurePublicBounds
import integration.FoundationCompactNumericListedDirectProofRootOneFormulaFailurePublicBounds
import integration.FoundationCompactNumericListedDirectProofRootClosedFormulaFailurePublicBounds
import integration.FoundationCompactNumericListedDirectProofRootTwoFormulaFailurePublicBounds
import integration.FoundationCompactNumericListedDirectProofRootFormulaTermFailurePublicBounds
import integration.FoundationCompactNumericListedDirectProofRootFailureBoundedFormula

/-!
# Public bounds for every failed proof-root parser branch

The proof-root parser has six exhaustive failure families.  Every family now
constructs its own bounded endpoint from the original input.  This file
dispatches on the actual parser failure and lifts the eight exposed endpoint
coordinates to one explicit input-weight budget.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootFailurePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectProofRootFailureSemantics
open FoundationCompactNumericListedDirectProofRootOuterFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootSequentFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootOneFormulaFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootClosedFormulaFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootTwoFormulaFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootFormulaTermFailureBoundedFormula
open FoundationCompactNumericListedDirectProofRootFailureBoundedFormula

/-- The sum of all six branch budgets dominates the budget of whichever
failure branch the parser selects. -/
def compactProofRootFailureBranchCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  FoundationCompactNumericListedDirectProofRootOuterFailurePublicBounds.compactProofRootOuterFailurePublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectProofRootSequentFailurePublicBounds.compactProofRootSequentFailurePublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectProofRootOneFormulaFailurePublicBounds.compactProofRootOneFormulaFailurePublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectProofRootClosedFormulaFailurePublicBounds.compactProofRootClosedFormulaFailurePublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectProofRootTwoFormulaFailurePublicBounds.compactProofRootTwoFormulaFailurePublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectProofRootFormulaTermFailurePublicBounds.compactProofRootFormulaTermFailurePublicCoordinateSizeBound
      inputWeight

/-- The unified endpoint is the sum of two branch-local slice coordinates and
the selected branch endpoint. -/
def compactProofRootFailurePublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  3 * compactProofRootFailureBranchCoordinateSizeBound inputWeight + 2

structure CompactProofRootFailurePublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish
      endpointBound bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width : Nat.size width <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  endpointBound : Nat.size endpointBound <= bound

private theorem natSize_add_le (left right : Nat) :
    Nat.size (left + right) <= Nat.size left + Nat.size right + 1 := by
  rw [Nat.size_le]
  have hleft : left < 2 ^ Nat.size left := Nat.lt_size_self left
  have hright : right < 2 ^ Nat.size right := Nat.lt_size_self right
  have hleftPower :
      2 ^ Nat.size left <= 2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_right (Nat.size left) (Nat.size right))
  have hrightPower :
      2 ^ Nat.size right <= 2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_left (Nat.size right) (Nat.size left))
  calc
    left + right < 2 ^ Nat.size left + 2 ^ Nat.size right :=
      Nat.add_lt_add hleft hright
    _ <= 2 ^ (Nat.size left + Nat.size right) +
        2 ^ (Nat.size left + Nat.size right) :=
      Nat.add_le_add hleftPower hrightPower
    _ = 2 ^ (Nat.size left + Nat.size right + 1) := by
      rw [pow_succ]
      omega

private theorem natSize_three_add_le (a b c : Nat) :
    Nat.size (a + b + c) <=
      Nat.size a + Nat.size b + Nat.size c + 2 := by
  have hab := natSize_add_le a b
  have habc := natSize_add_le (a + b) c
  omega

private theorem outerBound_le_branchBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootOuterFailurePublicBounds.compactProofRootOuterFailurePublicCoordinateSizeBound
        inputWeight <=
      compactProofRootFailureBranchCoordinateSizeBound inputWeight := by
  unfold compactProofRootFailureBranchCoordinateSizeBound
  omega

private theorem sequentBound_le_branchBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootSequentFailurePublicBounds.compactProofRootSequentFailurePublicCoordinateSizeBound
        inputWeight <=
      compactProofRootFailureBranchCoordinateSizeBound inputWeight := by
  unfold compactProofRootFailureBranchCoordinateSizeBound
  omega

private theorem oneBound_le_branchBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootOneFormulaFailurePublicBounds.compactProofRootOneFormulaFailurePublicCoordinateSizeBound
        inputWeight <=
      compactProofRootFailureBranchCoordinateSizeBound inputWeight := by
  unfold compactProofRootFailureBranchCoordinateSizeBound
  omega

private theorem closedBound_le_branchBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootClosedFormulaFailurePublicBounds.compactProofRootClosedFormulaFailurePublicCoordinateSizeBound
        inputWeight <=
      compactProofRootFailureBranchCoordinateSizeBound inputWeight := by
  unfold compactProofRootFailureBranchCoordinateSizeBound
  omega

private theorem twoBound_le_branchBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootTwoFormulaFailurePublicBounds.compactProofRootTwoFormulaFailurePublicCoordinateSizeBound
        inputWeight <=
      compactProofRootFailureBranchCoordinateSizeBound inputWeight := by
  unfold compactProofRootFailureBranchCoordinateSizeBound
  omega

private theorem termBound_le_branchBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootFormulaTermFailurePublicBounds.compactProofRootFormulaTermFailurePublicCoordinateSizeBound
        inputWeight <=
      compactProofRootFailureBranchCoordinateSizeBound inputWeight := by
  unfold compactProofRootFailureBranchCoordinateSizeBound
  omega

private theorem assemble_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      firstEndpoint secondEndpoint branchEndpoint : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hgraph : CompactProofRootFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        (firstEndpoint + secondEndpoint + branchEndpoint))
    (htokenTable :
      Nat.size tokenTable <=
        compactProofRootFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (hwidth :
      Nat.size width <=
        compactProofRootFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (htokenCount :
      Nat.size tokenCount <=
        compactProofRootFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (hinputStart :
      Nat.size inputStart <=
        compactProofRootFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (hinputFinish :
      Nat.size inputFinish <=
        compactProofRootFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (hfirstEndpoint :
      Nat.size firstEndpoint <=
        compactProofRootFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (hsecondEndpoint :
      Nat.size secondEndpoint <=
        compactProofRootFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (hbranchEndpoint :
      Nat.size branchEndpoint <=
        compactProofRootFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input)) :
    ∃ endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactProofRootFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactProofRootFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  let endpointBound := firstEndpoint + secondEndpoint + branchEndpoint
  have hbranchToPublic :
      compactProofRootFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input) <=
        compactProofRootFailurePublicCoordinateSizeBound
          (compactAdditiveValueWeight input) := by
    unfold compactProofRootFailurePublicCoordinateSizeBound
    omega
  have hendpointRaw :=
    natSize_three_add_le firstEndpoint secondEndpoint branchEndpoint
  have hendpoint :
      Nat.size endpointBound <=
        compactProofRootFailurePublicCoordinateSizeBound
          (compactAdditiveValueWeight input) := by
    dsimp only [endpointBound]
    unfold compactProofRootFailurePublicCoordinateSizeBound
    omega
  exact ⟨endpointBound, hinput, by
      simpa only [endpointBound] using hgraph,
    { tokenTable := htokenTable.trans hbranchToPublic
      width := hwidth.trans hbranchToPublic
      tokenCount := htokenCount.trans hbranchToPublic
      inputStart := hinputStart.trans hbranchToPublic
      inputFinish := hinputFinish.trans hbranchToPublic
      endpointBound := hendpoint }⟩

private theorem lift_outer_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootOuterFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootOuterFailurePublicBounds.CompactProofRootOuterFailurePublicCoordinateBounds
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish branchBound
          (FoundationCompactNumericListedDirectProofRootOuterFailurePublicBounds.compactProofRootOuterFailurePublicCoordinateSizeBound
            (compactAdditiveValueWeight input))) :
    ∃ endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactProofRootFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactProofRootFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  have hlift := outerBound_le_branchBound (compactAdditiveValueWeight input)
  exact assemble_with_publicBounds hinput
    (Or.inl
      ⟨tailStart, by omega, tailFinish, by omega,
        branchBound, by omega, hbranch⟩)
    (hbounds.tokenTable.trans hlift)
    (hbounds.width.trans hlift)
    (hbounds.tokenCount.trans hlift)
    (hbounds.inputStart.trans hlift)
    (hbounds.inputFinish.trans hlift)
    (hbounds.tailStart.trans hlift)
    (hbounds.tailFinish.trans hlift)
    (hbounds.endpointBound.trans hlift)

private theorem lift_sequent_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootSequentFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootSequentFailurePublicBounds.CompactProofRootSequentFailurePublicCoordinateBounds
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound
          (FoundationCompactNumericListedDirectProofRootSequentFailurePublicBounds.compactProofRootSequentFailurePublicCoordinateSizeBound
            (compactAdditiveValueWeight input))) :
    ∃ endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactProofRootFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactProofRootFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  have hlift := sequentBound_le_branchBound (compactAdditiveValueWeight input)
  exact assemble_with_publicBounds hinput
    (Or.inr (Or.inl
      ⟨bodyStart, by omega, bodyFinish, by omega,
        branchBound, by omega, hbranch⟩))
    (hbounds.tokenTable.trans hlift)
    (hbounds.width.trans hlift)
    (hbounds.tokenCount.trans hlift)
    (hbounds.inputStart.trans hlift)
    (hbounds.inputFinish.trans hlift)
    (hbounds.bodyStart.trans hlift)
    (hbounds.bodyFinish.trans hlift)
    (hbounds.endpointBound.trans hlift)

private theorem lift_one_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootOneFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootOneFormulaFailurePublicBounds.CompactProofRootOneFormulaFailurePublicCoordinateBounds
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound
          (FoundationCompactNumericListedDirectProofRootOneFormulaFailurePublicBounds.compactProofRootOneFormulaFailurePublicCoordinateSizeBound
            (compactAdditiveValueWeight input))) :
    ∃ endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactProofRootFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactProofRootFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  have hlift := oneBound_le_branchBound (compactAdditiveValueWeight input)
  exact assemble_with_publicBounds hinput
    (Or.inr (Or.inr (Or.inl
      ⟨bodyStart, by omega, bodyFinish, by omega,
        branchBound, by omega, hbranch⟩)))
    (hbounds.tokenTable.trans hlift)
    (hbounds.width.trans hlift)
    (hbounds.tokenCount.trans hlift)
    (hbounds.inputStart.trans hlift)
    (hbounds.inputFinish.trans hlift)
    (hbounds.bodyStart.trans hlift)
    (hbounds.bodyFinish.trans hlift)
    (hbounds.endpointBound.trans hlift)

private theorem lift_closed_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootClosedFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootClosedFormulaFailurePublicBounds.CompactProofRootClosedFormulaFailurePublicCoordinateBounds
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound
          (FoundationCompactNumericListedDirectProofRootClosedFormulaFailurePublicBounds.compactProofRootClosedFormulaFailurePublicCoordinateSizeBound
            (compactAdditiveValueWeight input))) :
    ∃ endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactProofRootFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactProofRootFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  have hlift := closedBound_le_branchBound (compactAdditiveValueWeight input)
  exact assemble_with_publicBounds hinput
    (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨bodyStart, by omega, bodyFinish, by omega,
        branchBound, by omega, hbranch⟩))))
    (hbounds.tokenTable.trans hlift)
    (hbounds.width.trans hlift)
    (hbounds.tokenCount.trans hlift)
    (hbounds.inputStart.trans hlift)
    (hbounds.inputFinish.trans hlift)
    (hbounds.bodyStart.trans hlift)
    (hbounds.bodyFinish.trans hlift)
    (hbounds.endpointBound.trans hlift)

private theorem lift_two_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootTwoFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootTwoFormulaFailurePublicBounds.CompactProofRootTwoFormulaFailurePublicCoordinateBounds
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound
          (FoundationCompactNumericListedDirectProofRootTwoFormulaFailurePublicBounds.compactProofRootTwoFormulaFailurePublicCoordinateSizeBound
            (compactAdditiveValueWeight input))) :
    ∃ endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactProofRootFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactProofRootFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  have hlift := twoBound_le_branchBound (compactAdditiveValueWeight input)
  exact assemble_with_publicBounds hinput
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨bodyStart, by omega, bodyFinish, by omega,
        branchBound, by omega, hbranch⟩)))))
    (hbounds.tokenTable.trans hlift)
    (hbounds.width.trans hlift)
    (hbounds.tokenCount.trans hlift)
    (hbounds.inputStart.trans hlift)
    (hbounds.inputFinish.trans hlift)
    (hbounds.bodyStart.trans hlift)
    (hbounds.bodyFinish.trans hlift)
    (hbounds.endpointBound.trans hlift)

private theorem lift_term_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      bodyStart bodyFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootFormulaTermFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        bodyStart bodyFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootFormulaTermFailurePublicBounds.CompactProofRootFormulaTermFailurePublicCoordinateBounds
        tokenTable width tokenCount inputStart inputFinish
          bodyStart bodyFinish branchBound
          (FoundationCompactNumericListedDirectProofRootFormulaTermFailurePublicBounds.compactProofRootFormulaTermFailurePublicCoordinateSizeBound
            (compactAdditiveValueWeight input))) :
    ∃ endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactProofRootFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactProofRootFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  have hlift := termBound_le_branchBound (compactAdditiveValueWeight input)
  exact assemble_with_publicBounds hinput
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨bodyStart, by omega, bodyFinish, by omega,
        branchBound, by omega, hbranch⟩)))))
    (hbounds.tokenTable.trans hlift)
    (hbounds.width.trans hlift)
    (hbounds.tokenCount.trans hlift)
    (hbounds.inputStart.trans hlift)
    (hbounds.inputFinish.trans hlift)
    (hbounds.bodyStart.trans hlift)
    (hbounds.bodyFinish.trans hlift)
    (hbounds.endpointBound.trans hlift)

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

private theorem exists_aggregate_sequent_with_publicBounds
    (tag : Nat) (body : List Nat) (htag : tag ≤ 9)
    (hsequent : compactSequentTokenValueParser body = none) :
    let input := tag :: body
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactProofRootFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactProofRootFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  rcases
      FoundationCompactNumericListedDirectProofRootSequentFailurePublicBounds.exists_compactProofRootSequentFailureEndpointBoundedGraph_of_none_with_publicBounds
        tag body htag hsequent with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, branchBound, hinput, hbranch, hbounds⟩
  rcases lift_sequent_with_publicBounds hinput hbranch hbounds with
    ⟨endpointBound, hinput, hgraph, hpublic⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinput, hgraph, hpublic⟩

private theorem exists_aggregate_formula_with_publicBounds
    (tag binderArity : Nat) (body : List Nat) (values : List (List Nat))
    (afterSequent : List Nat)
    (htagBinder : CompactProofRootFormulaFailureTagBinder tag binderArity)
    (hsequent : compactSequentTokenValueParser body =
      some (values, afterSequent))
    (hformula : compactFormulaTokenParser binderArity afterSequent = none) :
    let input := tag :: body
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactProofRootFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactProofRootFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  rcases
      FoundationCompactNumericListedDirectProofRootOneFormulaFailurePublicBounds.exists_compactProofRootOneFormulaFailureEndpointBoundedGraph_of_results_with_publicBounds
        tag binderArity body values afterSequent
          htagBinder hsequent hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      bodyStart, bodyFinish, branchBound, hinput, hbranch, hbounds⟩
  rcases lift_one_with_publicBounds hinput hbranch hbounds with
    ⟨endpointBound, hinput, hgraph, hpublic⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinput, hgraph, hpublic⟩

/- Every failed proof-root parse constructs one of the six exact failure
graphs, and every exposed coordinate is bounded solely from the original
input weight. -/
set_option maxHeartbeats 2400000 in
theorem
    exists_compactProofRootFailureEndpointBoundedGraph_of_none_with_publicBounds
    (input : List Nat)
    (hparser : compactListedProofNodeFieldsParser input = none) :
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactProofRootFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactProofRootFailurePublicCoordinateSizeBound
              inputWeight) := by
  have hfailure :=
    (compactListedProofNodeFieldsParser_eq_none_iff input).mp hparser
  cases hfailure with
  | empty =>
      rcases
          FoundationCompactNumericListedDirectProofRootOuterFailurePublicBounds.exists_compactProofRootOuterFailureEndpointBoundedGraph_of_empty_with_publicBounds with
        ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          tailStart, tailFinish, branchBound, hinput, hbranch, hbounds⟩
      rcases lift_outer_with_publicBounds hinput hbranch hbounds with
        ⟨endpointBound, hinput, hgraph, hpublic⟩
      exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        endpointBound, hinput, hgraph, hpublic⟩
  | invalid tag body htag =>
      rcases
          FoundationCompactNumericListedDirectProofRootOuterFailurePublicBounds.exists_compactProofRootOuterFailureEndpointBoundedGraph_of_invalid_with_publicBounds
            tag body htag with
        ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          tailStart, tailFinish, branchBound, hinput, hbranch, hbounds⟩
      rcases lift_outer_with_publicBounds hinput hbranch hbounds with
        ⟨endpointBound, hinput, hgraph, hpublic⟩
      exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        endpointBound, hinput, hgraph, hpublic⟩
  | tag0 body hnode =>
      rcases (compactNodeSequentFormulaFields_eq_none_iff 0 body).mp hnode with
        hsequent | ⟨values, suffix, hsequent, hformula⟩
      · exact exists_aggregate_sequent_with_publicBounds
          0 body (by omega) hsequent
      · exact exists_aggregate_formula_with_publicBounds
          0 0 body values suffix
            (by simp [CompactProofRootFormulaFailureTagBinder])
            hsequent hformula
  | tag1 body hnode =>
      rcases (compactNodeSequentClosedFormulaFields_eq_none_iff body).mp hnode with
        hsequent | ⟨values, suffix, hsequent, hformula⟩
      · exact exists_aggregate_sequent_with_publicBounds
          1 body (by omega) hsequent
      · rcases
            FoundationCompactNumericListedDirectProofRootClosedFormulaFailurePublicBounds.exists_compactProofRootClosedFormulaFailureEndpointBoundedGraph_of_results_with_publicBounds
              body values suffix hsequent hformula with
          ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
            bodyStart, bodyFinish, branchBound, hinput, hbranch, hbounds⟩
        rcases lift_closed_with_publicBounds hinput hbranch hbounds with
          ⟨endpointBound, hinput, hgraph, hpublic⟩
        exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound, hinput, hgraph, hpublic⟩
  | tag2 body hnode =>
      exact exists_aggregate_sequent_with_publicBounds
        2 body (by omega) (by
          simpa [compactNodeSequentOnlyFields] using hnode)
  | tag3 body hnode =>
      rcases (compactNodeSequentTwoFormulaFields_eq_none_iff 0 body).mp hnode with
        hfirst | ⟨firstFields, hfirst, hsecond⟩
      · rcases (compactNodeSequentFormulaFields_eq_none_iff 0 body).mp hfirst with
          hsequent | ⟨values, suffix, hsequent, hformula⟩
        · exact exists_aggregate_sequent_with_publicBounds
            3 body (by omega) hsequent
        · exact exists_aggregate_formula_with_publicBounds
            3 0 body values suffix
              (by simp [CompactProofRootFormulaFailureTagBinder])
              hsequent hformula
      · rcases compactNodeSequentFormulaFields_some_results hfirst with
          ⟨values, afterSequent, secondInput,
            hsequent, hfirstParser, hsuffix⟩
        rw [hsuffix] at hsecond
        rcases
            FoundationCompactNumericListedDirectProofRootTwoFormulaFailurePublicBounds.exists_compactProofRootTwoFormulaFailureEndpointBoundedGraph_of_results_with_publicBounds
              3 body values afterSequent secondInput (Or.inl rfl)
                hsequent hfirstParser hsecond with
          ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
            bodyStart, bodyFinish, branchBound, hinput, hbranch, hbounds⟩
        rcases lift_two_with_publicBounds hinput hbranch hbounds with
          ⟨endpointBound, hinput, hgraph, hpublic⟩
        exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound, hinput, hgraph, hpublic⟩
  | tag4 body hnode =>
      rcases (compactNodeSequentTwoFormulaFields_eq_none_iff 0 body).mp hnode with
        hfirst | ⟨firstFields, hfirst, hsecond⟩
      · rcases (compactNodeSequentFormulaFields_eq_none_iff 0 body).mp hfirst with
          hsequent | ⟨values, suffix, hsequent, hformula⟩
        · exact exists_aggregate_sequent_with_publicBounds
            4 body (by omega) hsequent
        · exact exists_aggregate_formula_with_publicBounds
            4 0 body values suffix
              (by simp [CompactProofRootFormulaFailureTagBinder])
              hsequent hformula
      · rcases compactNodeSequentFormulaFields_some_results hfirst with
          ⟨values, afterSequent, secondInput,
            hsequent, hfirstParser, hsuffix⟩
        rw [hsuffix] at hsecond
        rcases
            FoundationCompactNumericListedDirectProofRootTwoFormulaFailurePublicBounds.exists_compactProofRootTwoFormulaFailureEndpointBoundedGraph_of_results_with_publicBounds
              4 body values afterSequent secondInput (Or.inr rfl)
                hsequent hfirstParser hsecond with
          ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
            bodyStart, bodyFinish, branchBound, hinput, hbranch, hbounds⟩
        rcases lift_two_with_publicBounds hinput hbranch hbounds with
          ⟨endpointBound, hinput, hgraph, hpublic⟩
        exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound, hinput, hgraph, hpublic⟩
  | tag5 body hnode =>
      rcases (compactNodeSequentFormulaFields_eq_none_iff 1 body).mp hnode with
        hsequent | ⟨values, suffix, hsequent, hformula⟩
      · exact exists_aggregate_sequent_with_publicBounds
          5 body (by omega) hsequent
      · exact exists_aggregate_formula_with_publicBounds
          5 1 body values suffix
            (by simp [CompactProofRootFormulaFailureTagBinder])
            hsequent hformula
  | tag6 body hnode =>
      rcases (compactNodeSequentFormulaTermFields_eq_none_iff 1 0 body).mp hnode with
        hfirst | ⟨firstFields, hfirst, hterm⟩
      · rcases (compactNodeSequentFormulaFields_eq_none_iff 1 body).mp hfirst with
          hsequent | ⟨values, suffix, hsequent, hformula⟩
        · exact exists_aggregate_sequent_with_publicBounds
            6 body (by omega) hsequent
        · exact exists_aggregate_formula_with_publicBounds
            6 1 body values suffix
              (by simp [CompactProofRootFormulaFailureTagBinder])
              hsequent hformula
      · rcases compactNodeSequentFormulaFields_some_results hfirst with
          ⟨values, afterSequent, secondInput,
            hsequent, hfirstParser, hsuffix⟩
        rw [hsuffix] at hterm
        rcases
            FoundationCompactNumericListedDirectProofRootFormulaTermFailurePublicBounds.exists_compactProofRootFormulaTermFailureEndpointBoundedGraph_of_results_with_publicBounds
              body values afterSequent secondInput
                hsequent hfirstParser hterm with
          ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
            bodyStart, bodyFinish, branchBound, hinput, hbranch, hbounds⟩
        rcases lift_term_with_publicBounds hinput hbranch hbounds with
          ⟨endpointBound, hinput, hgraph, hpublic⟩
        exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound, hinput, hgraph, hpublic⟩
  | tag7 body hnode =>
      exact exists_aggregate_sequent_with_publicBounds
        7 body (by omega) (by
          simpa [compactNodeSequentOnlyFields] using hnode)
  | tag8 body hnode =>
      exact exists_aggregate_sequent_with_publicBounds
        8 body (by omega) (by
          simpa [compactNodeSequentOnlyFields] using hnode)
  | tag9 body hnode =>
      rcases (compactNodeSequentFormulaFields_eq_none_iff 0 body).mp hnode with
        hsequent | ⟨values, suffix, hsequent, hformula⟩
      · exact exists_aggregate_sequent_with_publicBounds
          9 body (by omega) hsequent
      · exact exists_aggregate_formula_with_publicBounds
          9 0 body values suffix
            (by simp [CompactProofRootFormulaFailureTagBinder])
            hsequent hformula

#print axioms
  exists_compactProofRootFailureEndpointBoundedGraph_of_none_with_publicBounds

end FoundationCompactNumericListedDirectProofRootFailurePublicBounds
