import integration.FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
import integration.FoundationCompactNumericListedDirectProofRootOneFormulaPublicBounds
import integration.FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds
import integration.FoundationCompactNumericListedDirectProofRootTwoFormulaPublicBounds
import integration.FoundationCompactNumericListedDirectProofRootFormulaTermPublicBounds
import integration.FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula

/-!
# Public bounds for every successful proof-root branch

The public proof-root parser has ten successful tags but only five endpoint
families.  This file dispatches on the actual parser result, keeps the exact
branch construction, and lifts the eight exposed success coordinates to one
explicit input-weight budget.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootSuccessPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectProofRootSequentOnlyBoundedFormula
open FoundationCompactNumericListedDirectProofRootOneFormulaBoundedFormula
open FoundationCompactNumericListedDirectProofRootClosedFormulaBoundedFormula
open FoundationCompactNumericListedDirectProofRootTwoFormulaBoundedFormula
open FoundationCompactNumericListedDirectProofRootFormulaTermBoundedFormula
open FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula

/-- The sum of all five branch budgets dominates the budget of whichever
successful parser branch is selected. -/
def compactProofRootSuccessBranchCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.compactProofRootSequentOnlyPublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectProofRootOneFormulaPublicBounds.compactProofRootOneFormulaPublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds.compactProofRootOneFormulaPublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectProofRootTwoFormulaPublicBounds.compactProofRootTwoFormulaPublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectProofRootFormulaTermPublicBounds.compactProofRootFormulaTermPublicCoordinateSizeBound
      inputWeight

/-- The outer success endpoint is the sum of two body coordinates and the
selected branch bound.  Three copies of the common branch budget, plus the two
binary-addition carry bits, therefore bound its binary size. -/
def compactProofRootSuccessPublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  3 * compactProofRootSuccessBranchCoordinateSizeBound inputWeight + 2

theorem compactProofRootSuccessBranchCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactProofRootSuccessBranchCoordinateSizeBound left <=
      compactProofRootSuccessBranchCoordinateSizeBound right := by
  have hsequent :=
    FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.compactProofRootSequentOnlyPublicCoordinateSizeBound_mono h
  have hone :=
    FoundationCompactNumericListedDirectProofRootOneFormulaPublicBounds.compactProofRootOneFormulaPublicCoordinateSizeBound_mono h
  have hclosed :=
    FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds.compactProofRootClosedFormulaPublicCoordinateSizeBound_mono h
  have htwo :=
    FoundationCompactNumericListedDirectProofRootTwoFormulaPublicBounds.compactProofRootTwoFormulaPublicCoordinateSizeBound_mono h
  have hterm :=
    FoundationCompactNumericListedDirectProofRootFormulaTermPublicBounds.compactProofRootFormulaTermPublicCoordinateSizeBound_mono h
  unfold compactProofRootSuccessBranchCoordinateSizeBound
  omega

theorem compactProofRootSuccessPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactProofRootSuccessPublicCoordinateSizeBound left <=
      compactProofRootSuccessPublicCoordinateSizeBound right := by
  have hbranch := compactProofRootSuccessBranchCoordinateSizeBound_mono h
  unfold compactProofRootSuccessPublicCoordinateSizeBound
  omega

structure CompactProofRootSuccessPublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish endpointBound bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width_value : width <= bound
  width : Nat.size width <= bound
  tokenCount_value : tokenCount <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  rootStart : Nat.size rootStart <= bound
  rootFinish : Nat.size rootFinish <= bound
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

private theorem sequentBound_le_successBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.compactProofRootSequentOnlyPublicCoordinateSizeBound
        inputWeight <=
      compactProofRootSuccessPublicCoordinateSizeBound inputWeight := by
  unfold compactProofRootSuccessPublicCoordinateSizeBound
  unfold compactProofRootSuccessBranchCoordinateSizeBound
  omega

private theorem oneBound_le_successBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootOneFormulaPublicBounds.compactProofRootOneFormulaPublicCoordinateSizeBound
        inputWeight <=
      compactProofRootSuccessPublicCoordinateSizeBound inputWeight := by
  unfold compactProofRootSuccessPublicCoordinateSizeBound
  unfold compactProofRootSuccessBranchCoordinateSizeBound
  omega

private theorem closedBound_le_successBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds.compactProofRootOneFormulaPublicCoordinateSizeBound
        inputWeight <=
      compactProofRootSuccessPublicCoordinateSizeBound inputWeight := by
  unfold compactProofRootSuccessPublicCoordinateSizeBound
  unfold compactProofRootSuccessBranchCoordinateSizeBound
  omega

private theorem twoBound_le_successBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootTwoFormulaPublicBounds.compactProofRootTwoFormulaPublicCoordinateSizeBound
        inputWeight <=
      compactProofRootSuccessPublicCoordinateSizeBound inputWeight := by
  unfold compactProofRootSuccessPublicCoordinateSizeBound
  unfold compactProofRootSuccessBranchCoordinateSizeBound
  omega

private theorem termBound_le_successBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectProofRootFormulaTermPublicBounds.compactProofRootFormulaTermPublicCoordinateSizeBound
        inputWeight <=
      compactProofRootSuccessPublicCoordinateSizeBound inputWeight := by
  unfold compactProofRootSuccessPublicCoordinateSizeBound
  unfold compactProofRootSuccessBranchCoordinateSizeBound
  omega

private theorem compactProofRootParser_success_tag_cases
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root) :
    root.1 = 0 \/ root.1 = 1 \/ root.1 = 2 \/ root.1 = 3 \/
      root.1 = 4 \/ root.1 = 5 \/ root.1 = 6 \/ root.1 = 7 \/
      root.1 = 8 \/ root.1 = 9 := by
  have hvalid :=
    (compactListedProofNodeFieldsParser_eq_some_iff_branchValid
      input root).mp hparser
  cases input with
  | nil =>
      simp [CompactNumericProofRootBranchValid] at hvalid
  | cons tag body =>
      by_cases h0 : tag = 0
      · have hbranch : root.1 = 0 /\
            compactNodeSequentFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, h0] using hvalid
        exact Or.inl hbranch.1
      by_cases h1 : tag = 1
      · have hbranch : root.1 = 1 /\
            compactNodeSequentClosedFormulaFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, h0, h1] using hvalid
        exact Or.inr (Or.inl hbranch.1)
      by_cases h2 : tag = 2
      · have hbranch : root.1 = 2 /\
            compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, h0, h1, h2] using hvalid
        exact Or.inr (Or.inr (Or.inl hbranch.1))
      by_cases h3 : tag = 3
      · have hbranch : root.1 = 3 /\
            compactNodeSequentTwoFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inl hbranch.1)))
      by_cases h4 : tag = 4
      · have hbranch : root.1 = 4 /\
            compactNodeSequentTwoFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbranch.1))))
      by_cases h5 : tag = 5
      · have hbranch : root.1 = 5 /\
            compactNodeSequentFormulaFields 1 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hbranch.1)))))
      by_cases h6 : tag = 6
      · have hbranch : root.1 = 6 /\
            compactNodeSequentFormulaTermFields 1 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl hbranch.1))))))
      by_cases h7 : tag = 7
      · have hbranch : root.1 = 7 /\
            compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6, h7] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl hbranch.1)))))))
      by_cases h8 : tag = 8
      · have hbranch : root.1 = 8 /\
            compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6, h7, h8] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbranch.1))))))))
      by_cases h9 : tag = 9
      · have hbranch : root.1 = 9 /\
            compactNodeSequentFormulaFields 0 body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid,
            h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] using hvalid
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbranch.1))))))))
      simp [CompactNumericProofRootBranchValid,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at hvalid

private theorem lift_sequent_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootSequentOnlyEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.CompactProofRootSequentOnlyPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish branchBound
            (FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.compactProofRootSequentOnlyPublicCoordinateSizeBound
                (compactAdditiveValueWeight input))) :
    exists endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input /\
        CompactProofRootSuccessBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound /\
        CompactProofRootSuccessPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound
            (compactProofRootSuccessPublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  have hlift :=
    sequentBound_le_successBound (compactAdditiveValueWeight input)
  have hendpoint :
      Nat.size endpointBound <=
        compactProofRootSuccessPublicCoordinateSizeBound
          (compactAdditiveValueWeight input) := by
    have hsum := natSize_three_add_le bodyStart bodyFinish branchBound
    have hbodyStart := hbounds.bodyStart
    have hbodyFinish := hbounds.bodyFinish
    have hbranchBound := hbounds.endpointBound
    dsimp only [endpointBound]
    unfold compactProofRootSuccessPublicCoordinateSizeBound
    unfold compactProofRootSuccessBranchCoordinateSizeBound
    omega
  refine ⟨endpointBound, hinput, ?_, ?_⟩
  · exact Or.inl
      ⟨bodyStart, by dsimp only [endpointBound]; omega,
        bodyFinish, by dsimp only [endpointBound]; omega,
        branchBound, by dsimp only [endpointBound]; omega, hbranch⟩
  · exact
      { tokenTable := hbounds.tokenTable.trans hlift
        width := hbounds.width.trans hlift
        width_value := hbounds.width_value.trans hlift
        tokenCount := hbounds.tokenCount.trans hlift
        tokenCount_value := hbounds.tokenCount_value.trans hlift
        inputStart := hbounds.inputStart.trans hlift
        inputFinish := hbounds.inputFinish.trans hlift
        rootStart := hbounds.rootStart.trans hlift
        rootFinish := hbounds.rootFinish.trans hlift
        endpointBound := hendpoint }

private theorem lift_one_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootOneFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootOneFormulaPublicBounds.CompactProofRootOneFormulaPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish branchBound
            (FoundationCompactNumericListedDirectProofRootOneFormulaPublicBounds.compactProofRootOneFormulaPublicCoordinateSizeBound
                (compactAdditiveValueWeight input))) :
    exists endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input /\
        CompactProofRootSuccessBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound /\
        CompactProofRootSuccessPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound
            (compactProofRootSuccessPublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  have hlift := oneBound_le_successBound (compactAdditiveValueWeight input)
  have hendpoint :
      Nat.size endpointBound <=
        compactProofRootSuccessPublicCoordinateSizeBound
          (compactAdditiveValueWeight input) := by
    have hsum := natSize_three_add_le bodyStart bodyFinish branchBound
    have hbodyStart := hbounds.bodyStart
    have hbodyFinish := hbounds.bodyFinish
    have hbranchBound := hbounds.endpointBound
    dsimp only [endpointBound]
    unfold compactProofRootSuccessPublicCoordinateSizeBound
    unfold compactProofRootSuccessBranchCoordinateSizeBound
    omega
  refine ⟨endpointBound, hinput, ?_, ?_⟩
  · exact Or.inr (Or.inl
      ⟨bodyStart, by dsimp only [endpointBound]; omega,
        bodyFinish, by dsimp only [endpointBound]; omega,
        branchBound, by dsimp only [endpointBound]; omega, hbranch⟩)
  · exact
      { tokenTable := hbounds.tokenTable.trans hlift
        width := hbounds.width.trans hlift
        width_value := hbounds.width_value.trans hlift
        tokenCount := hbounds.tokenCount.trans hlift
        tokenCount_value := hbounds.tokenCount_value.trans hlift
        inputStart := hbounds.inputStart.trans hlift
        inputFinish := hbounds.inputFinish.trans hlift
        rootStart := hbounds.rootStart.trans hlift
        rootFinish := hbounds.rootFinish.trans hlift
        endpointBound := hendpoint }

private theorem lift_closed_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootClosedFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds.CompactProofRootOneFormulaPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish branchBound
            (FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds.compactProofRootOneFormulaPublicCoordinateSizeBound
                (compactAdditiveValueWeight input))) :
    exists endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input /\
        CompactProofRootSuccessBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound /\
        CompactProofRootSuccessPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound
            (compactProofRootSuccessPublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  have hlift := closedBound_le_successBound (compactAdditiveValueWeight input)
  have hendpoint :
      Nat.size endpointBound <=
        compactProofRootSuccessPublicCoordinateSizeBound
          (compactAdditiveValueWeight input) := by
    have hsum := natSize_three_add_le bodyStart bodyFinish branchBound
    have hbodyStart := hbounds.bodyStart
    have hbodyFinish := hbounds.bodyFinish
    have hbranchBound := hbounds.endpointBound
    dsimp only [endpointBound]
    unfold compactProofRootSuccessPublicCoordinateSizeBound
    unfold compactProofRootSuccessBranchCoordinateSizeBound
    omega
  refine ⟨endpointBound, hinput, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inl
      ⟨bodyStart, by dsimp only [endpointBound]; omega,
        bodyFinish, by dsimp only [endpointBound]; omega,
        branchBound, by dsimp only [endpointBound]; omega, hbranch⟩))
  · exact
      { tokenTable := hbounds.tokenTable.trans hlift
        width := hbounds.width.trans hlift
        width_value := hbounds.width_value.trans hlift
        tokenCount := hbounds.tokenCount.trans hlift
        tokenCount_value := hbounds.tokenCount_value.trans hlift
        inputStart := hbounds.inputStart.trans hlift
        inputFinish := hbounds.inputFinish.trans hlift
        rootStart := hbounds.rootStart.trans hlift
        rootFinish := hbounds.rootFinish.trans hlift
        endpointBound := hendpoint }

private theorem lift_two_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootTwoFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootTwoFormulaPublicBounds.CompactProofRootTwoFormulaPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish branchBound
            (FoundationCompactNumericListedDirectProofRootTwoFormulaPublicBounds.compactProofRootTwoFormulaPublicCoordinateSizeBound
                (compactAdditiveValueWeight input))) :
    exists endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input /\
        CompactProofRootSuccessBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound /\
        CompactProofRootSuccessPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound
            (compactProofRootSuccessPublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  have hlift := twoBound_le_successBound (compactAdditiveValueWeight input)
  have hendpoint :
      Nat.size endpointBound <=
        compactProofRootSuccessPublicCoordinateSizeBound
          (compactAdditiveValueWeight input) := by
    have hsum := natSize_three_add_le bodyStart bodyFinish branchBound
    have hbodyStart := hbounds.bodyStart
    have hbodyFinish := hbounds.bodyFinish
    have hbranchBound := hbounds.endpointBound
    dsimp only [endpointBound]
    unfold compactProofRootSuccessPublicCoordinateSizeBound
    unfold compactProofRootSuccessBranchCoordinateSizeBound
    omega
  refine ⟨endpointBound, hinput, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨bodyStart, by dsimp only [endpointBound]; omega,
        bodyFinish, by dsimp only [endpointBound]; omega,
        branchBound, by dsimp only [endpointBound]; omega, hbranch⟩)))
  · exact
      { tokenTable := hbounds.tokenTable.trans hlift
        width := hbounds.width.trans hlift
        width_value := hbounds.width_value.trans hlift
        tokenCount := hbounds.tokenCount.trans hlift
        tokenCount_value := hbounds.tokenCount_value.trans hlift
        inputStart := hbounds.inputStart.trans hlift
        inputFinish := hbounds.inputFinish.trans hlift
        rootStart := hbounds.rootStart.trans hlift
        rootFinish := hbounds.rootFinish.trans hlift
        endpointBound := hendpoint }

private theorem lift_term_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish branchBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hbranch : CompactProofRootFormulaTermEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish bodyStart bodyFinish branchBound)
    (hbounds :
      FoundationCompactNumericListedDirectProofRootFormulaTermPublicBounds.CompactProofRootFormulaTermPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish branchBound
            (FoundationCompactNumericListedDirectProofRootFormulaTermPublicBounds.compactProofRootFormulaTermPublicCoordinateSizeBound
                (compactAdditiveValueWeight input))) :
    exists endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input /\
        CompactProofRootSuccessBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound /\
        CompactProofRootSuccessPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound
            (compactProofRootSuccessPublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  let endpointBound := bodyStart + bodyFinish + branchBound
  have hlift := termBound_le_successBound (compactAdditiveValueWeight input)
  have hendpoint :
      Nat.size endpointBound <=
        compactProofRootSuccessPublicCoordinateSizeBound
          (compactAdditiveValueWeight input) := by
    have hsum := natSize_three_add_le bodyStart bodyFinish branchBound
    have hbodyStart := hbounds.bodyStart
    have hbodyFinish := hbounds.bodyFinish
    have hbranchBound := hbounds.endpointBound
    dsimp only [endpointBound]
    unfold compactProofRootSuccessPublicCoordinateSizeBound
    unfold compactProofRootSuccessBranchCoordinateSizeBound
    omega
  refine ⟨endpointBound, hinput, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨bodyStart, by dsimp only [endpointBound]; omega,
        bodyFinish, by dsimp only [endpointBound]; omega,
        branchBound, by dsimp only [endpointBound]; omega, hbranch⟩)))
  · exact
      { tokenTable := hbounds.tokenTable.trans hlift
        width := hbounds.width.trans hlift
        width_value := hbounds.width_value.trans hlift
        tokenCount := hbounds.tokenCount.trans hlift
        tokenCount_value := hbounds.tokenCount_value.trans hlift
        inputStart := hbounds.inputStart.trans hlift
        inputFinish := hbounds.inputFinish.trans hlift
        rootStart := hbounds.rootStart.trans hlift
        rootFinish := hbounds.rootFinish.trans hlift
        endpointBound := hendpoint }

/- Every successful proof-root parse constructs the exact unified success
graph, with all eight exposed coordinates bounded from the original input. -/
set_option maxHeartbeats 1800000 in
theorem
    exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_publicBounds
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root) :
    let inputWeight := compactAdditiveValueWeight input
    exists tokenTable width tokenCount inputStart inputFinish,
    exists rootStart rootFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input /\
        CompactProofRootSuccessBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound /\
        CompactProofRootSuccessPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish endpointBound
            (compactProofRootSuccessPublicCoordinateSizeBound
              inputWeight) := by
  rcases compactProofRootParser_success_tag_cases hparser with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · rcases
        FoundationCompactNumericListedDirectProofRootOneFormulaPublicBounds.exists_compactProofRootOneFormulaEndpointBoundedGraph_of_success_with_publicBounds
            hparser (Or.inl h0) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, branchBound,
        hinput, hbranch, hbounds⟩
    rcases lift_one_with_publicBounds hinput hbranch hbounds with
      ⟨endpointBound, hinput, hsuccess, hpublic⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinput, hsuccess, hpublic⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootClosedFormulaPublicBounds.exists_compactProofRootClosedFormulaEndpointBoundedGraph_of_success_with_publicBounds
            hparser h1 with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, branchBound,
        hinput, hbranch, hbounds⟩
    rcases lift_closed_with_publicBounds hinput hbranch hbounds with
      ⟨endpointBound, hinput, hsuccess, hpublic⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinput, hsuccess, hpublic⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_success_with_publicBounds
            hparser (Or.inl h2) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, branchBound,
        hinput, hbranch, hbounds⟩
    rcases lift_sequent_with_publicBounds hinput hbranch hbounds with
      ⟨endpointBound, hinput, hsuccess, hpublic⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinput, hsuccess, hpublic⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootTwoFormulaPublicBounds.exists_compactProofRootTwoFormulaEndpointBoundedGraph_of_success_with_publicBounds
            hparser (Or.inl h3) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, branchBound,
        hinput, hbranch, hbounds⟩
    rcases lift_two_with_publicBounds hinput hbranch hbounds with
      ⟨endpointBound, hinput, hsuccess, hpublic⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinput, hsuccess, hpublic⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootTwoFormulaPublicBounds.exists_compactProofRootTwoFormulaEndpointBoundedGraph_of_success_with_publicBounds
            hparser (Or.inr h4) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, branchBound,
        hinput, hbranch, hbounds⟩
    rcases lift_two_with_publicBounds hinput hbranch hbounds with
      ⟨endpointBound, hinput, hsuccess, hpublic⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinput, hsuccess, hpublic⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootOneFormulaPublicBounds.exists_compactProofRootOneFormulaEndpointBoundedGraph_of_success_with_publicBounds
            hparser (Or.inr (Or.inl h5)) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, branchBound,
        hinput, hbranch, hbounds⟩
    rcases lift_one_with_publicBounds hinput hbranch hbounds with
      ⟨endpointBound, hinput, hsuccess, hpublic⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinput, hsuccess, hpublic⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootFormulaTermPublicBounds.exists_compactProofRootFormulaTermEndpointBoundedGraph_of_success_with_publicBounds
            hparser h6 with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, branchBound,
        hinput, hbranch, hbounds⟩
    rcases lift_term_with_publicBounds hinput hbranch hbounds with
      ⟨endpointBound, hinput, hsuccess, hpublic⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinput, hsuccess, hpublic⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_success_with_publicBounds
            hparser (Or.inr (Or.inl h7)) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, branchBound,
        hinput, hbranch, hbounds⟩
    rcases lift_sequent_with_publicBounds hinput hbranch hbounds with
      ⟨endpointBound, hinput, hsuccess, hpublic⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinput, hsuccess, hpublic⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds.exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_success_with_publicBounds
            hparser (Or.inr (Or.inr h8)) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, branchBound,
        hinput, hbranch, hbounds⟩
    rcases lift_sequent_with_publicBounds hinput hbranch hbounds with
      ⟨endpointBound, hinput, hsuccess, hpublic⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinput, hsuccess, hpublic⟩
  · rcases
        FoundationCompactNumericListedDirectProofRootOneFormulaPublicBounds.exists_compactProofRootOneFormulaEndpointBoundedGraph_of_success_with_publicBounds
            hparser (Or.inr (Or.inr h9)) with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        rootStart, rootFinish, bodyStart, bodyFinish, branchBound,
        hinput, hbranch, hbounds⟩
    rcases lift_one_with_publicBounds hinput hbranch hbounds with
      ⟨endpointBound, hinput, hsuccess, hpublic⟩
    exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, endpointBound, hinput, hsuccess, hpublic⟩

#print axioms
  exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_publicBounds
#print axioms compactProofRootSuccessPublicCoordinateSizeBound_mono

end FoundationCompactNumericListedDirectProofRootSuccessPublicBounds
