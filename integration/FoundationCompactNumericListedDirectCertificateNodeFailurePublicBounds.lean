import integration.FoundationCompactNumericListedDirectCertificateNodeOuterFailurePublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodePAImmediateFailurePublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailurePublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAFailurePublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeFailureBoundedFormula

/-!
# Public bounds for every structural-certificate parser failure

The structural-certificate parser has four exhaustive failure families.  This
file dispatches on its exact failure shape and lifts every exposed coordinate
to one explicit budget depending only on the original input weight.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeFailurePublicBounds

open FoundationCompactArithmeticSymbolCode
open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectCertificateNodeFailureSemantics
open FoundationCompactNumericListedDirectCertificateNodeOuterFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeFailureBoundedFormula

def compactCertificateNodeFailureBranchCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  FoundationCompactNumericListedDirectCertificateNodeOuterFailurePublicBounds.compactCertificateNodeOuterFailurePublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectCertificateNodePAImmediateFailurePublicBounds.compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailurePublicBounds.compactCertificateNodeSymbolPAFailurePublicCoordinateSizeBound
      inputWeight +
    FoundationCompactNumericListedDirectCertificateNodeInductionPAFailurePublicBounds.compactCertificateNodeInductionPAFailurePublicCoordinateSizeBound
      inputWeight

/-- The outer failure branch adds two tail endpoints to its local bound. -/
def compactCertificateNodeFailurePublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  3 * compactCertificateNodeFailureBranchCoordinateSizeBound inputWeight + 2

structure CompactCertificateNodeFailurePublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish endpointBound
      bound : Nat) : Prop where
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
    FoundationCompactNumericListedDirectCertificateNodeOuterFailurePublicBounds.compactCertificateNodeOuterFailurePublicCoordinateSizeBound
        inputWeight <=
      compactCertificateNodeFailureBranchCoordinateSizeBound inputWeight := by
  unfold compactCertificateNodeFailureBranchCoordinateSizeBound
  omega

private theorem immediateBound_le_branchBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectCertificateNodePAImmediateFailurePublicBounds.compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
        inputWeight <=
      compactCertificateNodeFailureBranchCoordinateSizeBound inputWeight := by
  unfold compactCertificateNodeFailureBranchCoordinateSizeBound
  omega

private theorem symbolBound_le_branchBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailurePublicBounds.compactCertificateNodeSymbolPAFailurePublicCoordinateSizeBound
        inputWeight <=
      compactCertificateNodeFailureBranchCoordinateSizeBound inputWeight := by
  unfold compactCertificateNodeFailureBranchCoordinateSizeBound
  omega

private theorem inductionBound_le_branchBound (inputWeight : Nat) :
    FoundationCompactNumericListedDirectCertificateNodeInductionPAFailurePublicBounds.compactCertificateNodeInductionPAFailurePublicCoordinateSizeBound
        inputWeight <=
      compactCertificateNodeFailureBranchCoordinateSizeBound inputWeight := by
  unfold compactCertificateNodeFailureBranchCoordinateSizeBound
  omega

private theorem branchBound_le_publicBound (inputWeight : Nat) :
    compactCertificateNodeFailureBranchCoordinateSizeBound inputWeight <=
      compactCertificateNodeFailurePublicCoordinateSizeBound inputWeight := by
  unfold compactCertificateNodeFailurePublicCoordinateSizeBound
  omega

private theorem package_direct_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hgraph : CompactCertificateNodeFailureBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound)
    (htokenTable :
      Nat.size tokenTable <=
        compactCertificateNodeFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (hwidth :
      Nat.size width <=
        compactCertificateNodeFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (htokenCount :
      Nat.size tokenCount <=
        compactCertificateNodeFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (hinputStart :
      Nat.size inputStart <=
        compactCertificateNodeFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (hinputFinish :
      Nat.size inputFinish <=
        compactCertificateNodeFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input))
    (hendpointBound :
      Nat.size endpointBound <=
        compactCertificateNodeFailureBranchCoordinateSizeBound
          (compactAdditiveValueWeight input)) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeFailureBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactCertificateNodeFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactCertificateNodeFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  have hlift :=
    branchBound_le_publicBound (compactAdditiveValueWeight input)
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinput, hgraph,
    { tokenTable := htokenTable.trans hlift
      width := hwidth.trans hlift
      tokenCount := htokenCount.trans hlift
      inputStart := hinputStart.trans hlift
      inputFinish := hinputFinish.trans hlift
      endpointBound := hendpointBound.trans hlift }⟩

private theorem lift_outer_with_publicBounds
    {input : List Nat}
    {tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish outerBound : Nat}
    (hinput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (houter : CompactCertificateNodeOuterFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        tailStart tailFinish outerBound)
    (hbounds :
      FoundationCompactNumericListedDirectCertificateNodeOuterFailurePublicBounds.CompactCertificateNodeOuterFailurePublicCoordinateBounds
        tokenTable width tokenCount inputStart inputFinish
          tailStart tailFinish outerBound
          (FoundationCompactNumericListedDirectCertificateNodeOuterFailurePublicBounds.compactCertificateNodeOuterFailurePublicCoordinateSizeBound
            (compactAdditiveValueWeight input))) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeFailureBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactCertificateNodeFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactCertificateNodeFailurePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  let endpointBound := tailStart + tailFinish + outerBound
  have hbranchLift :=
    outerBound_le_branchBound (compactAdditiveValueWeight input)
  have hpublicLift :=
    branchBound_le_publicBound (compactAdditiveValueWeight input)
  have hendpointRaw := natSize_three_add_le tailStart tailFinish outerBound
  have htailStart := hbounds.tailStart
  have htailFinish := hbounds.tailFinish
  have houterBound := hbounds.endpointBound
  have hendpoint :
      Nat.size endpointBound <=
        compactCertificateNodeFailurePublicCoordinateSizeBound
          (compactAdditiveValueWeight input) := by
    dsimp only [endpointBound]
    unfold compactCertificateNodeFailurePublicCoordinateSizeBound
    omega
  have hgraph : CompactCertificateNodeFailureBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound := by
    exact Or.inl
      ⟨tailStart, by dsimp only [endpointBound]; omega,
        tailFinish, by dsimp only [endpointBound]; omega,
        outerBound, by dsimp only [endpointBound]; omega, houter⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hinput, hgraph,
    { tokenTable := (hbounds.tokenTable.trans hbranchLift).trans hpublicLift
      width := (hbounds.width.trans hbranchLift).trans hpublicLift
      tokenCount := (hbounds.tokenCount.trans hbranchLift).trans hpublicLift
      inputStart := (hbounds.inputStart.trans hbranchLift).trans hpublicLift
      inputFinish := (hbounds.inputFinish.trans hbranchLift).trans hpublicLift
      endpointBound := hendpoint }⟩

/- Every failed structural-certificate parse constructs the exact unified
failure graph with a public coordinate budget. -/
set_option maxHeartbeats 2400000 in
theorem
    exists_compactCertificateNodeFailureBoundedGraph_of_parser_none_with_publicBounds
    (input : List Nat)
    (hparser : compactStructuralCertificateNodeParser input = none) :
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeFailureBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactCertificateNodeFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactCertificateNodeFailurePublicCoordinateSizeBound
              inputWeight) := by
  have hshape :=
    (compactStructuralCertificateNodeParser_eq_none_iff_failureShape
      input).mp hparser
  rcases hshape with rfl | ⟨tag, tail, rfl, hnode⟩
  · rcases
        FoundationCompactNumericListedDirectCertificateNodeOuterFailurePublicBounds.exists_compactCertificateNodeOuterFailureEndpointBoundedGraph_of_empty_with_publicBounds with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        tailStart, tailFinish, outerBound, hinput, houter, hbounds⟩
    exact lift_outer_with_publicBounds hinput houter hbounds
  · rcases hnode with ⟨rfl, hpa⟩ | ⟨h0, h1, h2, h3⟩
    · rcases hpa with rfl | ⟨paTag, body, rfl, hpafailure⟩
      · rcases
            FoundationCompactNumericListedDirectCertificateNodePAImmediateFailurePublicBounds.exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_empty_with_publicBounds with
          ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
            endpointBound, hinput, himmediate, hbounds⟩
        have hlift :=
          immediateBound_le_branchBound (compactAdditiveValueWeight [1])
        exact package_direct_with_publicBounds hinput
          (Or.inr (Or.inl himmediate))
          (hbounds.tokenTable.trans hlift)
          (hbounds.width.trans hlift)
          (hbounds.tokenCount.trans hlift)
          (hbounds.inputStart.trans hlift)
          (hbounds.inputFinish.trans hlift)
          (hbounds.endpointBound.trans hlift)
      · rcases hpafailure with hfunc | hrel | hformula | hlarge
        · rcases hfunc with ⟨rfl, hshort | hinvalid⟩
          · rcases
                FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailurePublicBounds.exists_compactCertificateNodeSymbolPAFailureEndpointBoundedGraph_with_publicBounds
                  3 body (Or.inl rfl) (Or.inl hshort) with
              ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound, hinput, hsymbol, hbounds⟩
            have hlift := symbolBound_le_branchBound
              (compactAdditiveValueWeight (1 :: 3 :: body))
            exact package_direct_with_publicBounds hinput
              (Or.inr (Or.inr (Or.inl hsymbol)))
              (hbounds.tokenTable.trans hlift)
              (hbounds.width.trans hlift)
              (hbounds.tokenCount.trans hlift)
              (hbounds.inputStart.trans hlift)
              (hbounds.inputFinish.trans hlift)
              (hbounds.endpointBound.trans hlift)
          · rcases
                FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailurePublicBounds.exists_compactCertificateNodeSymbolPAFailureEndpointBoundedGraph_with_publicBounds
                  3 body (Or.inl rfl)
                    (Or.inr (Or.inl ⟨rfl, hinvalid⟩)) with
              ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound, hinput, hsymbol, hbounds⟩
            have hlift := symbolBound_le_branchBound
              (compactAdditiveValueWeight (1 :: 3 :: body))
            exact package_direct_with_publicBounds hinput
              (Or.inr (Or.inr (Or.inl hsymbol)))
              (hbounds.tokenTable.trans hlift)
              (hbounds.width.trans hlift)
              (hbounds.tokenCount.trans hlift)
              (hbounds.inputStart.trans hlift)
              (hbounds.inputFinish.trans hlift)
              (hbounds.endpointBound.trans hlift)
        · rcases hrel with ⟨rfl, hshort | hinvalid⟩
          · rcases
                FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailurePublicBounds.exists_compactCertificateNodeSymbolPAFailureEndpointBoundedGraph_with_publicBounds
                  4 body (Or.inr rfl) (Or.inl hshort) with
              ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound, hinput, hsymbol, hbounds⟩
            have hlift := symbolBound_le_branchBound
              (compactAdditiveValueWeight (1 :: 4 :: body))
            exact package_direct_with_publicBounds hinput
              (Or.inr (Or.inr (Or.inl hsymbol)))
              (hbounds.tokenTable.trans hlift)
              (hbounds.width.trans hlift)
              (hbounds.tokenCount.trans hlift)
              (hbounds.inputStart.trans hlift)
              (hbounds.inputFinish.trans hlift)
              (hbounds.endpointBound.trans hlift)
          · rcases
                FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailurePublicBounds.exists_compactCertificateNodeSymbolPAFailureEndpointBoundedGraph_with_publicBounds
                  4 body (Or.inr rfl)
                    (Or.inr (Or.inr ⟨rfl, hinvalid⟩)) with
              ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
                endpointBound, hinput, hsymbol, hbounds⟩
            have hlift := symbolBound_le_branchBound
              (compactAdditiveValueWeight (1 :: 4 :: body))
            exact package_direct_with_publicBounds hinput
              (Or.inr (Or.inr (Or.inl hsymbol)))
              (hbounds.tokenTable.trans hlift)
              (hbounds.width.trans hlift)
              (hbounds.tokenCount.trans hlift)
              (hbounds.inputStart.trans hlift)
              (hbounds.inputFinish.trans hlift)
              (hbounds.endpointBound.trans hlift)
        · rcases hformula with ⟨rfl, hformula⟩
          rcases
              FoundationCompactNumericListedDirectCertificateNodeInductionPAFailurePublicBounds.exists_compactCertificateNodeInductionPAFailureEndpointBoundedGraph_with_publicBounds
                body hformula with
            ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
              endpointBound, hinput, hinduction, hbounds⟩
          have hlift := inductionBound_le_branchBound
            (compactAdditiveValueWeight (1 :: 22 :: body))
          exact package_direct_with_publicBounds hinput
            (Or.inr (Or.inr (Or.inr hinduction)))
            (hbounds.tokenTable.trans hlift)
            (hbounds.width.trans hlift)
            (hbounds.tokenCount.trans hlift)
            (hbounds.inputStart.trans hlift)
            (hbounds.inputFinish.trans hlift)
            (hbounds.endpointBound.trans hlift)
        · rcases
              FoundationCompactNumericListedDirectCertificateNodePAImmediateFailurePublicBounds.exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_large_with_publicBounds
                paTag body hlarge with
            ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
              endpointBound, hinput, himmediate, hbounds⟩
          have hlift := immediateBound_le_branchBound
            (compactAdditiveValueWeight (1 :: paTag :: body))
          exact package_direct_with_publicBounds hinput
            (Or.inr (Or.inl himmediate))
            (hbounds.tokenTable.trans hlift)
            (hbounds.width.trans hlift)
            (hbounds.tokenCount.trans hlift)
            (hbounds.inputStart.trans hlift)
            (hbounds.inputFinish.trans hlift)
            (hbounds.endpointBound.trans hlift)
    · rcases
          FoundationCompactNumericListedDirectCertificateNodeOuterFailurePublicBounds.exists_compactCertificateNodeOuterFailureEndpointBoundedGraph_of_invalid_with_publicBounds
            tag tail h0 h1 h2 h3 with
        ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
          tailStart, tailFinish, outerBound, hinput, houter, hbounds⟩
      exact lift_outer_with_publicBounds hinput houter hbounds

#print axioms
  exists_compactCertificateNodeFailureBoundedGraph_of_parser_none_with_publicBounds

end FoundationCompactNumericListedDirectCertificateNodeFailurePublicBounds
