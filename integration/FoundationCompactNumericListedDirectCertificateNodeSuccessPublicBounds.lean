import integration.FoundationCompactNumericListedDirectCertificateNodeSimplePublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeFixedPAPublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAPublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAPublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula

/-!
# Public bounds for every successful structural-certificate node

The public structural-certificate parser has four successful branches.  This
file dispatches on the actual parser result and retains the branch-specific
canonical construction while lifting all thirteen exposed coordinates to one
input-weight budget.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds

open FoundationCompactPAAxiomCertificate
open FoundationCompactArithmeticSymbolCode
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactSyntaxTokenMachine
open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectCertificateNodeSuccessBoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSimplePublicBounds
open FoundationCompactNumericListedDirectCertificateNodeFixedPAPublicBounds
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAPublicBounds
open FoundationCompactNumericListedDirectCertificateNodeInductionPAPublicBounds

/-- One common binary-size budget for every public coordinate of every
successful structural-certificate branch. -/
def compactCertificateNodeSuccessPublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeSimplePublicCoordinateSizeBound inputWeight +
    compactCertificateNodeFixedPAPublicCoordinateSizeBound inputWeight +
    compactCertificateNodeSymbolPAPublicCoordinateSizeBound inputWeight +
    compactCertificateNodeInductionPAPublicCoordinateSizeBound inputWeight

theorem compactCertificateNodeSuccessPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactCertificateNodeSuccessPublicCoordinateSizeBound left <=
      compactCertificateNodeSuccessPublicCoordinateSizeBound right := by
  have hsimple :=
    compactCertificateNodeSimplePublicCoordinateSizeBound_mono h
  have hfixed :=
    compactCertificateNodeFixedPAPublicCoordinateSizeBound_mono h
  have hsymbol :=
    compactCertificateNodeSymbolPAPublicCoordinateSizeBound_mono h
  have hinduction :=
    compactCertificateNodeInductionPAPublicCoordinateSizeBound_mono h
  unfold compactCertificateNodeSuccessPublicCoordinateSizeBound
  omega

structure CompactCertificateNodeSuccessPublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound bound : Nat) :
  Prop where
  tokenTable : Nat.size tokenTable <= bound
  width_value : width <= bound
  width : Nat.size width <= bound
  tokenCount_value : tokenCount <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  axiomStart : Nat.size axiomStart <= bound
  axiomFinish : Nat.size axiomFinish <= bound
  formulaStart : Nat.size formulaStart <= bound
  formulaFinish : Nat.size formulaFinish <= bound
  suffixStart : Nat.size suffixStart <= bound
  suffixFinish : Nat.size suffixFinish <= bound
  certificateTag : Nat.size certificateTag <= bound
  endpointBound : Nat.size endpointBound <= bound

private theorem simpleBound_le_successBound (inputWeight : Nat) :
    compactCertificateNodeSimplePublicCoordinateSizeBound inputWeight <=
      compactCertificateNodeSuccessPublicCoordinateSizeBound inputWeight := by
  unfold compactCertificateNodeSuccessPublicCoordinateSizeBound
  omega

private theorem fixedBound_le_successBound (inputWeight : Nat) :
    compactCertificateNodeFixedPAPublicCoordinateSizeBound inputWeight <=
      compactCertificateNodeSuccessPublicCoordinateSizeBound inputWeight := by
  unfold compactCertificateNodeSuccessPublicCoordinateSizeBound
  omega

private theorem symbolBound_le_successBound (inputWeight : Nat) :
    compactCertificateNodeSymbolPAPublicCoordinateSizeBound inputWeight <=
      compactCertificateNodeSuccessPublicCoordinateSizeBound inputWeight := by
  unfold compactCertificateNodeSuccessPublicCoordinateSizeBound
  omega

private theorem inductionBound_le_successBound (inputWeight : Nat) :
    compactCertificateNodeInductionPAPublicCoordinateSizeBound inputWeight <=
      compactCertificateNodeSuccessPublicCoordinateSizeBound inputWeight := by
  unfold compactCertificateNodeSuccessPublicCoordinateSizeBound
  omega

private theorem zeroSize_le_successBound (inputWeight : Nat) :
    Nat.size 0 <=
      compactCertificateNodeSuccessPublicCoordinateSizeBound inputWeight := by
  simp

set_option maxHeartbeats 1800000 in
theorem
    exists_compactCertificateNodeSuccessBoundedGraph_of_parser_success_with_publicBounds
    {input : List Nat} {certificateTag : Nat}
    {axiomTokens suffix : List Nat}
    (hparser :
      compactStructuralCertificateNodeParser input =
        some (certificateTag, (axiomTokens, suffix))) :
    let inputWeight := compactAdditiveValueWeight input
    exists tokenTable width tokenCount inputStart inputFinish,
    exists axiomStart axiomFinish formulaStart formulaFinish,
    exists suffixStart suffixFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input /\
        CompactCertificateNodeSuccessBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag endpointBound /\
        CompactCertificateNodeSuccessPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag endpointBound
            (compactCertificateNodeSuccessPublicCoordinateSizeBound
              inputWeight) := by
  have simpleBranch
      (tag : Nat) (branchSuffix : List Nat)
      (htag : tag = 0 \/ tag = 2 \/ tag = 3) :
      let branchInput := tag :: branchSuffix
      let inputWeight := compactAdditiveValueWeight branchInput
      exists tokenTable width tokenCount inputStart inputFinish,
      exists axiomStart axiomFinish formulaStart formulaFinish,
      exists suffixStart suffixFinish endpointBound,
        CompactAdditiveNatListDirectLayout
            tokenTable width tokenCount inputStart inputFinish branchInput /\
          CompactCertificateNodeSuccessBoundedGraph
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish tag endpointBound /\
          CompactCertificateNodeSuccessPublicCoordinateBounds
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish tag endpointBound
              (compactCertificateNodeSuccessPublicCoordinateSizeBound
                inputWeight) := by
    let branchInput := tag :: branchSuffix
    let inputWeight := compactAdditiveValueWeight branchInput
    rcases
        exists_compactCertificateNodeSimpleEndpointBoundedGraph_with_publicBounds
          tag branchSuffix htag with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        suffixStart, suffixFinish, endpointBound,
        hinput, hsimple, hbounds⟩
    have hlift := simpleBound_le_successBound inputWeight
    refine
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        0, 0, 0, 0, suffixStart, suffixFinish, endpointBound,
        hinput, Or.inl hsimple, ?_⟩
    exact
      { tokenTable := hbounds.tokenTable.trans hlift
        width_value := hbounds.width_value.trans hlift
        width := hbounds.width.trans hlift
        tokenCount_value := hbounds.tokenCount_value.trans hlift
        tokenCount := hbounds.tokenCount.trans hlift
        inputStart := hbounds.inputStart.trans hlift
        inputFinish := hbounds.inputFinish.trans hlift
        axiomStart := zeroSize_le_successBound inputWeight
        axiomFinish := zeroSize_le_successBound inputWeight
        formulaStart := zeroSize_le_successBound inputWeight
        formulaFinish := zeroSize_le_successBound inputWeight
        suffixStart := hbounds.suffixStart.trans hlift
        suffixFinish := hbounds.suffixFinish.trans hlift
        certificateTag := hbounds.tag.trans hlift
        endpointBound := hbounds.endpointBound.trans hlift }
  have fixedBranch
      (paTag : Nat) (branchSuffix : List Nat)
      (hfixed : CompactFixedPAAxiomTag paTag) :
      let branchInput := 1 :: paTag :: branchSuffix
      let inputWeight := compactAdditiveValueWeight branchInput
      exists tokenTable width tokenCount inputStart inputFinish,
      exists axiomStart axiomFinish formulaStart formulaFinish,
      exists suffixStart suffixFinish endpointBound,
        CompactAdditiveNatListDirectLayout
            tokenTable width tokenCount inputStart inputFinish branchInput /\
          CompactCertificateNodeSuccessBoundedGraph
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish 1 endpointBound /\
          CompactCertificateNodeSuccessPublicCoordinateBounds
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish 1 endpointBound
              (compactCertificateNodeSuccessPublicCoordinateSizeBound
                inputWeight) := by
    let branchInput := 1 :: paTag :: branchSuffix
    let inputWeight := compactAdditiveValueWeight branchInput
    rcases
        exists_compactCertificateNodeFixedPAEndpointBoundedGraph_with_publicBounds
          paTag branchSuffix hfixed with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        axiomStart, axiomFinish, suffixStart, suffixFinish, endpointBound,
        hinput, hfixedGraph, hbounds⟩
    have hlift := fixedBound_le_successBound inputWeight
    refine
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        axiomStart, axiomFinish, 0, 0, suffixStart, suffixFinish,
        endpointBound, hinput, Or.inr (Or.inl hfixedGraph), ?_⟩
    exact
      { tokenTable := hbounds.tokenTable.trans hlift
        width_value := hbounds.width_value.trans hlift
        width := hbounds.width.trans hlift
        tokenCount_value := hbounds.tokenCount_value.trans hlift
        tokenCount := hbounds.tokenCount.trans hlift
        inputStart := hbounds.inputStart.trans hlift
        inputFinish := hbounds.inputFinish.trans hlift
        axiomStart := hbounds.axiomStart.trans hlift
        axiomFinish := hbounds.axiomFinish.trans hlift
        formulaStart := zeroSize_le_successBound inputWeight
        formulaFinish := zeroSize_le_successBound inputWeight
        suffixStart := hbounds.suffixStart.trans hlift
        suffixFinish := hbounds.suffixFinish.trans hlift
        certificateTag := hbounds.certificateTag.trans hlift
        endpointBound := hbounds.endpointBound.trans hlift }
  have symbolBranch
      (paTag arity symbolCode : Nat) (branchSuffix : List Nat)
      (hvalid : CompactSymbolPAAxiomTagValid paTag arity symbolCode) :
      let branchInput := 1 :: paTag :: arity :: symbolCode :: branchSuffix
      let inputWeight := compactAdditiveValueWeight branchInput
      exists tokenTable width tokenCount inputStart inputFinish,
      exists axiomStart axiomFinish formulaStart formulaFinish,
      exists suffixStart suffixFinish endpointBound,
        CompactAdditiveNatListDirectLayout
            tokenTable width tokenCount inputStart inputFinish branchInput /\
          CompactCertificateNodeSuccessBoundedGraph
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish 1 endpointBound /\
          CompactCertificateNodeSuccessPublicCoordinateBounds
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish 1 endpointBound
              (compactCertificateNodeSuccessPublicCoordinateSizeBound
                inputWeight) := by
    let branchInput := 1 :: paTag :: arity :: symbolCode :: branchSuffix
    let inputWeight := compactAdditiveValueWeight branchInput
    rcases
        exists_compactCertificateNodeSymbolPAEndpointBoundedGraph_with_publicBounds
          paTag arity symbolCode branchSuffix hvalid with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        axiomStart, axiomFinish, suffixStart, suffixFinish, endpointBound,
        hinput, hsymbolGraph, hbounds⟩
    have hlift := symbolBound_le_successBound inputWeight
    refine
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        axiomStart, axiomFinish, 0, 0, suffixStart, suffixFinish,
        endpointBound, hinput, Or.inr (Or.inr (Or.inl hsymbolGraph)), ?_⟩
    exact
      { tokenTable := hbounds.tokenTable.trans hlift
        width_value := hbounds.width_value.trans hlift
        width := hbounds.width.trans hlift
        tokenCount_value := hbounds.tokenCount_value.trans hlift
        tokenCount := hbounds.tokenCount.trans hlift
        inputStart := hbounds.inputStart.trans hlift
        inputFinish := hbounds.inputFinish.trans hlift
        axiomStart := hbounds.axiomStart.trans hlift
        axiomFinish := hbounds.axiomFinish.trans hlift
        formulaStart := zeroSize_le_successBound inputWeight
        formulaFinish := zeroSize_le_successBound inputWeight
        suffixStart := hbounds.suffixStart.trans hlift
        suffixFinish := hbounds.suffixFinish.trans hlift
        certificateTag := hbounds.certificateTag.trans hlift
        endpointBound := hbounds.endpointBound.trans hlift }
  have inductionBranch
      (formulaInput branchSuffix : List Nat)
      (hformula : compactFormulaTokenParser
        1 formulaInput = some branchSuffix) :
      let branchInput := 1 :: 22 :: formulaInput
      let inputWeight := compactAdditiveValueWeight branchInput
      exists tokenTable width tokenCount inputStart inputFinish,
      exists axiomStart axiomFinish formulaStart formulaFinish,
      exists suffixStart suffixFinish endpointBound,
        CompactAdditiveNatListDirectLayout
            tokenTable width tokenCount inputStart inputFinish branchInput /\
          CompactCertificateNodeSuccessBoundedGraph
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish 1 endpointBound /\
          CompactCertificateNodeSuccessPublicCoordinateBounds
            tokenTable width tokenCount inputStart inputFinish
              axiomStart axiomFinish formulaStart formulaFinish
              suffixStart suffixFinish 1 endpointBound
              (compactCertificateNodeSuccessPublicCoordinateSizeBound
                inputWeight) := by
    let branchInput := 1 :: 22 :: formulaInput
    let inputWeight := compactAdditiveValueWeight branchInput
    rcases
        exists_compactCertificateNodeInductionPAEndpointBoundedGraph_with_publicBounds
          formulaInput branchSuffix hformula with
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, endpointBound,
        hinput, hinductionGraph, hbounds⟩
    have hlift := inductionBound_le_successBound inputWeight
    refine
      ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
        axiomStart, axiomFinish, formulaStart, formulaFinish,
        suffixStart, suffixFinish, endpointBound,
        hinput, Or.inr (Or.inr (Or.inr hinductionGraph)), ?_⟩
    exact
      { tokenTable := hbounds.tokenTable.trans hlift
        width_value := hbounds.width_value.trans hlift
        width := hbounds.width.trans hlift
        tokenCount_value := hbounds.tokenCount_value.trans hlift
        tokenCount := hbounds.tokenCount.trans hlift
        inputStart := hbounds.inputStart.trans hlift
        inputFinish := hbounds.inputFinish.trans hlift
        axiomStart := hbounds.axiomStart.trans hlift
        axiomFinish := hbounds.axiomFinish.trans hlift
        formulaStart := hbounds.formulaStart.trans hlift
        formulaFinish := hbounds.formulaFinish.trans hlift
        suffixStart := hbounds.suffixStart.trans hlift
        suffixFinish := hbounds.suffixFinish.trans hlift
        certificateTag := hbounds.certificateTag.trans hlift
        endpointBound := hbounds.endpointBound.trans hlift }
  cases input with
  | nil =>
      simp [compactStructuralCertificateNodeParser] at hparser
  | cons tag tail =>
      by_cases h0 : tag = 0
      · subst tag
        have hparseEq :
            some (0, (([] : List Nat), tail)) =
              some (certificateTag, (axiomTokens, suffix)) := by
          simpa [compactStructuralCertificateNodeParser] using hparser
        have hnode := Option.some.inj hparseEq
        have htagEq : certificateTag = 0 :=
          (congrArg (fun node => node.1) hnode).symm
        have hpayload := congrArg (fun node => node.2) hnode
        have haxiomEq : axiomTokens = [] :=
          (congrArg (fun payload => payload.1) hpayload).symm
        have hsuffixEq : suffix = tail :=
          (congrArg (fun payload => payload.2) hpayload).symm
        subst certificateTag
        subst axiomTokens
        subst suffix
        simpa using simpleBranch 0 tail (Or.inl rfl)
      by_cases h1 : tag = 1
      · subst tag
        cases hpa : compactPAAxiomCertificateTokenParser tail with
        | none =>
            simp [compactStructuralCertificateNodeParser, h0, hpa] at hparser
        | some after =>
            have hparseEq :
                some (1, (FoundationCompactNumericSyntaxValueParser.consumedTokenPrefix
                  tail after, after)) =
                  some (certificateTag, (axiomTokens, suffix)) := by
              simpa [compactStructuralCertificateNodeParser, h0, hpa]
                using hparser
            have hnode := Option.some.inj hparseEq
            have htagEq : certificateTag = 1 :=
              (congrArg (fun node => node.1) hnode).symm
            have hpayload := congrArg (fun node => node.2) hnode
            have haxiomEq :
                axiomTokens =
                  FoundationCompactNumericSyntaxValueParser.consumedTokenPrefix
                    tail after :=
              (congrArg (fun payload => payload.1) hpayload).symm
            have hsuffixEq : suffix = after :=
              (congrArg (fun payload => payload.2) hpayload).symm
            subst certificateTag
            subst axiomTokens
            subst suffix
            rcases (compactPAAxiomCertificateTokenParser_success_iff
                tail after).mp hpa with
              ⟨certificate, htail⟩
            rw [htail]
            cases certificate with
            | eqRefl =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 0 after (by simp [CompactFixedPAAxiomTag])
            | eqSymm =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 1 after (by simp [CompactFixedPAAxiomTag])
            | eqTrans =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 2 after (by simp [CompactFixedPAAxiomTag])
            | eqFuncExt functionSymbol =>
                simpa [compactPAAxiomCertificateTokens] using
                  symbolBranch 3 _ (Encodable.encode functionSymbol) after
                    (Or.inl
                      ⟨rfl, arithmeticFuncCodeValid_encode functionSymbol⟩)
            | eqRelExt relationSymbol =>
                simpa [compactPAAxiomCertificateTokens] using
                  symbolBranch 4 _ (Encodable.encode relationSymbol) after
                    (Or.inr
                      ⟨rfl, arithmeticRelCodeValid_encode relationSymbol⟩)
            | addZero =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 5 after (by simp [CompactFixedPAAxiomTag])
            | addAssoc =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 6 after (by simp [CompactFixedPAAxiomTag])
            | addComm =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 7 after (by simp [CompactFixedPAAxiomTag])
            | addEqOfLt =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 8 after (by simp [CompactFixedPAAxiomTag])
            | zeroLe =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 9 after (by simp [CompactFixedPAAxiomTag])
            | zeroLtOne =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 10 after (by simp [CompactFixedPAAxiomTag])
            | oneLeOfZeroLt =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 11 after (by simp [CompactFixedPAAxiomTag])
            | addLtAdd =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 12 after (by simp [CompactFixedPAAxiomTag])
            | mulZero =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 13 after (by simp [CompactFixedPAAxiomTag])
            | mulOne =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 14 after (by simp [CompactFixedPAAxiomTag])
            | mulAssoc =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 15 after (by simp [CompactFixedPAAxiomTag])
            | mulComm =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 16 after (by simp [CompactFixedPAAxiomTag])
            | mulLtMul =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 17 after (by simp [CompactFixedPAAxiomTag])
            | distr =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 18 after (by simp [CompactFixedPAAxiomTag])
            | ltIrrefl =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 19 after (by simp [CompactFixedPAAxiomTag])
            | ltTrans =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 20 after (by simp [CompactFixedPAAxiomTag])
            | ltTri =>
                simpa [compactPAAxiomCertificateTokens] using
                  fixedBranch 21 after (by simp [CompactFixedPAAxiomTag])
            | induction body =>
                simpa [compactPAAxiomCertificateTokens] using
                  inductionBranch
                    (compactArithmeticFormulaTokens body ++ after) after
                    (compactFormulaTokenParser_canonical_append body after)
      by_cases h2 : tag = 2
      · subst tag
        have hparseEq :
            some (2, (([] : List Nat), tail)) =
              some (certificateTag, (axiomTokens, suffix)) := by
          simpa [compactStructuralCertificateNodeParser, h0, h1] using hparser
        have hnode := Option.some.inj hparseEq
        have htagEq : certificateTag = 2 :=
          (congrArg (fun node => node.1) hnode).symm
        have hpayload := congrArg (fun node => node.2) hnode
        have haxiomEq : axiomTokens = [] :=
          (congrArg (fun payload => payload.1) hpayload).symm
        have hsuffixEq : suffix = tail :=
          (congrArg (fun payload => payload.2) hpayload).symm
        subst certificateTag
        subst axiomTokens
        subst suffix
        simpa using simpleBranch 2 tail (Or.inr (Or.inl rfl))
      by_cases h3 : tag = 3
      · subst tag
        have hparseEq :
            some (3, (([] : List Nat), tail)) =
              some (certificateTag, (axiomTokens, suffix)) := by
          simpa [compactStructuralCertificateNodeParser, h0, h1, h2]
            using hparser
        have hnode := Option.some.inj hparseEq
        have htagEq : certificateTag = 3 :=
          (congrArg (fun node => node.1) hnode).symm
        have hpayload := congrArg (fun node => node.2) hnode
        have haxiomEq : axiomTokens = [] :=
          (congrArg (fun payload => payload.1) hpayload).symm
        have hsuffixEq : suffix = tail :=
          (congrArg (fun payload => payload.2) hpayload).symm
        subst certificateTag
        subst axiomTokens
        subst suffix
        simpa using simpleBranch 3 tail (Or.inr (Or.inr rfl))
      simp [compactStructuralCertificateNodeParser, h0, h1, h2, h3] at hparser

#print axioms
  exists_compactCertificateNodeSuccessBoundedGraph_of_parser_success_with_publicBounds
#print axioms compactCertificateNodeSuccessPublicCoordinateSizeBound_mono

end FoundationCompactNumericListedDirectCertificateNodeSuccessPublicBounds
