import integration.FoundationCompactNumericListedDirectNodeTransitionCases
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompiler

/-!
# Explicit checked certificate for node-transition tag matching

The ten legal proof/certificate tag pairs are selected directly from the
semantic tag-match relation.  No formula-truth compiler is used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNodeTransitionTagMatchExplicitHybridCertificate

open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem rewriting_embeddedClosedTerm
    {sourceVariables targetVariables : Type*}
    {sourceArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity targetVariables 0)
    (term : ArithmeticSemiterm Empty 0) :
    rewriting
        ((Rew.emb : Rew ℒₒᵣ Empty sourceArity
            sourceVariables sourceArity)
          ((Rew.subst
            (![] : Fin 0 -> ArithmeticSemiterm Empty sourceArity)) term)) =
      (Rew.emb : Rew ℒₒᵣ Empty 0 targetVariables 0) term := by
  have hcomposition :
      rewriting.comp
          ((Rew.emb : Rew ℒₒᵣ Empty sourceArity
              sourceVariables sourceArity).comp
            (Rew.subst
              (![] : Fin 0 -> ArithmeticSemiterm Empty sourceArity))) =
        (Rew.emb : Rew ℒₒᵣ Empty 0 targetVariables 0) := by
    apply Rew.ext
    · intro coordinate
      exact Fin.elim0 coordinate
    · intro coordinate
      exact Empty.elim coordinate
  have happ := congrArg (fun candidate => candidate term) hcomposition
  simpa only [Rew.comp_app] using happ

private def fixedNumeralTerm (value : Nat) : ValuationTerm :=
  (Semiterm.Operator.numeral ℒₒᵣ value : Semiterm.Const ℒₒᵣ)

@[simp] private theorem termValue_fixedNumeralTerm (value : Nat) :
    termValue zeroValuation (fixedNumeralTerm value) = value := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] zeroValuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  rw [LO.FirstOrder.Structure.numeral_eq_numeral
    (L := ℒₒᵣ) (M := Nat) value]
  simp

private def tagEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(fixedNumeralTerm expected)”

private def tagPairFormula
    (proofTag certificateTag expectedProof expectedCertificate : Nat) :
    ValuationFormula :=
  tagEqFormula proofTag expectedProof ⋏
    tagEqFormula certificateTag expectedCertificate

def compactNumericNodeTransitionTagMatchClosedFormula
    (proofTag certificateTag : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericNodeTransitionTagMatchDef.val) ⇜
    ![shortBinaryNumeralTerm proofTag,
      shortBinaryNumeralTerm certificateTag]

private def compactNumericNodeTransitionTagMatchPartsFormula
    (proofTag certificateTag : Nat) : ValuationFormula :=
  tagPairFormula proofTag certificateTag 0 0 ⋎
    (tagPairFormula proofTag certificateTag 1 1 ⋎
      (tagPairFormula proofTag certificateTag 2 0 ⋎
        (tagPairFormula proofTag certificateTag 3 3 ⋎
          (tagPairFormula proofTag certificateTag 4 2 ⋎
            (tagPairFormula proofTag certificateTag 5 2 ⋎
              (tagPairFormula proofTag certificateTag 6 2 ⋎
                (tagPairFormula proofTag certificateTag 7 2 ⋎
                  (tagPairFormula proofTag certificateTag 8 2 ⋎
                    tagPairFormula proofTag certificateTag 9 3))))))))

theorem compactNumericNodeTransitionTagMatchClosedFormula_alignment
    (proofTag certificateTag : Nat) :
    compactNumericNodeTransitionTagMatchClosedFormula
        proofTag certificateTag =
      compactNumericNodeTransitionTagMatchPartsFormula
        proofTag certificateTag := by
  unfold compactNumericNodeTransitionTagMatchClosedFormula
  unfold compactNumericNodeTransitionTagMatchPartsFormula
  unfold tagPairFormula tagEqFormula fixedNumeralTerm
  unfold compactNumericNodeTransitionTagMatchDef
  simp [shortBinaryNumeralTerm,
    Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.Zero.term_eq]
  repeat' apply And.intro
  all_goals apply rewriting_embeddedClosedTerm

private noncomputable def tagEqCertificate
    (value expected : Nat) (heq : value = expected) :
    HybridCertificate (tagEqFormula value expected) := by
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
  change termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (fixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using heq

private noncomputable def tagPairCertificate
    (proofTag certificateTag expectedProof expectedCertificate : Nat)
    (hproof : proofTag = expectedProof)
    (hcertificate : certificateTag = expectedCertificate) :
    HybridCertificate
      (tagPairFormula proofTag certificateTag
        expectedProof expectedCertificate) :=
  .conjunction
    (tagEqCertificate proofTag expectedProof hproof)
    (tagEqCertificate certificateTag expectedCertificate hcertificate)

private noncomputable def tagNeCertificate
    (value expected : Nat) (hne : value ≠ expected) :
    HybridCertificate (∼tagEqFormula value expected) := by
  unfold tagEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
  change ¬termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (fixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using hne

private noncomputable def tagPairFalseCertificate
    (proofTag certificateTag expectedProof expectedCertificate : Nat)
    (hfalse : ¬(proofTag = expectedProof ∧
      certificateTag = expectedCertificate)) :
    HybridCertificate
      (∼tagPairFormula proofTag certificateTag
        expectedProof expectedCertificate) := by
  unfold tagPairFormula
  by_cases hproof : proofTag = expectedProof
  · have hcertificate : certificateTag ≠ expectedCertificate := by
      intro hcertificate
      exact hfalse ⟨hproof, hcertificate⟩
    exact .disjunctionRight
      (tagNeCertificate certificateTag expectedCertificate hcertificate)
  · exact .disjunctionLeft
      (tagNeCertificate proofTag expectedProof hproof)

/-- The exact closed negation of the ten legal proof/certificate tag pairs. -/
def compactNumericNodeTransitionTagMismatchClosedFormula
    (proofTag certificateTag : Nat) : ValuationFormula :=
  ∼compactNumericNodeTransitionTagMatchClosedFormula proofTag certificateTag

theorem compactNumericNodeTransitionTagMismatchClosedFormula_alignment
    (proofTag certificateTag : Nat) :
    compactNumericNodeTransitionTagMismatchClosedFormula
        proofTag certificateTag =
      ∼compactNumericNodeTransitionTagMatchPartsFormula
        proofTag certificateTag := by
  unfold compactNumericNodeTransitionTagMismatchClosedFormula
  rw [compactNumericNodeTransitionTagMatchClosedFormula_alignment]

noncomputable def
    compactNumericNodeTransitionTagMatchExplicitHybridCertificateOfGraph
    (proofTag certificateTag : Nat)
    (hmatch : CompactNumericNodeTransitionTagMatch
      proofTag certificateTag) :
    HybridCertificate
      (compactNumericNodeTransitionTagMatchClosedFormula
        proofTag certificateTag) := by
  rw [compactNumericNodeTransitionTagMatchClosedFormula_alignment]
  if h0 : proofTag = 0 then
    have hc : certificateTag = 0 := by
      have hm := hmatch
      rw [h0] at hm
      simpa [CompactNumericNodeTransitionTagMatch] using hm
    exact .disjunctionLeft
      (tagPairCertificate proofTag certificateTag 0 0 h0 hc)
  else if h1 : proofTag = 1 then
    have hc : certificateTag = 1 := by
      have hm := hmatch
      rw [h1] at hm
      simpa [CompactNumericNodeTransitionTagMatch] using hm
    exact .disjunctionRight (.disjunctionLeft
      (tagPairCertificate proofTag certificateTag 1 1 h1 hc))
  else if h2 : proofTag = 2 then
    have hc : certificateTag = 0 := by
      have hm := hmatch
      rw [h2] at hm
      simpa [CompactNumericNodeTransitionTagMatch] using hm
    exact .disjunctionRight (.disjunctionRight (.disjunctionLeft
      (tagPairCertificate proofTag certificateTag 2 0 h2 hc)))
  else if h3 : proofTag = 3 then
    have hc : certificateTag = 3 := by
      have hm := hmatch
      rw [h3] at hm
      simpa [CompactNumericNodeTransitionTagMatch] using hm
    exact .disjunctionRight (.disjunctionRight (.disjunctionRight
      (.disjunctionLeft
        (tagPairCertificate proofTag certificateTag 3 3 h3 hc))))
  else if h4 : proofTag = 4 then
    have hc : certificateTag = 2 := by
      have hm := hmatch
      rw [h4] at hm
      simpa [CompactNumericNodeTransitionTagMatch] using hm
    exact .disjunctionRight (.disjunctionRight (.disjunctionRight
      (.disjunctionRight (.disjunctionLeft
        (tagPairCertificate proofTag certificateTag 4 2 h4 hc)))))
  else if h5 : proofTag = 5 then
    have hc : certificateTag = 2 := by
      have hm := hmatch
      rw [h5] at hm
      simpa [CompactNumericNodeTransitionTagMatch] using hm
    exact .disjunctionRight (.disjunctionRight (.disjunctionRight
      (.disjunctionRight (.disjunctionRight (.disjunctionLeft
        (tagPairCertificate proofTag certificateTag 5 2 h5 hc))))))
  else if h6 : proofTag = 6 then
    have hc : certificateTag = 2 := by
      have hm := hmatch
      rw [h6] at hm
      simpa [CompactNumericNodeTransitionTagMatch] using hm
    exact .disjunctionRight (.disjunctionRight (.disjunctionRight
      (.disjunctionRight (.disjunctionRight (.disjunctionRight
        (.disjunctionLeft
          (tagPairCertificate proofTag certificateTag 6 2 h6 hc)))))))
  else if h7 : proofTag = 7 then
    have hc : certificateTag = 2 := by
      have hm := hmatch
      rw [h7] at hm
      simpa [CompactNumericNodeTransitionTagMatch] using hm
    exact .disjunctionRight (.disjunctionRight (.disjunctionRight
      (.disjunctionRight (.disjunctionRight (.disjunctionRight
        (.disjunctionRight (.disjunctionLeft
          (tagPairCertificate proofTag certificateTag 7 2 h7 hc))))))))
  else if h8 : proofTag = 8 then
    have hc : certificateTag = 2 := by
      have hm := hmatch
      rw [h8] at hm
      simpa [CompactNumericNodeTransitionTagMatch] using hm
    exact .disjunctionRight (.disjunctionRight (.disjunctionRight
      (.disjunctionRight (.disjunctionRight (.disjunctionRight
        (.disjunctionRight (.disjunctionRight (.disjunctionLeft
          (tagPairCertificate proofTag certificateTag 8 2 h8 hc)))))))))
  else
    have h9 : proofTag = 9 := by
      by_contra hne
      have hm := hmatch
      simp [CompactNumericNodeTransitionTagMatch,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, hne] at hm
    have hc : certificateTag = 3 := by
      have hm := hmatch
      rw [h9] at hm
      simpa [CompactNumericNodeTransitionTagMatch] using hm
    exact .disjunctionRight (.disjunctionRight (.disjunctionRight
      (.disjunctionRight (.disjunctionRight (.disjunctionRight
        (.disjunctionRight (.disjunctionRight (.disjunctionRight
          (tagPairCertificate proofTag certificateTag 9 3 h9 hc)))))))))

/-- Explicitly certify that none of the ten legal tag pairs is present. -/
noncomputable def
    compactNumericNodeTransitionTagMismatchExplicitHybridCertificateOfGraph
    (proofTag certificateTag : Nat)
    (hmismatch : ¬CompactNumericNodeTransitionTagMatch
      proofTag certificateTag) :
    HybridCertificate
      (compactNumericNodeTransitionTagMismatchClosedFormula
        proofTag certificateTag) := by
  rw [compactNumericNodeTransitionTagMismatchClosedFormula_alignment]
  have pairFalse
      (expectedProof expectedCertificate : Nat)
      (hlegal : CompactNumericNodeTransitionTagMatch
        expectedProof expectedCertificate) :
      ¬(proofTag = expectedProof ∧
        certificateTag = expectedCertificate) := by
    intro hpair
    rcases hpair with ⟨rfl, rfl⟩
    exact hmismatch hlegal
  let pair0 := tagPairFalseCertificate proofTag certificateTag 0 0
    (pairFalse 0 0 (by simp [CompactNumericNodeTransitionTagMatch]))
  let pair1 := tagPairFalseCertificate proofTag certificateTag 1 1
    (pairFalse 1 1 (by simp [CompactNumericNodeTransitionTagMatch]))
  let pair2 := tagPairFalseCertificate proofTag certificateTag 2 0
    (pairFalse 2 0 (by simp [CompactNumericNodeTransitionTagMatch]))
  let pair3 := tagPairFalseCertificate proofTag certificateTag 3 3
    (pairFalse 3 3 (by simp [CompactNumericNodeTransitionTagMatch]))
  let pair4 := tagPairFalseCertificate proofTag certificateTag 4 2
    (pairFalse 4 2 (by simp [CompactNumericNodeTransitionTagMatch]))
  let pair5 := tagPairFalseCertificate proofTag certificateTag 5 2
    (pairFalse 5 2 (by simp [CompactNumericNodeTransitionTagMatch]))
  let pair6 := tagPairFalseCertificate proofTag certificateTag 6 2
    (pairFalse 6 2 (by simp [CompactNumericNodeTransitionTagMatch]))
  let pair7 := tagPairFalseCertificate proofTag certificateTag 7 2
    (pairFalse 7 2 (by simp [CompactNumericNodeTransitionTagMatch]))
  let pair8 := tagPairFalseCertificate proofTag certificateTag 8 2
    (pairFalse 8 2 (by simp [CompactNumericNodeTransitionTagMatch]))
  let pair9 := tagPairFalseCertificate proofTag certificateTag 9 3
    (pairFalse 9 3 (by simp [CompactNumericNodeTransitionTagMatch]))
  exact .conjunction pair0
    (.conjunction pair1
      (.conjunction pair2
        (.conjunction pair3
          (.conjunction pair4
            (.conjunction pair5
              (.conjunction pair6
                (.conjunction pair7
                  (.conjunction pair8 pair9))))))))

#print axioms compactNumericNodeTransitionTagMatchClosedFormula_alignment
#print axioms
  compactNumericNodeTransitionTagMatchExplicitHybridCertificateOfGraph
#print axioms compactNumericNodeTransitionTagMismatchClosedFormula_alignment
#print axioms
  compactNumericNodeTransitionTagMismatchExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectNodeTransitionTagMatchExplicitHybridCertificate
