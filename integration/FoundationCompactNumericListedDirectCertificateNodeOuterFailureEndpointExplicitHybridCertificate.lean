import integration.FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpoint
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for outer certificate-node failure

Both failure causes are retained: an empty input and a nonempty input whose
head tag is different from each of 0, 1, 2, and 3.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpointExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpoint
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

private abbrev OuterFailureHybridCertificate
    (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_emptyFormulaSubstitution
    {targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Empty sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity -> ArithmeticSemiterm Empty sourceArity) :
    rewriting ▹ (formula ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      rewriting.comp (Rew.subst terms) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ (formula ⇜ terms) =
        (rewriting.comp (Rew.subst terms)) ▹ formula := by
      rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private def outerFailureOuterTerms
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates) :
    Fin 14 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm tailStart,
    shortBinaryNumeralTerm tailFinish,
    shortBinaryNumeralTerm coordinates.inputBoundary,
    shortBinaryNumeralTerm coordinates.inputCount,
    shortBinaryNumeralTerm coordinates.inputBoundarySize,
    shortBinaryNumeralTerm coordinates.tailBoundary,
    shortBinaryNumeralTerm coordinates.tailCount,
    shortBinaryNumeralTerm coordinates.tailBoundarySize,
    shortBinaryNumeralTerm coordinates.tag]

def compactCertificateNodeOuterFailureEndpointClosedFormula
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeOuterFailureEndpointGraphDef.val) ⇜
    outerFailureOuterTerms tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish coordinates

private def fixedNumeralTerm (value : Nat) : ValuationTerm :=
  (Semiterm.Operator.numeral ℒₒᵣ value : Semiterm.Const ℒₒᵣ)

private def fixedEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(fixedNumeralTerm expected)”

private def fixedNeFormula (value expected : Nat) : ValuationFormula :=
  ∼fixedEqFormula value expected

private def compactCertificateNodeOuterFailureEndpointExplicitFormula
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      inputStart coordinates.inputCount inputFinish coordinates.inputBoundary
      coordinates.inputBoundarySize ⋏
    (fixedEqFormula coordinates.inputCount 0 ⋎
      (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
          tokenCount tailStart coordinates.tailCount tailFinish
          coordinates.tailBoundary coordinates.tailBoundarySize ⋏
        (fixedNeFormula coordinates.tag 0 ⋏
          (fixedNeFormula coordinates.tag 1 ⋏
            (fixedNeFormula coordinates.tag 2 ⋏
              (fixedNeFormula coordinates.tag 3 ⋏
                compactAdditiveNatListConsRowsClosedFormula tokenTable width
                  tokenCount coordinates.tailBoundary coordinates.tailCount
                  coordinates.inputBoundary coordinates.inputCount
                  coordinates.tag))))))

theorem compactCertificateNodeOuterFailureEndpointClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates) :
    compactCertificateNodeOuterFailureEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish tailStart tailFinish coordinates =
      compactCertificateNodeOuterFailureEndpointExplicitFormula tokenTable
        width tokenCount inputStart inputFinish tailStart tailFinish
        coordinates := by
  unfold compactCertificateNodeOuterFailureEndpointClosedFormula
    compactCertificateNodeOuterFailureEndpointExplicitFormula
    fixedNeFormula fixedEqFormula fixedNumeralTerm outerFailureOuterTerms
    compactCertificateNodeOuterFailureEndpointGraphDef
    compactAdditiveNatListWitnessRowsClosedFormula
  rw [compactAdditiveNatListConsRowsClosedFormula_eq_explicitSubstitution]
  simp [rewriting_emptyFormulaSubstitution,
    rewriting_embeddedFormulaSubstitution, Rew.subst_bvar]
  constructor
  · congr 1
    funext coordinate
    fin_cases coordinate <;> simp [Rew.subst_bvar]
  constructor
  · congr 1
    funext coordinate
    fin_cases coordinate <;> simp [Rew.subst_bvar]
  · congr 1
    funext coordinate
    fin_cases coordinate <;> simp [Rew.subst_bvar]

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

private noncomputable def fixedEqCertificate
    (value expected : Nat) (heq : value = expected) :
    OuterFailureHybridCertificate (fixedEqFormula value expected) := by
  unfold fixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
  change termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (fixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using heq

private noncomputable def fixedNeCertificate
    (value expected : Nat) (hne : value ≠ expected) :
    OuterFailureHybridCertificate (fixedNeFormula value expected) := by
  unfold fixedNeFormula fixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
  change ¬termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (fixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using hne

/-- Complete checked certificate for either outer failure cause. -/
noncomputable def
    compactCertificateNodeOuterFailureEndpointExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish : Nat)
    (coordinates : CompactCertificateNodeOuterFailureEndpointCoordinates)
    (hgraph : CompactCertificateNodeOuterFailureEndpointGraph tokenTable width
      tokenCount inputStart inputFinish tailStart tailFinish coordinates) :
    OuterFailureHybridCertificate
      (compactCertificateNodeOuterFailureEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish tailStart tailFinish coordinates) := by
  rw [compactCertificateNodeOuterFailureEndpointClosedFormula_alignment]
  unfold compactCertificateNodeOuterFailureEndpointExplicitFormula
  let inputCertificate :=
    compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart coordinates.inputCount
      inputFinish coordinates.inputBoundary coordinates.inputBoundarySize
      hgraph.1
  by_cases hempty : coordinates.inputCount = 0
  · exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      inputCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (fixedEqCertificate coordinates.inputCount 0 hempty))
  · have hinvalid := hgraph.2.resolve_left hempty
    let invalidCertificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount tailStart coordinates.tailCount
          tailFinish coordinates.tailBoundary coordinates.tailBoundarySize
          hinvalid.1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (fixedNeCertificate coordinates.tag 0 hinvalid.2.1)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (fixedNeCertificate coordinates.tag 1 hinvalid.2.2.1)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (fixedNeCertificate coordinates.tag 2 hinvalid.2.2.2.1)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (fixedNeCertificate coordinates.tag 3
                  hinvalid.2.2.2.2.1)
                (compactAdditiveNatListConsRowsOfGraphExplicitHybridCertificate
                  tokenTable width tokenCount coordinates.tailBoundary
                  coordinates.tailCount coordinates.inputBoundary
                  coordinates.inputCount coordinates.tag
                  hinvalid.2.2.2.2.2)))))
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      inputCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        invalidCertificate)

#print axioms compactCertificateNodeOuterFailureEndpointClosedFormula_alignment
#print axioms compactCertificateNodeOuterFailureEndpointExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpointExplicitHybridCertificate
