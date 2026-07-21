import integration.FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for immediate PA-certificate failure

Both genuine failure branches are certified against the exact nineteen-
coordinate endpoint formula.  In particular, the outer structural tag remains
the unary numeral term occurring in the original formula; it is not replaced
by the syntactically different short binary numeral for the same value.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpointExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

private abbrev PAImmediateFailureHybridCertificate
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

private def paImmediateFailureOuterTerms
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates) :
    Fin 19 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm coordinates.inputBoundary,
    shortBinaryNumeralTerm coordinates.inputCount,
    shortBinaryNumeralTerm coordinates.inputBoundarySize,
    shortBinaryNumeralTerm coordinates.tailStart,
    shortBinaryNumeralTerm coordinates.tailFinish,
    shortBinaryNumeralTerm coordinates.tailBoundary,
    shortBinaryNumeralTerm coordinates.tailCount,
    shortBinaryNumeralTerm coordinates.tailBoundarySize,
    shortBinaryNumeralTerm coordinates.bodyStart,
    shortBinaryNumeralTerm coordinates.bodyFinish,
    shortBinaryNumeralTerm coordinates.bodyBoundary,
    shortBinaryNumeralTerm coordinates.bodyCount,
    shortBinaryNumeralTerm coordinates.bodyBoundarySize,
    shortBinaryNumeralTerm coordinates.paTag]

def compactCertificateNodePAImmediateFailureEndpointClosedFormula
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodePAImmediateFailureEndpointGraphDef.val) ⇜
    paImmediateFailureOuterTerms tokenTable width tokenCount inputStart
      inputFinish coordinates

private def fixedNumeralTerm (value : Nat) : ValuationTerm :=
  (Semiterm.Operator.numeral ℒₒᵣ value : Semiterm.Const ℒₒᵣ)

private def fixedEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(fixedNumeralTerm expected)”

private def fixedLtFormula (threshold value : Nat) : ValuationFormula :=
  “!!(fixedNumeralTerm threshold) < !!(shortBinaryNumeralTerm value)”

private def compactCertificateNodePAImmediateFailureEndpointExplicitFormula
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      inputStart coordinates.inputCount inputFinish coordinates.inputBoundary
      coordinates.inputBoundarySize ⋏
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
        coordinates.tailStart coordinates.tailCount coordinates.tailFinish
        coordinates.tailBoundary coordinates.tailBoundarySize ⋏
      (compactAdditiveNatListConsRowsAtValuationHeadFormula tokenTable width
          tokenCount coordinates.tailBoundary coordinates.tailCount
          coordinates.inputBoundary coordinates.inputCount
          (fixedNumeralTerm 1) ⋏
        (fixedEqFormula coordinates.tailCount 0 ⋎
          (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
              tokenCount coordinates.bodyStart coordinates.bodyCount
              coordinates.bodyFinish coordinates.bodyBoundary
              coordinates.bodyBoundarySize ⋏
            (fixedLtFormula 22 coordinates.paTag ⋏
              compactAdditiveNatListConsRowsClosedFormula tokenTable width
                tokenCount coordinates.bodyBoundary coordinates.bodyCount
                coordinates.tailBoundary coordinates.tailCount
                coordinates.paTag)))))

theorem compactCertificateNodePAImmediateFailureEndpointClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates) :
    compactCertificateNodePAImmediateFailureEndpointClosedFormula tokenTable
        width tokenCount inputStart inputFinish coordinates =
      compactCertificateNodePAImmediateFailureEndpointExplicitFormula
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  unfold compactCertificateNodePAImmediateFailureEndpointClosedFormula
    compactCertificateNodePAImmediateFailureEndpointExplicitFormula
    fixedEqFormula fixedLtFormula fixedNumeralTerm
    paImmediateFailureOuterTerms
    compactCertificateNodePAImmediateFailureEndpointGraphDef
    compactAdditiveNatListWitnessRowsClosedFormula
  rw [compactAdditiveNatListConsRowsAtValuationHeadFormula_eq_explicitSubstitution]
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

@[simp] private theorem termValue_fixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  rw [LO.FirstOrder.Structure.numeral_eq_numeral
    (L := ℒₒᵣ) (M := Nat) value]
  simp

private noncomputable def fixedEqCertificate
    (value expected : Nat) (heq : value = expected) :
    PAImmediateFailureHybridCertificate (fixedEqFormula value expected) := by
  unfold fixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
  change termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (fixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using heq

private noncomputable def fixedLtCertificate
    (threshold value : Nat) (hlt : threshold < value) :
    PAImmediateFailureHybridCertificate (fixedLtFormula threshold value) := by
  unfold fixedLtFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![fixedNumeralTerm threshold, shortBinaryNumeralTerm value]
  change termValue zeroValuation (fixedNumeralTerm threshold) <
    termValue zeroValuation (shortBinaryNumeralTerm value)
  simpa [termValue_shortBinaryNumeralTerm] using hlt

/-- Complete checked certificate for either immediate PA failure cause. -/
noncomputable def
    compactCertificateNodePAImmediateFailureEndpointExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates)
    (hgraph : CompactCertificateNodePAImmediateFailureEndpointGraph tokenTable
      width tokenCount inputStart inputFinish coordinates) :
    PAImmediateFailureHybridCertificate
      (compactCertificateNodePAImmediateFailureEndpointClosedFormula tokenTable
        width tokenCount inputStart inputFinish coordinates) := by
  rw [compactCertificateNodePAImmediateFailureEndpointClosedFormula_alignment]
  unfold compactCertificateNodePAImmediateFailureEndpointExplicitFormula
  let inputCertificate :=
    compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart coordinates.inputCount
      inputFinish coordinates.inputBoundary coordinates.inputBoundarySize
      hgraph.1
  let tailCertificate :=
    compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates.tailStart coordinates.tailCount
      coordinates.tailFinish coordinates.tailBoundary
      coordinates.tailBoundarySize hgraph.2.1
  let outerConsCertificate :=
    compactAdditiveNatListConsRowsAtValuationHeadExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates.tailBoundary
      coordinates.tailCount coordinates.inputBoundary coordinates.inputCount 1
      (fixedNumeralTerm 1) (by simp) hgraph.2.2.1
  let branchCertificate : PAImmediateFailureHybridCertificate
      (fixedEqFormula coordinates.tailCount 0 ⋎
        (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
            tokenCount coordinates.bodyStart coordinates.bodyCount
            coordinates.bodyFinish coordinates.bodyBoundary
            coordinates.bodyBoundarySize ⋏
          (fixedLtFormula 22 coordinates.paTag ⋏
            compactAdditiveNatListConsRowsClosedFormula tokenTable width
              tokenCount coordinates.bodyBoundary coordinates.bodyCount
              coordinates.tailBoundary coordinates.tailCount
              coordinates.paTag))) := by
    by_cases hempty : coordinates.tailCount = 0
    · exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (fixedEqCertificate coordinates.tailCount 0 hempty)
    · have hlarge := hgraph.2.2.2.resolve_left hempty
      exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount coordinates.bodyStart
            coordinates.bodyCount coordinates.bodyFinish
            coordinates.bodyBoundary coordinates.bodyBoundarySize hlarge.1)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (fixedLtCertificate 22 coordinates.paTag hlarge.2.1)
            (compactAdditiveNatListConsRowsOfGraphExplicitHybridCertificate
              tokenTable width tokenCount coordinates.bodyBoundary
              coordinates.bodyCount coordinates.tailBoundary
              coordinates.tailCount coordinates.paTag hlarge.2.2)))
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    inputCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tailCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        outerConsCertificate branchCertificate))

#print axioms compactCertificateNodePAImmediateFailureEndpointClosedFormula_alignment
#print axioms compactCertificateNodePAImmediateFailureEndpointExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpointExplicitHybridCertificate
