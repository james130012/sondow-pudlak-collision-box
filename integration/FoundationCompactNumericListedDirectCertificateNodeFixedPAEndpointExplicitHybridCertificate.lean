import integration.FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate

/-!
# Explicit hybrid certificate for a fixed PA-axiom certificate node

The certificate follows the exact twenty-five-coordinate source formula.  It
assembles four list-row certificates, the fixed-tag arithmetic literals, both
cons-row graphs, and the append-slices graph without semantic truth fallback.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpointExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

private abbrev FixedPAEndpointHybridCertificate
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

private def fixedPAEndpointOuterTerms
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates) :
    Fin 25 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm axiomStart,
    shortBinaryNumeralTerm axiomFinish,
    shortBinaryNumeralTerm suffixStart,
    shortBinaryNumeralTerm suffixFinish,
    shortBinaryNumeralTerm certificateTag,
    shortBinaryNumeralTerm coordinates.inputBoundary,
    shortBinaryNumeralTerm coordinates.inputCount,
    shortBinaryNumeralTerm coordinates.inputBoundarySize,
    shortBinaryNumeralTerm coordinates.tailStart,
    shortBinaryNumeralTerm coordinates.tailFinish,
    shortBinaryNumeralTerm coordinates.tailBoundary,
    shortBinaryNumeralTerm coordinates.tailCount,
    shortBinaryNumeralTerm coordinates.tailBoundarySize,
    shortBinaryNumeralTerm coordinates.axiomBoundary,
    shortBinaryNumeralTerm coordinates.axiomCount,
    shortBinaryNumeralTerm coordinates.axiomBoundarySize,
    shortBinaryNumeralTerm coordinates.suffixBoundary,
    shortBinaryNumeralTerm coordinates.suffixCount,
    shortBinaryNumeralTerm coordinates.suffixBoundarySize,
    shortBinaryNumeralTerm coordinates.paTag]

def compactCertificateNodeFixedPAEndpointClosedFormula
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeFixedPAEndpointGraphDef.val) ⇜
    fixedPAEndpointOuterTerms tokenTable width tokenCount inputStart
      inputFinish axiomStart axiomFinish suffixStart suffixFinish
      certificateTag coordinates

private def fixedNumeralTerm (value : Nat) : ValuationTerm :=
  (Semiterm.Operator.numeral ℒₒᵣ value : Semiterm.Const ℒₒᵣ)

private def fixedEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(fixedNumeralTerm expected)”

private def fixedLtFormula (value upper : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) < !!(fixedNumeralTerm upper)”

private def fixedNeFormula (value expected : Nat) : ValuationFormula :=
  ∼fixedEqFormula value expected

private def compactCertificateNodeFixedPAEndpointExplicitFormula
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates) :
    ValuationFormula :=
  let inputRows := compactAdditiveNatListWitnessRowsClosedFormula tokenTable
    width tokenCount inputStart coordinates.inputCount inputFinish
      coordinates.inputBoundary coordinates.inputBoundarySize
  let tailRows := compactAdditiveNatListWitnessRowsClosedFormula tokenTable
    width tokenCount coordinates.tailStart coordinates.tailCount
      coordinates.tailFinish coordinates.tailBoundary
      coordinates.tailBoundarySize
  let axiomRows := compactAdditiveNatListWitnessRowsClosedFormula tokenTable
    width tokenCount axiomStart coordinates.axiomCount axiomFinish
      coordinates.axiomBoundary coordinates.axiomBoundarySize
  let suffixRows := compactAdditiveNatListWitnessRowsClosedFormula tokenTable
    width tokenCount suffixStart coordinates.suffixCount suffixFinish
      coordinates.suffixBoundary coordinates.suffixBoundarySize
  let outerCons := compactAdditiveNatListConsRowsAtValuationHeadFormula
    tokenTable width tokenCount coordinates.tailBoundary coordinates.tailCount
      coordinates.inputBoundary coordinates.inputCount (fixedNumeralTerm 1)
  let innerCons := compactAdditiveNatListConsRowsClosedFormula tokenTable width
    tokenCount coordinates.suffixBoundary coordinates.suffixCount
      coordinates.tailBoundary coordinates.tailCount coordinates.paTag
  let appendRows := compactAdditiveNatListAppendSlicesClosedFormula tokenTable
    width tokenCount axiomStart axiomFinish coordinates.axiomCount suffixStart
      suffixFinish coordinates.suffixCount coordinates.tailStart
      coordinates.tailFinish coordinates.tailCount
  inputRows ⋏ tailRows ⋏ axiomRows ⋏ suffixRows ⋏
    fixedEqFormula certificateTag 1 ⋏
    fixedLtFormula coordinates.paTag 22 ⋏
    fixedNeFormula coordinates.paTag 3 ⋏
    fixedNeFormula coordinates.paTag 4 ⋏
    outerCons ⋏ innerCons ⋏ appendRows

theorem compactCertificateNodeFixedPAEndpointClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates) :
    compactCertificateNodeFixedPAEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
        suffixFinish certificateTag coordinates =
      compactCertificateNodeFixedPAEndpointExplicitFormula tokenTable width
        tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
        suffixFinish certificateTag coordinates := by
  unfold compactCertificateNodeFixedPAEndpointClosedFormula
    compactCertificateNodeFixedPAEndpointExplicitFormula
    fixedEqFormula fixedLtFormula fixedNeFormula fixedNumeralTerm
    fixedPAEndpointOuterTerms compactCertificateNodeFixedPAEndpointGraphDef
    compactAdditiveNatListWitnessRowsClosedFormula
    compactAdditiveNatListAppendSlicesClosedFormula
  rw [compactAdditiveNatListConsRowsAtValuationHeadFormula_eq_explicitSubstitution]
  rw [compactAdditiveNatListConsRowsClosedFormula_eq_explicitSubstitution]
  simp [rewriting_emptyFormulaSubstitution,
    rewriting_embeddedFormulaSubstitution, Rew.subst_bvar]
  repeat' apply And.intro
  all_goals
    congr 1 <;>
      try
        (funext coordinate
         fin_cases coordinate <;> simp [Rew.subst_bvar])

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
    FixedPAEndpointHybridCertificate (fixedEqFormula value expected) := by
  unfold fixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
  change termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (fixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using heq

private noncomputable def fixedLtCertificate
    (value upper : Nat) (hlt : value < upper) :
    FixedPAEndpointHybridCertificate (fixedLtFormula value upper) := by
  unfold fixedLtFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm value, fixedNumeralTerm upper]
  change termValue zeroValuation (shortBinaryNumeralTerm value) <
    termValue zeroValuation (fixedNumeralTerm upper)
  simpa [termValue_shortBinaryNumeralTerm] using hlt

private noncomputable def fixedNeCertificate
    (value expected : Nat) (hne : value ≠ expected) :
    FixedPAEndpointHybridCertificate (fixedNeFormula value expected) := by
  unfold fixedNeFormula fixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
  change ¬termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (fixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using hne

/-- Complete checked certificate for a concrete fixed PA endpoint graph. -/
noncomputable def
    compactCertificateNodeFixedPAEndpointExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates)
    (hgraph : CompactCertificateNodeFixedPAEndpointGraph tokenTable width
      tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
      suffixFinish certificateTag coordinates) :
    FixedPAEndpointHybridCertificate
      (compactCertificateNodeFixedPAEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish axiomStart axiomFinish suffixStart
        suffixFinish certificateTag coordinates) := by
  rw [compactCertificateNodeFixedPAEndpointClosedFormula_alignment]
  unfold compactCertificateNodeFixedPAEndpointExplicitFormula
  rcases hgraph with
    ⟨hinput, htail, haxiom, hsuffix, hcertificateTag,
      ⟨hpaLt, hpaNe3, hpaNe4⟩, houterCons, hinnerCons, happend⟩
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart coordinates.inputCount
      inputFinish coordinates.inputBoundary coordinates.inputBoundarySize
      hinput)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount coordinates.tailStart
        coordinates.tailCount coordinates.tailFinish
        coordinates.tailBoundary coordinates.tailBoundarySize htail)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount axiomStart coordinates.axiomCount
          axiomFinish coordinates.axiomBoundary coordinates.axiomBoundarySize
          haxiom)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
            tokenTable width tokenCount suffixStart coordinates.suffixCount
            suffixFinish coordinates.suffixBoundary
            coordinates.suffixBoundarySize hsuffix)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (fixedEqCertificate certificateTag 1 hcertificateTag)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (fixedLtCertificate coordinates.paTag 22 hpaLt)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (fixedNeCertificate coordinates.paTag 3 hpaNe3)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (fixedNeCertificate coordinates.paTag 4 hpaNe4)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveNatListConsRowsAtValuationHeadExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount coordinates.tailBoundary
                      coordinates.tailCount coordinates.inputBoundary
                      coordinates.inputCount 1 (fixedNumeralTerm 1)
                      (by simp) houterCons)
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (compactAdditiveNatListConsRowsOfGraphExplicitHybridCertificate
                        tokenTable width tokenCount coordinates.suffixBoundary
                        coordinates.suffixCount coordinates.tailBoundary
                        coordinates.tailCount coordinates.paTag hinnerCons)
                      (compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
                        tokenTable width tokenCount axiomStart axiomFinish
                        coordinates.axiomCount suffixStart suffixFinish
                        coordinates.suffixCount coordinates.tailStart
                        coordinates.tailFinish coordinates.tailCount
                        happend))))))))))

#print axioms compactCertificateNodeFixedPAEndpointClosedFormula_alignment
#print axioms compactCertificateNodeFixedPAEndpointExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpointExplicitHybridCertificate
