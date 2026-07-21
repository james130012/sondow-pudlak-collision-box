import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate

/-!
# Explicit hybrid assembly for an induction PA certificate-node endpoint

The outer six structural components are certified directly.  The remaining
parser endpoint is retained as its original closed formula, so a future parser
certificate can be installed without changing this endpoint presentation.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpointExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointFormula
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

abbrev InductionPAEndpointHybridCertificate (formula : ValuationFormula) :=
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

private def inductionPAEndpointOuterTerms
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates) :
    Fin 33 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm axiomStart,
    shortBinaryNumeralTerm axiomFinish,
    shortBinaryNumeralTerm formulaStart,
    shortBinaryNumeralTerm formulaFinish,
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
    shortBinaryNumeralTerm coordinates.parser.inputBoundary,
    shortBinaryNumeralTerm coordinates.parser.inputCount,
    shortBinaryNumeralTerm coordinates.parser.inputBoundarySize,
    shortBinaryNumeralTerm coordinates.parser.expectedBoundary,
    shortBinaryNumeralTerm coordinates.parser.expectedCount,
    shortBinaryNumeralTerm coordinates.parser.expectedBoundarySize,
    shortBinaryNumeralTerm coordinates.parser.stateBoundary,
    shortBinaryNumeralTerm coordinates.parser.stateCount,
    shortBinaryNumeralTerm coordinates.parser.tableWidth,
    shortBinaryNumeralTerm coordinates.parser.valueBound]

def compactCertificateNodeInductionPAEndpointClosedFormula
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeInductionPAEndpointGraphDef.val) ⇜
    inductionPAEndpointOuterTerms tokenTable width tokenCount inputStart
      inputFinish axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag coordinates

private def fixedNumeralTerm (value : Nat) : ValuationTerm :=
  (Semiterm.Operator.numeral ℒₒᵣ value : Semiterm.Const ℒₒᵣ)

private def fixedEqFormula (value expected : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm value) = !!(fixedNumeralTerm expected)”

def compactParserSyntaxExactEndpointClosedFormula
    (tokenTable width tokenCount formulaStart formulaFinish
      suffixStart suffixFinish : Nat)
    (coordinates : CompactParserSyntaxExactEndpointCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactParserSyntaxExactEndpointGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm formulaStart,
      shortBinaryNumeralTerm formulaFinish,
      shortBinaryNumeralTerm suffixStart,
      shortBinaryNumeralTerm suffixFinish,
      fixedNumeralTerm 1,
      fixedNumeralTerm 1,
      fixedNumeralTerm 0,
      shortBinaryNumeralTerm coordinates.inputBoundary,
      shortBinaryNumeralTerm coordinates.inputCount,
      shortBinaryNumeralTerm coordinates.inputBoundarySize,
      shortBinaryNumeralTerm coordinates.expectedBoundary,
      shortBinaryNumeralTerm coordinates.expectedCount,
      shortBinaryNumeralTerm coordinates.expectedBoundarySize,
      shortBinaryNumeralTerm coordinates.stateBoundary,
      shortBinaryNumeralTerm coordinates.stateCount,
      shortBinaryNumeralTerm coordinates.tableWidth,
      shortBinaryNumeralTerm coordinates.valueBound]

private def compactCertificateNodeInductionPAEndpointExplicitFormula
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      inputStart coordinates.inputCount inputFinish coordinates.inputBoundary
      coordinates.inputBoundarySize ⋏
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
        coordinates.tailStart coordinates.tailCount coordinates.tailFinish
        coordinates.tailBoundary coordinates.tailBoundarySize ⋏
      (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
          axiomStart coordinates.axiomCount axiomFinish
          coordinates.axiomBoundary coordinates.axiomBoundarySize ⋏
        (fixedEqFormula certificateTag 1 ⋏
          (compactAdditiveNatListConsRowsAtValuationHeadFormula tokenTable width
              tokenCount coordinates.tailBoundary coordinates.tailCount
              coordinates.inputBoundary coordinates.inputCount
              (fixedNumeralTerm 1) ⋏
            (compactAdditiveNatListConsRowsAtValuationHeadFormula tokenTable width
                tokenCount coordinates.parser.inputBoundary
                coordinates.parser.inputCount coordinates.tailBoundary
                coordinates.tailCount 22 (fixedNumeralTerm 22) ⋏
              (compactParserSyntaxExactEndpointClosedFormula tokenTable width
                  tokenCount formulaStart formulaFinish suffixStart suffixFinish
                  coordinates.parser ⋏
                compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
                  tokenCount axiomStart axiomFinish coordinates.axiomCount
                  suffixStart suffixFinish coordinates.parser.expectedCount
                  coordinates.tailStart coordinates.tailFinish
                  coordinates.tailCount))))))

theorem compactCertificateNodeInductionPAEndpointClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates) :
    compactCertificateNodeInductionPAEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish axiomStart axiomFinish formulaStart
        formulaFinish suffixStart suffixFinish certificateTag coordinates =
      compactCertificateNodeInductionPAEndpointExplicitFormula tokenTable width
        tokenCount inputStart inputFinish axiomStart axiomFinish formulaStart
        formulaFinish suffixStart suffixFinish certificateTag coordinates := by
  unfold compactCertificateNodeInductionPAEndpointClosedFormula
    compactCertificateNodeInductionPAEndpointExplicitFormula
    compactParserSyntaxExactEndpointClosedFormula
    fixedEqFormula fixedNumeralTerm inductionPAEndpointOuterTerms
    compactCertificateNodeInductionPAEndpointGraphDef
    compactAdditiveNatListWitnessRowsClosedFormula
    compactAdditiveNatListAppendSlicesClosedFormula
  simp only [compactAdditiveNatListConsRowsAtValuationHeadFormula_eq_explicitSubstitution]
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
    InductionPAEndpointHybridCertificate (fixedEqFormula value expected) := by
  unfold fixedEqFormula
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]
  change termValue zeroValuation (shortBinaryNumeralTerm value) =
    termValue zeroValuation (fixedNumeralTerm expected)
  simpa [termValue_shortBinaryNumeralTerm] using heq

/-- Assemble the original endpoint formula once the exact parser terminal is
available.  No semantic truth compiler is used for the parser component. -/
noncomputable def
    compactCertificateNodeInductionPAEndpointExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag : Nat)
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates)
    (hgraph : CompactCertificateNodeInductionPAEndpointGraph tokenTable width
      tokenCount inputStart inputFinish axiomStart axiomFinish formulaStart
      formulaFinish suffixStart suffixFinish certificateTag coordinates)
    (parserCertificate : InductionPAEndpointHybridCertificate
      (compactParserSyntaxExactEndpointClosedFormula tokenTable width tokenCount
        formulaStart formulaFinish suffixStart suffixFinish coordinates.parser)) :
    InductionPAEndpointHybridCertificate
      (compactCertificateNodeInductionPAEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish axiomStart axiomFinish formulaStart
        formulaFinish suffixStart suffixFinish certificateTag coordinates) := by
  rw [compactCertificateNodeInductionPAEndpointClosedFormula_alignment]
  unfold compactCertificateNodeInductionPAEndpointExplicitFormula
  rcases hgraph with
    ⟨hinput, htail, haxiom, hcertificateTag, houterCons, hinnerCons,
      _hparser, happend⟩
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
      coordinates.inputBoundary coordinates.inputBoundarySize hinput)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount coordinates.tailStart coordinates.tailCount
        coordinates.tailFinish coordinates.tailBoundary
        coordinates.tailBoundarySize htail)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount axiomStart coordinates.axiomCount
          axiomFinish coordinates.axiomBoundary coordinates.axiomBoundarySize
          haxiom)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (fixedEqCertificate certificateTag 1 hcertificateTag)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListConsRowsAtValuationHeadExplicitHybridCertificateOfGraph
              tokenTable width tokenCount coordinates.tailBoundary
              coordinates.tailCount coordinates.inputBoundary
              coordinates.inputCount 1 (fixedNumeralTerm 1) (by simp)
              houterCons)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListConsRowsAtValuationHeadExplicitHybridCertificateOfGraph
                tokenTable width tokenCount coordinates.parser.inputBoundary
                coordinates.parser.inputCount coordinates.tailBoundary
                coordinates.tailCount 22 (fixedNumeralTerm 22) (by simp)
                hinnerCons)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                parserCertificate
                (compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount axiomStart axiomFinish
                  coordinates.axiomCount suffixStart suffixFinish
                  coordinates.parser.expectedCount coordinates.tailStart
                  coordinates.tailFinish coordinates.tailCount happend)))))))

#print axioms compactCertificateNodeInductionPAEndpointClosedFormula_alignment
#print axioms compactCertificateNodeInductionPAEndpointExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpointExplicitHybridCertificate
