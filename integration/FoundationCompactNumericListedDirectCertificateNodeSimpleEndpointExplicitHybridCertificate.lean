import integration.FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for the simple certificate-node endpoint

The original fourteen-coordinate graph is assembled from two checked list-row
certificates, an explicit three-way tag branch, and the checked cons-row graph.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSimpleEndpointExplicitHybridCertificate

open FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

private abbrev SimpleEndpointHybridCertificate
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

private def simpleEndpointOuterTerms
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates) :
    Fin 14 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm inputStart,
    shortBinaryNumeralTerm inputFinish,
    shortBinaryNumeralTerm suffixStart,
    shortBinaryNumeralTerm suffixFinish,
    shortBinaryNumeralTerm tag,
    shortBinaryNumeralTerm coordinates.inputBoundary,
    shortBinaryNumeralTerm coordinates.inputCount,
    shortBinaryNumeralTerm coordinates.inputBoundarySize,
    shortBinaryNumeralTerm coordinates.suffixBoundary,
    shortBinaryNumeralTerm coordinates.suffixCount,
    shortBinaryNumeralTerm coordinates.suffixBoundarySize]

def compactCertificateNodeSimpleEndpointClosedFormula
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactCertificateNodeSimpleEndpointGraphDef.val) ⇜
    simpleEndpointOuterTerms tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag coordinates

private def simpleEndpointTagFormula (tag : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm tag) = 0” ⋎
    (“!!(shortBinaryNumeralTerm tag) = 2” ⋎
      “!!(shortBinaryNumeralTerm tag) = 3”)

private def compactCertificateNodeSimpleEndpointExplicitFormula
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates) :
    ValuationFormula :=
  compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      inputStart coordinates.inputCount inputFinish coordinates.inputBoundary
      coordinates.inputBoundarySize ⋏
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
        suffixStart coordinates.suffixCount suffixFinish
        coordinates.suffixBoundary coordinates.suffixBoundarySize ⋏
      (simpleEndpointTagFormula tag ⋏
        compactAdditiveNatListConsRowsClosedFormula tokenTable width tokenCount
          coordinates.suffixBoundary coordinates.suffixCount
          coordinates.inputBoundary coordinates.inputCount tag))

theorem compactCertificateNodeSimpleEndpointClosedFormula_alignment
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates) :
    compactCertificateNodeSimpleEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish suffixStart suffixFinish tag
        coordinates =
      compactCertificateNodeSimpleEndpointExplicitFormula tokenTable width
        tokenCount inputStart inputFinish suffixStart suffixFinish tag
        coordinates := by
  unfold compactCertificateNodeSimpleEndpointClosedFormula
    compactCertificateNodeSimpleEndpointExplicitFormula
    simpleEndpointTagFormula simpleEndpointOuterTerms
    compactCertificateNodeSimpleEndpointGraphDef
    compactAdditiveNatListWitnessRowsClosedFormula
  rw [compactAdditiveNatListConsRowsClosedFormula_eq_explicitSubstitution]
  simp [rewriting_emptyFormulaSubstitution,
    rewriting_embeddedFormulaSubstitution, Rew.subst_bvar]
  constructor
  · congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Rew.subst_bvar]
  constructor
  · congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Rew.subst_bvar]
  · congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Rew.subst_bvar]

private def unaryNumeralTerm (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

@[simp] private theorem termValue_unaryNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (unaryNumeralTerm value) = value := by
  unfold termValue unaryNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  simp

private noncomputable def tagEqualityCertificate
    (tag expected : Nat) (heq : tag = expected) :
    SimpleEndpointHybridCertificate
      “!!(shortBinaryNumeralTerm tag) = !!(unaryNumeralTerm expected)” := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm tag, unaryNumeralTerm expected] (by
        change termValue zeroValuation (shortBinaryNumeralTerm tag) =
          termValue zeroValuation (unaryNumeralTerm expected)
        simpa [termValue_shortBinaryNumeralTerm] using heq)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def simpleEndpointTagCertificate
    (tag : Nat) (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
    SimpleEndpointHybridCertificate (simpleEndpointTagFormula tag) := by
  unfold simpleEndpointTagFormula
  if hzero : tag = 0 then
    exact .disjunctionLeft (tagEqualityCertificate tag 0 hzero)
  else if htwo : tag = 2 then
    exact .disjunctionRight
      (.disjunctionLeft (tagEqualityCertificate tag 2 htwo))
  else
    have hthree : tag = 3 :=
      (htag.resolve_left hzero).resolve_left htwo
    exact .disjunctionRight
      (.disjunctionRight (tagEqualityCertificate tag 3 hthree))

/-- Complete checked certificate for one concrete simple certificate-node
endpoint graph. -/
noncomputable def
    compactCertificateNodeSimpleEndpointExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates)
    (hgraph : CompactCertificateNodeSimpleEndpointGraph tokenTable width
      tokenCount inputStart inputFinish suffixStart suffixFinish tag
      coordinates) :
    SimpleEndpointHybridCertificate
      (compactCertificateNodeSimpleEndpointClosedFormula tokenTable width
        tokenCount inputStart inputFinish suffixStart suffixFinish tag
        coordinates) := by
  rw [compactCertificateNodeSimpleEndpointClosedFormula_alignment]
  unfold compactCertificateNodeSimpleEndpointExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount inputStart coordinates.inputCount
      inputFinish coordinates.inputBoundary coordinates.inputBoundarySize
      hgraph.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount suffixStart coordinates.suffixCount
        suffixFinish coordinates.suffixBoundary coordinates.suffixBoundarySize
        hgraph.2.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (simpleEndpointTagCertificate tag hgraph.2.2.1)
        (compactAdditiveNatListConsRowsOfGraphExplicitHybridCertificate
          tokenTable width tokenCount coordinates.suffixBoundary
          coordinates.suffixCount coordinates.inputBoundary
          coordinates.inputCount tag hgraph.2.2.2)))

#print axioms compactCertificateNodeSimpleEndpointClosedFormula_alignment
#print axioms compactCertificateNodeSimpleEndpointExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCertificateNodeSimpleEndpointExplicitHybridCertificate
