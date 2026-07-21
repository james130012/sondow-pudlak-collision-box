import integration.FoundationCompactNumericListedDirectFormulaTransformStateFormula
import integration.FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for a formula-transform state core

The constructor consumes the original seventeen-coordinate graph.  Every
conjunct is discharged by a concrete structural or arithmetic certificate;
no truth-to-certificate conversion is used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

def compactFormulaTransformStateCoreClosedFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFormulaTransformStateCoreGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.parserFinish,
      shortBinaryNumeralTerm coordinates.parserTokensFinish,
      shortBinaryNumeralTerm coordinates.parserTasksFinish,
      shortBinaryNumeralTerm coordinates.parserTokensBoundary,
      shortBinaryNumeralTerm coordinates.parserTokensCount,
      shortBinaryNumeralTerm coordinates.parserTasksBoundary,
      shortBinaryNumeralTerm coordinates.parserTasksCount,
      shortBinaryNumeralTerm coordinates.outputBoundary,
      shortBinaryNumeralTerm coordinates.outputCount,
      shortBinaryNumeralTerm sizeWitness.parserTokensBoundarySize,
      shortBinaryNumeralTerm sizeWitness.parserTasksBoundarySize,
      shortBinaryNumeralTerm sizeWitness.outputBoundarySize]

def compactFormulaTransformStateCoreExplicitFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    ValuationFormula :=
  compactAdditiveProductSplitClosedFormula
      tokenCount coordinates.start coordinates.parserFinish
        coordinates.finish ⋏
    (compactUnifiedParserStateCoreClosedFormula
        tokenTable width tokenCount
        coordinates.start coordinates.parserFinish
        coordinates.parserTokensFinish coordinates.parserTasksFinish
        coordinates.parserTokensBoundary coordinates.parserTokensCount
        coordinates.parserTasksBoundary coordinates.parserTasksCount
        sizeWitness.parserTokensBoundarySize
        sizeWitness.parserTasksBoundarySize ⋏
      (compactAdditiveStructuredListLayoutClosedFormula
          tokenTable width tokenCount coordinates.parserFinish
          coordinates.outputCount coordinates.finish
          coordinates.outputBoundary ⋏
        (compactAdditiveUnitBoundaryRowsClosedFormula
            tokenCount coordinates.outputCount coordinates.outputBoundary ⋏
          (compactNatSizeClosedFormula
              sizeWitness.outputBoundarySize coordinates.outputBoundary ⋏
            “!!(shortBinaryNumeralTerm sizeWitness.outputBoundarySize) ≤
              (!!(shortBinaryNumeralTerm coordinates.outputCount) + 1) *
                !!(shortBinaryNumeralTerm tokenCount)”))))

theorem compactFormulaTransformStateCoreClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformStateCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness =
      compactFormulaTransformStateCoreExplicitFormula
        tokenTable width tokenCount coordinates sizeWitness := by
  unfold compactFormulaTransformStateCoreClosedFormula
  unfold compactFormulaTransformStateCoreExplicitFormula
  unfold compactFormulaTransformStateCoreGraphDef
  unfold compactAdditiveProductSplitClosedFormula
  unfold compactUnifiedParserStateCoreClosedFormula
  unfold compactAdditiveStructuredListLayoutClosedFormula
  unfold compactAdditiveUnitBoundaryRowsClosedFormula
  unfold compactNatSizeClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left * !!right’ =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def valuationLeCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hle : termValue zeroValuation leftTerm ≤
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm ≤ !!rightTerm” := by
  if heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue zeroValuation leftTerm <
        termValue zeroValuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

noncomputable def outputBoundaryAreaCertificate
    (tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hbound : sizeWitness.outputBoundarySize ≤
      (coordinates.outputCount + 1) * tokenCount) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm sizeWitness.outputBoundarySize) ≤
        (!!(shortBinaryNumeralTerm coordinates.outputCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm coordinates.outputCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  exact valuationLeCertificate
    (shortBinaryNumeralTerm sizeWitness.outputBoundarySize) rightTerm (by
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticMul,
        termValue_arithmeticOne] using hbound)

noncomputable def
    compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    HybridCertificate
      (compactFormulaTransformStateCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness) := by
  rcases hgraph with
    ⟨houter, hparser, houtputLayout, houtputRows,
      houtputSize, houtputArea⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveProductSplitExplicitHybridCertificateOfGraph
      tokenCount coordinates.start coordinates.parserFinish
        coordinates.finish houter)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph
        tokenTable width tokenCount coordinates.parser sizeWitness.parser
          hparser)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
          tokenTable width tokenCount coordinates.parserFinish
            coordinates.outputCount coordinates.finish
            coordinates.outputBoundary houtputLayout)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
            tokenCount coordinates.outputCount coordinates.outputBoundary
              houtputRows)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactNatSizeExplicitHybridCertificateOfEq
              sizeWitness.outputBoundarySize coordinates.outputBoundary
                houtputSize)
            (outputBoundaryAreaCertificate tokenCount coordinates sizeWitness
              houtputArea)))))
  exact .cast
    (compactFormulaTransformStateCoreClosedFormula_alignment
      tokenTable width tokenCount coordinates sizeWitness).symm parts

noncomputable def compileCompactFormulaTransformStateCoreExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformStateCoreClosedFormula
          tokenTable width tokenCount coordinates sizeWitness).freeVariables
        zeroValuation)
      (compactFormulaTransformStateCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness) :=
  (compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
    tokenTable width tokenCount coordinates sizeWitness hgraph).compile

noncomputable def compactFormulaTransformStateCoreExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates sizeWitness hgraph)

theorem
    compileCompactFormulaTransformStateCoreExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    (compileCompactFormulaTransformStateCoreExplicitHybridContext
      tokenTable width tokenCount coordinates sizeWitness hgraph).payloadLength ≤
      compactFormulaTransformStateCoreExplicitStructuralResource
        tokenTable width tokenCount coordinates sizeWitness hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates sizeWitness hgraph)

#print axioms compactFormulaTransformStateCoreClosedFormula_alignment
#print axioms compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformStateCoreExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
