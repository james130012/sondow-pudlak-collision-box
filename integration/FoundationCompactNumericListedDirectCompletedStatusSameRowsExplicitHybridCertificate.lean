import integration.FoundationCompactNumericListedDirectCompletedStatusSameRows
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit certificate for equal completed binary-Nat statuses

Both completed prefixes, both output layouts, row equality, exact boundary
sizes, and the two public area bounds are compiled separately.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

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

noncomputable def boundaryAreaCertificate
    (tokenCount outputCount boundarySize : Nat)
    (hbound : boundarySize ≤ (outputCount + 1) * tokenCount) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm boundarySize) ≤
        (!!(shortBinaryNumeralTerm outputCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm outputCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  exact valuationLeCertificate
    (shortBinaryNumeralTerm boundarySize) rightTerm (by
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticMul,
        termValue_arithmeticOne] using hbound)

def compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat) : ValuationFormula :=
  compactBinaryNatCompletedStatusPrefixClosedFormula
      tokenTable width tokenCount sourceStatusStart sourceOutputStart ⋏
    (compactAdditiveStructuredListLayoutClosedFormula
        tokenTable width tokenCount sourceOutputStart outputCount
          sourceStatusFinish sourceOutputBoundary ⋏
      (compactBinaryNatCompletedStatusPrefixClosedFormula
          tokenTable width tokenCount targetStatusStart targetOutputStart ⋏
        (compactAdditiveStructuredListLayoutClosedFormula
            tokenTable width tokenCount targetOutputStart outputCount
              targetStatusFinish targetOutputBoundary ⋏
          (compactAdditiveNatListSameRowsClosedFormula
              tokenTable width tokenCount sourceOutputBoundary outputCount
                targetOutputBoundary outputCount ⋏
            (compactNatSizeClosedFormula
                sourceOutputBoundarySize sourceOutputBoundary ⋏
              (“!!(shortBinaryNumeralTerm sourceOutputBoundarySize) ≤
                  (!!(shortBinaryNumeralTerm outputCount) + 1) *
                    !!(shortBinaryNumeralTerm tokenCount)” ⋏
                (compactNatSizeClosedFormula
                    targetOutputBoundarySize targetOutputBoundary ⋏
                  “!!(shortBinaryNumeralTerm targetOutputBoundarySize) ≤
                    (!!(shortBinaryNumeralTerm outputCount) + 1) *
                      !!(shortBinaryNumeralTerm tokenCount)”)))))))

noncomputable def
    compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat)
    (hgraph : CompactBinaryNatCompletedStatusSameRowsWithSize
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount) :
    HybridCertificate
      (compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
        tokenTable width tokenCount
          sourceStatusStart sourceStatusFinish
          targetStatusStart targetStatusFinish
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) := by
  rcases hgraph with
    ⟨hbase, hsourceSize, hsourceArea, htargetSize, htargetArea⟩
  rcases hbase with
    ⟨hsourcePrefix, hsourceLayout, htargetPrefix,
      htargetLayout, hsame⟩
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceStatusStart sourceOutputStart
        hsourcePrefix)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
        tokenTable width tokenCount sourceOutputStart outputCount
          sourceStatusFinish sourceOutputBoundary hsourceLayout)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount targetStatusStart targetOutputStart
            htargetPrefix)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
            tokenTable width tokenCount targetOutputStart outputCount
              targetStatusFinish targetOutputBoundary htargetLayout)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
              tokenTable width tokenCount sourceOutputBoundary outputCount
                targetOutputBoundary outputCount hsame)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactNatSizeExplicitHybridCertificateOfEq
                sourceOutputBoundarySize sourceOutputBoundary hsourceSize)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (boundaryAreaCertificate tokenCount outputCount
                  sourceOutputBoundarySize hsourceArea)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (compactNatSizeExplicitHybridCertificateOfEq
                    targetOutputBoundarySize targetOutputBoundary htargetSize)
                  (boundaryAreaCertificate tokenCount outputCount
                    targetOutputBoundarySize htargetArea))))))))

noncomputable def
    compileCompactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridContext
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat)
    (hgraph : CompactBinaryNatCompletedStatusSameRowsWithSize
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
          tokenTable width tokenCount
            sourceStatusStart sourceStatusFinish
            targetStatusStart targetStatusFinish
            sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
            targetOutputStart targetOutputBoundary targetOutputBoundarySize
            outputCount).freeVariables zeroValuation)
      (compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
        tokenTable width tokenCount
          sourceStatusStart sourceStatusFinish
          targetStatusStart targetStatusFinish
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount) :=
  (compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph
    tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount hgraph).compile

noncomputable def
    compactBinaryNatCompletedStatusSameRowsWithSizeExplicitStructuralResource
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat)
    (hgraph : CompactBinaryNatCompletedStatusSameRowsWithSize
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount hgraph)

theorem
    compileCompactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount : Nat)
    (hgraph : CompactBinaryNatCompletedStatusSameRowsWithSize
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount) :
    (compileCompactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridContext
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount hgraph).payloadLength ≤
      compactBinaryNatCompletedStatusSameRowsWithSizeExplicitStructuralResource
        tokenTable width tokenCount
          sourceStatusStart sourceStatusFinish
          targetStatusStart targetStatusFinish
          sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
          targetOutputStart targetOutputBoundary targetOutputBoundarySize
          outputCount hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount hgraph)

#print axioms
  compactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridCertificateOfGraph
#print axioms
  compileCompactBinaryNatCompletedStatusSameRowsWithSizeExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
