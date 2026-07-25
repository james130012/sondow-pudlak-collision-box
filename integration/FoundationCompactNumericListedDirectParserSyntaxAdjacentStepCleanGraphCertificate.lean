import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate

/-!
# Clean graph certificate for one adjacent syntax-parser step

The original 33-coordinate adjacent-row formula is preserved.  Its final
component is the clean six-way syntax-step certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepCleanGraphCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate
    compactParserStateAtRowsZeroValuation formula

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def
    compactParserSyntaxAdjacentStepRowCleanHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph tokenTable width tokenCount
      stateBoundary stateCount index row) :
    HybridCertificate
      (compactParserSyntaxAdjacentStepRowClosedFormula tokenTable width
        tokenCount stateBoundary stateCount index row) := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  have hnextAtTerm : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount
      (termValue compactParserStateAtRowsZeroValuation nextIndexTerm)
      row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, compactParserStateAtRowsZeroValuation,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hnext
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount stateBoundary stateCount index row.currentCoordinates
      row.currentSize hcurrent)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactUnifiedParserStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
        tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
        row.nextCoordinates row.nextSize hnextAtTerm)
      (compactUnifiedParserSyntaxStepCleanHybridCertificateOfGraph tokenTable
        width tokenCount row.currentCoordinates row.nextCoordinates
        row.stepWitness hstep))
  exact .cast
    (compactParserSyntaxAdjacentStepRowClosedFormula_alignment tokenTable width
      tokenCount stateBoundary stateCount index row).symm
    parts

#print axioms
  compactParserSyntaxAdjacentStepRowCleanHybridCertificateOfGraph

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepCleanGraphCertificate
