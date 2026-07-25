import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexRowAlignment
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexCurrentStatusAlignment
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexNextStatusAlignment

/-! # Exact open-index alignment of the bounded adjacent-row formula -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFormulaAlignment

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitutionComponents
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexRowAlignment
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexCurrentStatusAlignment
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexNextStatusAlignment

theorem
    compactParserSyntaxAdjacentRowBoundedSourceRawTerminal_rewriting_openIndex
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) 27 ▹
      compactParserSyntaxAdjacentRowBoundedSourceRawTerminal =
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount stateBoundary stateCount valueBound indexTerm := by
  change
    (sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) 27 ▹
      compactParserSyntaxAdjacentRowSourceRowFormula) ⋏
    ((sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) 27 ▹
      compactParserSyntaxAdjacentRowSourceCurrentStatusFormula) ⋏
    (sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) 27 ▹
      compactParserSyntaxAdjacentRowSourceNextStatusFormula)) = _
  rw [compactParserSyntaxAdjacentRowSourceRowFormula_rewriting_openIndex,
    compactParserSyntaxAdjacentRowSourceCurrentStatusFormula_rewriting_openIndex,
    compactParserSyntaxAdjacentRowSourceNextStatusFormula_rewriting_openIndex]
  rfl

private theorem
    compactParserSyntaxAdjacentRowBoundedSourceRawBody_alignment_openIndex
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    Rew.subst
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) ▹
      compactParserSyntaxAdjacentRowBoundedSourceRawBody =
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 27
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal
        tokenTable width tokenCount stateBoundary stateCount valueBound
          indexTerm) := by
  unfold compactParserSyntaxAdjacentRowBoundedSourceRawBody
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [compactParserSyntaxAdjacentRowBoundedSourceRawTerminal_rewriting_openIndex]
  have hbound :
      Rew.subst
          (compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms
            tokenTable width tokenCount stateBoundary stateCount valueBound
              indexTerm)
          (#6 : ArithmeticSemiterm Nat 7) =
        shortBinaryNumeralTerm valueBound := by
    simp [Rew.subst_bvar,
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms]
  rw [hbound]
  rfl

theorem compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount valueBound indexTerm =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 27
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) := by
  unfold compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula
  rw [compactParserSyntaxAdjacentRowBoundedDef_emb_eq_sourceRawBody]
  exact
    compactParserSyntaxAdjacentRowBoundedSourceRawBody_alignment_openIndex
      tokenTable width tokenCount stateBoundary stateCount valueBound indexTerm

#print axioms
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula_alignment

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFormulaAlignment
