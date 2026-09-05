import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsPublicAlignment
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Public seven-leaf syntax for formula-transform endpoints -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax

open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate

theorem compactFormulaTransformStateAtRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    (compactFormulaTransformStateAtRowsClosedFormula tokenTable width tokenCount
      stateBoundary stateCount index coordinates sizeWitness).freeVariables =
        ∅ := by
  unfold compactFormulaTransformStateAtRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem
    compactFormulaTransformInitialFinalRowsPublicExplicitFormula_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    (compactFormulaTransformInitialFinalRowsPublicExplicitFormula
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity witness
      ).freeVariables = ∅ := by
  rw [← compactFormulaTransformInitialFinalRowsClosedFormula_alignment_public]
  unfold compactFormulaTransformInitialFinalRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax
