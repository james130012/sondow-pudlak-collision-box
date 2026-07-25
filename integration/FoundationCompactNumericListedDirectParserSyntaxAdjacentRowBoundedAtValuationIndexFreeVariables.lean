import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

/-! # Free-variable bound for the open-index adjacent-row terminal -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFreeVariables

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

theorem
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_freeVariables_subset_singleton
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm)
    (hindexVariables : indexTerm.freeVariables ⊆ {0}) :
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount stateBoundary stateCount valueBound
        indexTerm).freeVariables ⊆ {0} := by
  unfold compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal
  unfold compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawRowFormula
  simp only [LO.FirstOrder.Semiformula.freeVariables_and]
  apply Finset.union_subset
  · apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate <;>
      simp [sourceSubstitutionLift_freeVariables_eq,
        shortBinaryNumeralTerm_freeVariables_eq_empty, hindexVariables]
  · apply Finset.union_subset
    · apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
      intro coordinate
      fin_cases coordinate <;>
        simp [sourceSubstitutionLift_freeVariables_eq,
          shortBinaryNumeralTerm_freeVariables_eq_empty]
    · apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
      intro coordinate
      fin_cases coordinate <;>
        simp [sourceSubstitutionLift_freeVariables_eq,
          shortBinaryNumeralTerm_freeVariables_eq_empty]

#print axioms
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFreeVariables
