import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchTermFreeVariables
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Free-variable support of the atomic row in a cons-tail branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBranchRowFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTermFreeVariables

theorem consRowsTailBranchAtomicRow_freeVariables_subset_singleton
    (tokenTable width tokenCount : Nat) :
    (((Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
        closedShift 4 (shortBinaryNumeralTerm width),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        (#3 : ArithmeticSemiterm Nat 4),
        (#2 : ArithmeticSemiterm Nat 4),
        (#1 : ArithmeticSemiterm Nat 4),
        (#0 : ArithmeticSemiterm Nat 4)])).freeVariables ⊆ {0} := by
  apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
  intro coordinate
  fin_cases coordinate
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 tokenTable
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 width
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 tokenCount
  · exact boundVariable_freeVariables_subset_singleton 3
  · exact boundVariable_freeVariables_subset_singleton 2
  · exact boundVariable_freeVariables_subset_singleton 1
  · exact boundVariable_freeVariables_subset_singleton 0

#print axioms consRowsTailBranchAtomicRow_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectNatListConsRowsTailBranchRowFreeVariables
