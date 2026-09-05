import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchTermFreeVariables
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Free-variable support of the two target entries in a cons-tail branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBranchTargetFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTermFreeVariables

theorem consRowsTailBranchTargetLeft_freeVariables_subset_singleton
    (targetBoundary tokenCount : Nat) :
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        closedShift 4 (‘&0 + 1’ : ValuationTerm),
        (#1 : ArithmeticSemiterm Nat 4)])).freeVariables ⊆ {0} := by
  apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
  intro coordinate
  fin_cases coordinate
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 targetBoundary
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 tokenCount
  · exact shiftedIndexSuccessor_freeVariables_subset_singleton 4
  · exact boundVariable_freeVariables_subset_singleton 1

theorem consRowsTailBranchTargetRight_freeVariables_subset_singleton
    (targetBoundary tokenCount : Nat) :
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        closedShift 4 (‘&0 + 2’ : ValuationTerm),
        (#0 : ArithmeticSemiterm Nat 4)])).freeVariables ⊆ {0} := by
  apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
  intro coordinate
  fin_cases coordinate
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 targetBoundary
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 tokenCount
  · exact shiftedIndexSecondSuccessor_freeVariables_subset_singleton 4
  · exact boundVariable_freeVariables_subset_singleton 0

#print axioms consRowsTailBranchTargetLeft_freeVariables_subset_singleton
#print axioms consRowsTailBranchTargetRight_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectNatListConsRowsTailBranchTargetFreeVariables
