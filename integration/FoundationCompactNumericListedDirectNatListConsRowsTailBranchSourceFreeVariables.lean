import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchTermFreeVariables
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Free-variable support of the two source entries in a cons-tail branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBranchSourceFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchTermFreeVariables

theorem consRowsTailBranchSourceLeft_freeVariables_subset_singleton
    (sourceBoundary tokenCount : Nat) :
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        closedShift 4 (&0 : ValuationTerm),
        (#3 : ArithmeticSemiterm Nat 4)])).freeVariables ⊆ {0} := by
  apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
  intro coordinate
  fin_cases coordinate
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 sourceBoundary
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 tokenCount
  · exact shiftedIndex_freeVariables_subset_singleton 4
  · exact boundVariable_freeVariables_subset_singleton 3

theorem consRowsTailBranchSourceRight_freeVariables_subset_singleton
    (sourceBoundary tokenCount : Nat) :
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        closedShift 4 (‘&0 + 1’ : ValuationTerm),
        (#2 : ArithmeticSemiterm Nat 4)])).freeVariables ⊆ {0} := by
  apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
  intro coordinate
  fin_cases coordinate
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 sourceBoundary
  · exact shiftedShortNumeral_freeVariables_subset_singleton 4 tokenCount
  · exact shiftedIndexSuccessor_freeVariables_subset_singleton 4
  · exact boundVariable_freeVariables_subset_singleton 2

#print axioms consRowsTailBranchSourceLeft_freeVariables_subset_singleton
#print axioms consRowsTailBranchSourceRight_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectNatListConsRowsTailBranchSourceFreeVariables
