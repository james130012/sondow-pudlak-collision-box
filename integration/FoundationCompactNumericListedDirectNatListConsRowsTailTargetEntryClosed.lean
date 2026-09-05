import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSourceTermFreeVariables
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Closed target-entry formulas of the cons-tail source terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTargetEntryClosed

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailSourceTermFreeVariables

theorem consRowsTailSourceTerminalTargetLeft_freeVariables_eq_empty
    (targetBoundary tokenCount : Nat) :
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
        closedShift 5 (shortBinaryNumeralTerm tokenCount),
        (‘#4 + 1’ : ArithmeticSemiterm Nat 5),
        (#1 : ArithmeticSemiterm Nat 5)])).freeVariables = ∅ := by
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 targetBoundary
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 tokenCount
  · exact consSourceIndexSuccessor_freeVariables_eq_empty
  · simp

theorem consRowsTailSourceTerminalTargetRight_freeVariables_eq_empty
    (targetBoundary tokenCount : Nat) :
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
        closedShift 5 (shortBinaryNumeralTerm tokenCount),
        (‘#4 + 2’ : ArithmeticSemiterm Nat 5),
        (#0 : ArithmeticSemiterm Nat 5)])).freeVariables = ∅ := by
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 targetBoundary
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 tokenCount
  · exact consSourceIndexSecondSuccessor_freeVariables_eq_empty
  · simp

#print axioms consRowsTailSourceTerminalTargetLeft_freeVariables_eq_empty
#print axioms consRowsTailSourceTerminalTargetRight_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsTailTargetEntryClosed
