import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSourceTermFreeVariables
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Closed source-entry formulas of the cons-tail source terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailSourceEntryClosed

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailSourceTermFreeVariables

theorem consRowsTailSourceTerminalSourceLeft_freeVariables_eq_empty
    (sourceBoundary tokenCount : Nat) :
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 5 (shortBinaryNumeralTerm tokenCount),
        (#4 : ArithmeticSemiterm Nat 5),
        (#3 : ArithmeticSemiterm Nat 5)])).freeVariables = ∅ := by
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 sourceBoundary
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 tokenCount
  · simp
  · simp

theorem consRowsTailSourceTerminalSourceRight_freeVariables_eq_empty
    (sourceBoundary tokenCount : Nat) :
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 5 (shortBinaryNumeralTerm tokenCount),
        (‘#4 + 1’ : ArithmeticSemiterm Nat 5),
        (#2 : ArithmeticSemiterm Nat 5)])).freeVariables = ∅ := by
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 sourceBoundary
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 tokenCount
  · exact consSourceIndexSuccessor_freeVariables_eq_empty
  · simp

#print axioms consRowsTailSourceTerminalSourceLeft_freeVariables_eq_empty
#print axioms consRowsTailSourceTerminalSourceRight_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsTailSourceEntryClosed
