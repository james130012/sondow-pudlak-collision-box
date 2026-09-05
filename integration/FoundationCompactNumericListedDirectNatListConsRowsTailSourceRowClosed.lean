import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSourceTermFreeVariables
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Closed atomic-row formula of the cons-tail source terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailSourceRowClosed

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailSourceTermFreeVariables

theorem consRowsTailSourceTerminalAtomicRow_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat) :
    (((Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜
      ![closedShift 5 (shortBinaryNumeralTerm tokenTable),
        closedShift 5 (shortBinaryNumeralTerm width),
        closedShift 5 (shortBinaryNumeralTerm tokenCount),
        (#3 : ArithmeticSemiterm Nat 5),
        (#2 : ArithmeticSemiterm Nat 5),
        (#1 : ArithmeticSemiterm Nat 5),
        (#0 : ArithmeticSemiterm Nat 5)])).freeVariables = ∅ := by
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 tokenTable
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 width
  · exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 tokenCount
  · simp
  · simp
  · simp
  · simp

#print axioms consRowsTailSourceTerminalAtomicRow_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsTailSourceRowClosed
