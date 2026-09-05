import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSyntaxUniformBound
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
import integration.FoundationCompactPAFreeFormulaVariableTransport

/-! # Free-variable support of terms used by one cons-tail branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBranchTermFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAFreeFormulaVariableTransport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

theorem shiftedShortNumeral_freeVariables_subset_singleton
    (depth value : Nat) :
    (closedShift depth (shortBinaryNumeralTerm value)).freeVariables ⊆ {0} := by
  induction depth with
  | zero =>
      rw [show closedShift 0 (shortBinaryNumeralTerm value) =
        shortBinaryNumeralTerm value by rfl]
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
      simp
  | succ depth inductionHypothesis =>
      simp only [closedShift]
      rw [bShiftTerm_freeVariables_eq]
      exact inductionHypothesis

theorem shiftedIndex_freeVariables_subset_singleton
    (depth : Nat) :
    (closedShift depth (&0 : ValuationTerm)).freeVariables ⊆ {0} := by
  induction depth with
  | zero => simp [closedShift]
  | succ depth inductionHypothesis =>
      simp only [closedShift]
      rw [bShiftTerm_freeVariables_eq]
      exact inductionHypothesis

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem shiftedIndexSuccessor_freeVariables_subset_singleton
    (depth : Nat) :
    (closedShift depth (‘&0 + 1’ : ValuationTerm)).freeVariables ⊆ {0} := by
  induction depth with
  | zero =>
      rw [show closedShift 0 (‘&0 + 1’ : ValuationTerm) =
        (‘&0 + 1’ : ValuationTerm) by rfl]
      rw [arithmeticAddTerm_freeVariables_eq_union]
      rw [arithmeticOneTerm_freeVariables_eq_empty]
      simp
  | succ depth inductionHypothesis =>
      simp only [closedShift]
      rw [bShiftTerm_freeVariables_eq]
      exact inductionHypothesis

theorem shiftedIndexSecondSuccessor_freeVariables_subset_singleton
    (depth : Nat) :
    (closedShift depth (‘&0 + 2’ : ValuationTerm)).freeVariables ⊆ {0} := by
  induction depth with
  | zero =>
      rw [show closedShift 0 (‘&0 + 2’ : ValuationTerm) =
        (‘&0 + 2’ : ValuationTerm) by rfl]
      rw [arithmeticAddTerm_freeVariables_eq_union]
      simp [LO.FirstOrder.Semiterm.Operator.operator]
  | succ depth inductionHypothesis =>
      simp only [closedShift]
      rw [bShiftTerm_freeVariables_eq]
      exact inductionHypothesis

theorem boundVariable_freeVariables_subset_singleton
    {arity : Nat} (coordinate : Fin arity) :
    (#coordinate : ArithmeticSemiterm Nat arity).freeVariables ⊆ {0} := by
  simp

#print axioms shiftedShortNumeral_freeVariables_subset_singleton
#print axioms shiftedIndex_freeVariables_subset_singleton
#print axioms shiftedIndexSuccessor_freeVariables_subset_singleton
#print axioms shiftedIndexSecondSuccessor_freeVariables_subset_singleton
#print axioms boundVariable_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectNatListConsRowsTailBranchTermFreeVariables
