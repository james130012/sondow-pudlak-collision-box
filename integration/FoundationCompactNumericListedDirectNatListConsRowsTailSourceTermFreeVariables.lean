import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyDefinitions
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAFreeFormulaVariableTransport

/-! # Closed terms used by the five-variable cons-tail source terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailSourceTermFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAFreeFormulaVariableTransport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

theorem consSourceShiftedShortNumeral_freeVariables_eq_empty
    (depth value : Nat) :
    (closedShift depth (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
  induction depth with
  | zero =>
      simpa only [closedShift] using
        shortBinaryNumeralTerm_freeVariables_eq_empty value
  | succ depth inductionHypothesis =>
      simp only [closedShift]
      exact bShift_freeVariables_eq_empty_of_empty _ inductionHypothesis

private theorem arithmeticOneTerm_freeVariables_eq_empty
    {arity : Nat} :
    (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem consSourceIndexSuccessor_freeVariables_eq_empty :
    (‘#4 + 1’ : ArithmeticSemiterm Nat 5).freeVariables = ∅ := by
  rw [arithmeticAddTerm_freeVariables_eq_union,
    arithmeticOneTerm_freeVariables_eq_empty]
  simp

private theorem arithmeticTwoValuationTerm_freeVariables_eq_empty :
    (‘2’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

theorem consSourceIndexSecondSuccessor_freeVariables_eq_empty :
    (‘#4 + 2’ : ArithmeticSemiterm Nat 5).freeVariables = ∅ := by
  have htwo : (‘2’ : ArithmeticSemiterm Nat 5).freeVariables = ∅ := by
    change (closedShift 5 (‘2’ : ValuationTerm)).freeVariables = ∅
    exact consSourceShiftedShortNumeral_freeVariables_eq_empty 5 2
  rw [arithmeticAddTerm_freeVariables_eq_union]
  rw [htwo]
  simp

#print axioms consSourceShiftedShortNumeral_freeVariables_eq_empty
#print axioms consSourceIndexSuccessor_freeVariables_eq_empty
#print axioms consSourceIndexSecondSuccessor_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsTailSourceTermFreeVariables
