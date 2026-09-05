import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadSyntaxUniformBound
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Closedness of the installed natural-list cons head formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsHeadBodyClosed

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadSyntaxUniformBound

private theorem natListConsClosedShift_freeVariables_eq_empty
    (arity : Nat) (term : ValuationTerm)
    (hterm : term.freeVariables = ∅) :
    (FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.closedShift
      arity term).freeVariables = ∅ := by
  induction arity with
  | zero => simpa [
      FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.closedShift]
  | succ arity inductionHypothesis =>
      simp only [
        FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.closedShift]
      exact bShift_freeVariables_eq_empty_of_empty _ inductionHypothesis

private theorem natListConsArithmeticOne_freeVariables_eq_empty
    {arity : Nat} :
    (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem natListConsBexsLTSucc_freeVariables_eq_empty_of_empty
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity)
    (hbody : body.freeVariables = ∅)
    (hbound : bound.freeVariables = ∅) :
    (body.bexsLTSucc bound).freeVariables = ∅ := by
  have hone : (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ :=
    natListConsArithmeticOne_freeVariables_eq_empty
  have hsuccessor :
      (‘!!bound + 1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    rw [arithmeticAddTerm_freeVariables_eq_union, hbound, hone]
    simp
  have hshifted :
      (Rew.bShift
        (‘!!bound + 1’ : ArithmeticSemiterm Nat arity)).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty _ hsuccessor
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT LO.FirstOrder.bexs
  rw [LO.FirstOrder.Semiformula.freeVariables_exs,
    LO.FirstOrder.Semiformula.freeVariables_and,
    lessThanFormula_freeVariables, hshifted, hbody]
  simp

theorem compactAdditiveNatListConsRowsHeadBody_freeVariables_eq_empty
    (tokenTable width tokenCount targetBoundary head : Nat) :
    (compactAdditiveNatListConsRowsHeadBody tokenTable width tokenCount
      targetBoundary head).freeVariables = ∅ := by
  let terminal := compactAdditiveNatListConsRowsHeadTerminal tokenTable width
    tokenCount targetBoundary head
  let innerBound : ArithmeticSemiterm Nat 1 :=
    closedShift 1 (shortBinaryNumeralTerm tokenCount)
  let outerBound : ValuationTerm := shortBinaryNumeralTerm tokenCount
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    exact compactAdditiveNatListConsRowsHeadTerminal_freeVariables_eq_empty
      tokenTable width tokenCount targetBoundary head
  have hinnerBound : innerBound.freeVariables = ∅ := by
    dsimp only [innerBound]
    exact natListConsClosedShift_freeVariables_eq_empty 1 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have houterBound : outerBound.freeVariables = ∅ := by
    dsimp only [outerBound]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hinner := natListConsBexsLTSucc_freeVariables_eq_empty_of_empty
    terminal innerBound hterminal hinnerBound
  have houter := natListConsBexsLTSucc_freeVariables_eq_empty_of_empty
    (terminal.bexsLTSucc innerBound) outerBound hinner houterBound
  simpa only [compactAdditiveNatListConsRowsHeadBody, terminal, innerBound,
    outerBound] using houter

#print axioms compactAdditiveNatListConsRowsHeadBody_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsHeadBodyClosed
