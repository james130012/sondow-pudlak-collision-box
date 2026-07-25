import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
import integration.FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds

/-!
# Fully fixed arithmetic leaves of syntax-task-list uncons

This closes positivity, binary size, and the tail-area inequality.  The list
drop, triple-boundary, and list-cons graph leaves remain separate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsAtomicFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFixedWidthEntryBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds

private def unconsAtomicZeroValuation : Nat -> Nat := fun _ => 0

def unconsPositiveTermCodePolynomial (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘0’ : ValuationTerm)).length

def unconsPositiveFullyFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (unconsPositiveTermCodePolynomial bitBound)

theorem
    compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial_le_fullyFixed
    (sourceCount bitBound : Nat)
    (hsourceCountSize : Nat.size sourceCount <= bitBound) :
    compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial
        sourceCount <=
      unconsPositiveFullyFixedPayloadPolynomial bitBound := by
  let args : Fin 2 -> ValuationTerm :=
    ![(‘0’ : ValuationTerm), shortBinaryNumeralTerm sourceCount]
  have hsourceCode :
      (binaryTermCode (shortBinaryNumeralTerm sourceCount)).length <=
        unconsPositiveTermCodePolynomial bitBound := by
    have hraw := binaryNumeralTerm_code_length_le_envelope sourceCount bitBound
      hsourceCountSize
    unfold unconsPositiveTermCodePolynomial
    omega
  have hzeroCode :
      (binaryTermCode (‘0’ : ValuationTerm)).length <=
        unconsPositiveTermCodePolynomial bitBound := by
    unfold unconsPositiveTermCodePolynomial
    omega
  unfold compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial
    unconsPositiveFullyFixedPayloadPolynomial
  exact compilePositiveRelationPayloadPolynomial_le_fixed
    unconsAtomicZeroValuation Language.ORing.Rel.lt args 0
    (unconsPositiveTermCodePolynomial bitBound)
    (by
      change (‘0’ : ValuationTerm).freeVariables ⊆ {0}
      intro coordinate hcoordinate
      simp [LO.FirstOrder.Semiterm.Operator.operator] at hcoordinate)
    (by
      change
        (shortBinaryNumeralTerm sourceCount : ValuationTerm).freeVariables ⊆ {0}
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
      simp)
    (by rfl) hzeroCode hsourceCode

theorem compactNatSizeStructuralPayloadPolynomial_le_unconsFullyFixed
    (size value bitBound : Nat)
    (hsize : size = Nat.size value)
    (hvalueSize : Nat.size value <= bitBound) :
    compactNatSizeStructuralPayloadPolynomial size value <=
      compactNatSizeFixedPayloadPolynomial bitBound :=
  compactNatSizeStructuralPayloadPolynomial_le_fixed size value bitBound hsize
    hvalueSize

theorem
    compactAdditiveSyntaxTaskListUnconsRowsTailAreaPayloadPolynomial_le_fullyFixed
    (tailBoundarySize tailCount tokenCount tailBoundary numericBound bitBound :
      Nat)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (htailCount : tailCount <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListUnconsRowsTailAreaPayloadPolynomial
        tailBoundarySize tailCount tokenCount <=
      parserAreaFixedPayloadPolynomial bitBound := by
  let valuation : Nat -> Nat := fun _ => 0
  let leftTerm := shortBinaryNumeralTerm tailBoundarySize
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm tailCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables valuation
  let common :=
    compilePositiveRelationPayloadPolynomial valuation Language.Eq.eq args +
      compilePositiveRelationPayloadPolynomial valuation Language.ORing.Rel.lt
        args +
      weakeningFullAssemblyCost (insert equalityFormula Gamma) +
      weakeningFullAssemblyCost (insert strictFormula Gamma) +
      disjunctionFullAssemblyCost Gamma equalityFormula strictFormula
  have h :=
    boundaryAreaStructuralPayloadPolynomial_le_fixed tailBoundarySize tailCount
      tokenCount tailBoundary numericBound bitBound hsize htokenCount htailCount
      htailBoundarySize hnumericSize
  change common <= parserAreaFixedPayloadPolynomial bitBound at h
  change common <= parserAreaFixedPayloadPolynomial bitBound
  exact h

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsAtomicFullyFixedBounds
