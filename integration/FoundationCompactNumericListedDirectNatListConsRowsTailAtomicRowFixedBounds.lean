import integration.FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
import integration.FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds

/-! # Fixed atomic-row resource for natural-list cons tail rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 280000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailAtomicRowFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
open FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
open FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds

theorem natListConsRowsTailAtomicRowPayload_le_fixed
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
      numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceLeft : sourceLeft <= numericBound)
    (hsourceRight : sourceRight <= numericBound)
    (htargetLeft : targetLeft <= numericBound)
    (htargetRight : targetRight <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm sourceLeft)
        (shortBinaryNumeralTerm sourceRight)
        (shortBinaryNumeralTerm targetLeft)
        (shortBinaryNumeralTerm targetRight) <=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound :=
  compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope_le_fixed
    valuation tokenTable width tokenCount sourceLeft sourceRight targetLeft
    targetRight numericBound bitBound hwidth htokenCount hsourceLeft
    hsourceRight htargetLeft htargetRight htokenTableSize hnumericSize

theorem natListConsRowsTailAtomicRowFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight :
      Nat) :
    (compactAdditiveAtomicRowEqAtValuationFormula
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm sourceLeft)
      (shortBinaryNumeralTerm sourceRight)
      (shortBinaryNumeralTerm targetLeft)
      (shortBinaryNumeralTerm targetRight)).freeVariables = ∅ := by
  unfold compactAdditiveAtomicRowEqAtValuationFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms natListConsRowsTailAtomicRowPayload_le_fixed
#print axioms natListConsRowsTailAtomicRowFormula_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsTailAtomicRowFixedBounds
