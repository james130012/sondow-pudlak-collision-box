import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFormulaFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedCore
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds

/-! # Fixed atomic core for term-output-row certificates -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 180000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds

private abbrev termRowsAtomicZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsPositiveAtomicFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (termOutputFailureTermCodePolynomial bitBound)

def termRowsNegativeAtomicFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  termOutputFailureAtomicPayloadPolynomial bitBound

def termRowsAtomicLeafFormulaCodePolynomial (bitBound : Nat) : Nat :=
  outputRowsAtomicLeafFormulaCodePolynomial bitBound

theorem termRowsShortNumeralCode_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      termOutputFailureTermCodePolynomial bitBound :=
  failureShortNumeralCode_le value bitBound hvalue

theorem termRowsLiteralCode_le
    (literal : ValuationTerm) (bitBound : Nat)
    (hliteral :
      literal = (‘0’ : ValuationTerm) ∨
      literal = (‘1’ : ValuationTerm) ∨
      literal = (‘2’ : ValuationTerm) ∨
      literal = (‘4’ : ValuationTerm) ∨
      literal = (‘5’ : ValuationTerm)) :
    (binaryTermCode literal).length <=
      termOutputFailureTermCodePolynomial bitBound := by
  unfold termOutputFailureTermCodePolynomial
  exact outputRowsModeLiteralCode_le literal bitBound hliteral

theorem termRowsLiteral_closed
    (literal : ValuationTerm)
    (hliteral :
      literal = (‘0’ : ValuationTerm) ∨
      literal = (‘1’ : ValuationTerm) ∨
      literal = (‘2’ : ValuationTerm) ∨
      literal = (‘4’ : ValuationTerm) ∨
      literal = (‘5’ : ValuationTerm)) :
    literal.freeVariables = ∅ :=
  outputRowsModeLiteral_closed literal hliteral

theorem termRowsAddShortNumeralsCode_le
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    (binaryTermCode
      (nativeAddTerm (shortBinaryNumeralTerm left)
        (shortBinaryNumeralTerm right))).length <=
      termOutputFailureTermCodePolynomial bitBound := by
  have hleftCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hrightCode :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hright
  have hadd := paAddTerm_code_length_le
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
  change (binaryTermCode
    (paAddTerm (shortBinaryNumeralTerm left)
      (shortBinaryNumeralTerm right))).length <= _
  unfold termOutputFailureTermCodePolynomial
    outputRowsAtomicTermCodePolynomial
  omega

theorem termRowsAddShortNumerals_closed (left right : Nat) :
    (nativeAddTerm (shortBinaryNumeralTerm left)
      (shortBinaryNumeralTerm right)).freeVariables = ∅ := by
  rw [nativeAddTerm_freeVariables_failure,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  simp

theorem termRowsNativeEqStructuralEnvelope_le_fixed_of_closed
    (left right : ValuationTerm) (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    termRowsNativeEqStructuralEnvelope left right <=
      termRowsPositiveAtomicFixedPayloadPolynomial bitBound := by
  unfold termRowsNativeEqStructuralEnvelope
    termRowsPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    termRowsAtomicZeroValuation Language.Eq.eq left right 0
    (termOutputFailureTermCodePolynomial bitBound)
    hleftClosed hrightClosed hleftCode hrightCode

theorem termRowsNativeNeStructuralEnvelope_le_fixed_of_closed
    (left right : ValuationTerm) (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    termRowsNativeNeStructuralEnvelope left right <=
      termRowsNegativeAtomicFixedPayloadPolynomial bitBound := by
  unfold termRowsNegativeAtomicFixedPayloadPolynomial
  exact termRowsNativeNeStructuralEnvelope_le_fixed left right bitBound
    hleftClosed hrightClosed hleftCode hrightCode

theorem termRowsNativeLtStructuralEnvelope_le_fixed_of_closed
    (left right : ValuationTerm) (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    termRowsNativeLtStructuralEnvelope left right <=
      termRowsPositiveAtomicFixedPayloadPolynomial bitBound := by
  unfold termRowsNativeLtStructuralEnvelope
    termRowsPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    termRowsAtomicZeroValuation Language.ORing.Rel.lt left right 0
    (termOutputFailureTermCodePolynomial bitBound)
    hleftClosed hrightClosed hleftCode hrightCode

theorem termRowsNativeEqCertificate_structuralPayloadBound_le_fixed
    (left right : ValuationTerm)
    (heq : termValue termRowsAtomicZeroValuation left =
      termValue termRowsAtomicZeroValuation right)
    (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    hybridFormulaStructuralPayloadBound (nativeEqCertificate left right heq) <=
      termRowsPositiveAtomicFixedPayloadPolynomial bitBound :=
  (nativeEqCertificate_structuralPayloadBound_le_transparent left right heq).trans
    (termRowsNativeEqStructuralEnvelope_le_fixed_of_closed left right bitBound
      hleftClosed hrightClosed hleftCode hrightCode)

theorem termRowsNativeNeCertificate_structuralPayloadBound_le_fixed
    (left right : ValuationTerm)
    (hne : termValue termRowsAtomicZeroValuation left ≠
      termValue termRowsAtomicZeroValuation right)
    (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    hybridFormulaStructuralPayloadBound (nativeNeCertificate left right hne) <=
      termRowsNegativeAtomicFixedPayloadPolynomial bitBound :=
  (nativeNeCertificate_structuralPayloadBound_le_transparent left right hne).trans
    (termRowsNativeNeStructuralEnvelope_le_fixed_of_closed left right bitBound
      hleftClosed hrightClosed hleftCode hrightCode)

theorem termRowsNativeLtCertificate_structuralPayloadBound_le_fixed
    (left right : ValuationTerm)
    (hlt : termValue termRowsAtomicZeroValuation left <
      termValue termRowsAtomicZeroValuation right)
    (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    hybridFormulaStructuralPayloadBound (nativeLtCertificate left right hlt) <=
      termRowsPositiveAtomicFixedPayloadPolynomial bitBound :=
  (nativeLtCertificate_structuralPayloadBound_le_transparent left right hlt).trans
    (termRowsNativeLtStructuralEnvelope_le_fixed_of_closed left right bitBound
      hleftClosed hrightClosed hleftCode hrightCode)

theorem consumedCountEqualityCertificate_structuralPayloadBound_le_fixed
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hcurrentCountSize : Nat.size current.parserTokensCount <= bitBound)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (hnextCountSize : Nat.size next.parserTokensCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (consumedCountEqualityCertificate current next consumedCount hcount) <=
      termRowsPositiveAtomicFixedPayloadPolynomial bitBound := by
  have htransparent :=
    consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
      current next consumedCount hcount
  exact htransparent.trans
    (termRowsNativeEqStructuralEnvelope_le_fixed_of_closed
      (shortBinaryNumeralTerm current.parserTokensCount)
      (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
        (shortBinaryNumeralTerm next.parserTokensCount)) bitBound
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (termRowsAddShortNumerals_closed _ _)
      (termRowsShortNumeralCode_le _ bitBound hcurrentCountSize)
      (termRowsAddShortNumeralsCode_le _ _ bitBound hconsumedSize
        hnextCountSize))

theorem shortNumeralLiteralEqCertificate_structuralPayloadBound_le_fixed
    (value expected : Nat) (literal : ValuationTerm)
    (hliteralValue : termValue termRowsAtomicZeroValuation literal = expected)
    (heq : value = expected) (bitBound : Nat)
    (hvalueSize : Nat.size value <= bitBound)
    (hliteralClosed : literal.freeVariables = ∅)
    (hliteralCode : (binaryTermCode literal).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    hybridFormulaStructuralPayloadBound
        (shortNumeralLiteralEqCertificate value expected literal hliteralValue
          heq) <=
      termRowsPositiveAtomicFixedPayloadPolynomial bitBound :=
  (shortNumeralLiteralEqCertificate_structuralPayloadBound_le_transparent
    value expected literal hliteralValue heq).trans
      (termRowsNativeEqStructuralEnvelope_le_fixed_of_closed
        (shortBinaryNumeralTerm value) literal bitBound
        (shortBinaryNumeralTerm_freeVariables_eq_empty _) hliteralClosed
        (termRowsShortNumeralCode_le value bitBound hvalueSize) hliteralCode)

theorem shortNumeralLiteralNeCertificate_structuralPayloadBound_le_fixed
    (value expected : Nat) (literal : ValuationTerm)
    (hliteralValue : termValue termRowsAtomicZeroValuation literal = expected)
    (hne : value ≠ expected) (bitBound : Nat)
    (hvalueSize : Nat.size value <= bitBound)
    (hliteralClosed : literal.freeVariables = ∅)
    (hliteralCode : (binaryTermCode literal).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    hybridFormulaStructuralPayloadBound
        (shortNumeralLiteralNeCertificate value expected literal hliteralValue
          hne) <=
      termRowsNegativeAtomicFixedPayloadPolynomial bitBound :=
  (shortNumeralLiteralNeCertificate_structuralPayloadBound_le_transparent
    value expected literal hliteralValue hne).trans
      (termRowsNativeNeStructuralEnvelope_le_fixed_of_closed
        (shortBinaryNumeralTerm value) literal bitBound
        (shortBinaryNumeralTerm_freeVariables_eq_empty _) hliteralClosed
        (termRowsShortNumeralCode_le value bitBound hvalueSize) hliteralCode)

#print axioms termRowsNativeEqCertificate_structuralPayloadBound_le_fixed
#print axioms termRowsNativeNeCertificate_structuralPayloadBound_le_fixed
#print axioms termRowsNativeLtCertificate_structuralPayloadBound_le_fixed
#print axioms consumedCountEqualityCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
