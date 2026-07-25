import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeSyntaxFixedBounds

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeFixedBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeSyntaxFixedBounds

def outputRowsRawModeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  let syntaxResource := outputRowsRawModeSyntaxPolynomial bitBound
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound)))

theorem rawModeLeafEnvelope_le_fixed
    (mode bitBound : Nat) (literal : ValuationTerm)
    (hmodeSize : Nat.size mode <= bitBound)
    (hliteral :
      literal = (‘0’ : ValuationTerm) ∨
      literal = (‘1’ : ValuationTerm) ∨
      literal = (‘2’ : ValuationTerm) ∨
      literal = (‘4’ : ValuationTerm) ∨
      literal = (‘5’ : ValuationTerm)) :
    outputRowsNativeEqStructuralEnvelope (shortBinaryNumeralTerm mode)
        literal <=
      outputRowsPositiveAtomicFixedPayloadPolynomial bitBound :=
  outputRowsNativeEqStructuralEnvelope_le_fixed mode literal bitBound
    hmodeSize (outputRowsModeLiteral_closed literal hliteral)
    (outputRowsModeLiteralCode_le literal bitBound hliteral)

#print axioms rawModeLeafEnvelope_le_fixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeFixedBounds
