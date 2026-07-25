import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds
import integration.FoundationCompactPAHybridSixConjunctionClosedGeneralBounds

/-!
# Fixed five-mode exclusion with a checked tail

The five negative equality certificates and the supplied tail form one
right-associated six-leaf conjunction.  All five atomic resources use the same
closed negative-relation polynomial, and all connective costs use one syntax
coordinate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsOtherModeFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridSixConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds

private abbrev otherModeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation

def outputRowsOtherModeFixedPayloadPolynomial
    (syntaxResource bitBound tailResource : Nat) : Nat :=
  hybridSixConjunctionGeneralPayloadEnvelope syntaxResource
    (outputRowsNegativeAtomicFixedPayloadPolynomial bitBound)
    (outputRowsNegativeAtomicFixedPayloadPolynomial bitBound)
    (outputRowsNegativeAtomicFixedPayloadPolynomial bitBound)
    (outputRowsNegativeAtomicFixedPayloadPolynomial bitBound)
    (outputRowsNegativeAtomicFixedPayloadPolynomial bitBound)
    tailResource

private theorem nativeNeClosed_otherMode
    (mode : Nat) (literal : ValuationTerm)
    (hliteral : literal.freeVariables = ∅) :
    (nativeNeFormula (shortBinaryNumeralTerm mode) literal).freeVariables =
      ∅ := by
  simp [nativeNeFormula, nativeEqFormula,
    shortBinaryNumeralTerm_freeVariables_eq_empty, hliteral]

theorem otherModeWithTailCertificate_structuralPayloadBound_le_fixed
    (mode bitBound syntaxResource : Nat)
    (hzero : mode ≠ 0) (hone : mode ≠ 1) (htwo : mode ≠ 2)
    (hfour : mode ≠ 4) (hfive : mode ≠ 5)
    (tail : ValuationFormula)
    (tailCertificate :
      CheckedHybridValuationBoundedFormulaCertificate otherModeZeroValuation
        tail)
    (tailResource : Nat)
    (htail :
      hybridFormulaStructuralPayloadBound tailCertificate <= tailResource)
    (hmodeSize : Nat.size mode <= bitBound)
    (hsyntaxPositive : 1 <= syntaxResource)
    (htailClosed : tail.freeVariables = ∅)
    (hfullCode :
      (binaryFormulaCode
        (otherModeWithTailFormula (shortBinaryNumeralTerm mode) tail)).length <=
          syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (otherModeWithTailCertificate mode hzero hone htwo hfour hfive tail
          tailCertificate) <=
      outputRowsOtherModeFixedPayloadPolynomial syntaxResource bitBound
        tailResource := by
  let modeTerm := shortBinaryNumeralTerm mode
  let zeroLiteral : ValuationTerm := (‘0’ : ValuationTerm)
  let oneLiteral : ValuationTerm := (‘1’ : ValuationTerm)
  let twoLiteral : ValuationTerm := (‘2’ : ValuationTerm)
  let fourLiteral : ValuationTerm := (‘4’ : ValuationTerm)
  let fiveLiteral : ValuationTerm := (‘5’ : ValuationTerm)
  let zeroFormula := nativeNeFormula modeTerm zeroLiteral
  let oneFormula := nativeNeFormula modeTerm oneLiteral
  let twoFormula := nativeNeFormula modeTerm twoLiteral
  let fourFormula := nativeNeFormula modeTerm fourLiteral
  let fiveFormula := nativeNeFormula modeTerm fiveLiteral
  let atomResource := outputRowsNegativeAtomicFixedPayloadPolynomial bitBound
  let zeroCertificate := modeNativeInequalityCertificate mode zeroLiteral 0
    (termValue_arithmeticZero otherModeZeroValuation) hzero
  let oneCertificate := modeNativeInequalityCertificate mode oneLiteral 1
    (termValue_arithmeticOne otherModeZeroValuation) hone
  let twoCertificate := modeNativeInequalityCertificate mode twoLiteral 2
    (termValue_arithmeticTwo otherModeZeroValuation) htwo
  let fourCertificate := modeNativeInequalityCertificate mode fourLiteral 4
    (termValue_arithmeticFour otherModeZeroValuation) hfour
  let fiveCertificate := modeNativeInequalityCertificate mode fiveLiteral 5
    (termValue_arithmeticFive otherModeZeroValuation) hfive
  have hzeroLiteral :
      zeroLiteral = (‘0’ : ValuationTerm) ∨
      zeroLiteral = (‘1’ : ValuationTerm) ∨
      zeroLiteral = (‘2’ : ValuationTerm) ∨
      zeroLiteral = (‘4’ : ValuationTerm) ∨
      zeroLiteral = (‘5’ : ValuationTerm) := Or.inl rfl
  have honeLiteral :
      oneLiteral = (‘0’ : ValuationTerm) ∨
      oneLiteral = (‘1’ : ValuationTerm) ∨
      oneLiteral = (‘2’ : ValuationTerm) ∨
      oneLiteral = (‘4’ : ValuationTerm) ∨
      oneLiteral = (‘5’ : ValuationTerm) := Or.inr (Or.inl rfl)
  have htwoLiteral :
      twoLiteral = (‘0’ : ValuationTerm) ∨
      twoLiteral = (‘1’ : ValuationTerm) ∨
      twoLiteral = (‘2’ : ValuationTerm) ∨
      twoLiteral = (‘4’ : ValuationTerm) ∨
      twoLiteral = (‘5’ : ValuationTerm) :=
    Or.inr (Or.inr (Or.inl rfl))
  have hfourLiteral :
      fourLiteral = (‘0’ : ValuationTerm) ∨
      fourLiteral = (‘1’ : ValuationTerm) ∨
      fourLiteral = (‘2’ : ValuationTerm) ∨
      fourLiteral = (‘4’ : ValuationTerm) ∨
      fourLiteral = (‘5’ : ValuationTerm) :=
    Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hfiveLiteral :
      fiveLiteral = (‘0’ : ValuationTerm) ∨
      fiveLiteral = (‘1’ : ValuationTerm) ∨
      fiveLiteral = (‘2’ : ValuationTerm) ∨
      fiveLiteral = (‘4’ : ValuationTerm) ∨
      fiveLiteral = (‘5’ : ValuationTerm) :=
    Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hzeroClosed := outputRowsModeLiteral_closed zeroLiteral hzeroLiteral
  have honeClosed := outputRowsModeLiteral_closed oneLiteral honeLiteral
  have htwoClosed := outputRowsModeLiteral_closed twoLiteral htwoLiteral
  have hfourClosed := outputRowsModeLiteral_closed fourLiteral hfourLiteral
  have hfiveClosed := outputRowsModeLiteral_closed fiveLiteral hfiveLiteral
  have hzeroResource :
      hybridFormulaStructuralPayloadBound zeroCertificate <= atomResource := by
    exact modeNativeInequalityCertificate_structuralPayloadBound_le_fixed
      mode zeroLiteral 0 bitBound
      (termValue_arithmeticZero otherModeZeroValuation) hzero hmodeSize
      hzeroClosed (outputRowsModeLiteralCode_le zeroLiteral bitBound
        hzeroLiteral)
  have honeResource :
      hybridFormulaStructuralPayloadBound oneCertificate <= atomResource := by
    exact modeNativeInequalityCertificate_structuralPayloadBound_le_fixed
      mode oneLiteral 1 bitBound
      (termValue_arithmeticOne otherModeZeroValuation) hone hmodeSize
      honeClosed (outputRowsModeLiteralCode_le oneLiteral bitBound honeLiteral)
  have htwoResource :
      hybridFormulaStructuralPayloadBound twoCertificate <= atomResource := by
    exact modeNativeInequalityCertificate_structuralPayloadBound_le_fixed
      mode twoLiteral 2 bitBound
      (termValue_arithmeticTwo otherModeZeroValuation) htwo hmodeSize
      htwoClosed (outputRowsModeLiteralCode_le twoLiteral bitBound htwoLiteral)
  have hfourResource :
      hybridFormulaStructuralPayloadBound fourCertificate <= atomResource := by
    exact modeNativeInequalityCertificate_structuralPayloadBound_le_fixed
      mode fourLiteral 4 bitBound
      (termValue_arithmeticFour otherModeZeroValuation) hfour hmodeSize
      hfourClosed
      (outputRowsModeLiteralCode_le fourLiteral bitBound hfourLiteral)
  have hfiveResource :
      hybridFormulaStructuralPayloadBound fiveCertificate <= atomResource := by
    exact modeNativeInequalityCertificate_structuralPayloadBound_le_fixed
      mode fiveLiteral 5 bitBound
      (termValue_arithmeticFive otherModeZeroValuation) hfive hmodeSize
      hfiveClosed
      (outputRowsModeLiteralCode_le fiveLiteral bitBound hfiveLiteral)
  let fiveTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    fiveCertificate tailCertificate
  have hfiveTail := transparentHybridConjunctionPayloadBound_le
    fiveCertificate tailCertificate atomResource tailResource hfiveResource
    htail
  let fourTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    fourCertificate fiveTail
  have hfourTail := transparentHybridConjunctionPayloadBound_le
    fourCertificate fiveTail atomResource
    (transparentHybridConjunctionPayloadEnvelope otherModeZeroValuation
      fiveFormula tail atomResource tailResource) hfourResource hfiveTail
  let twoTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    twoCertificate fourTail
  have htwoTail := transparentHybridConjunctionPayloadBound_le
    twoCertificate fourTail atomResource
    (transparentHybridConjunctionPayloadEnvelope otherModeZeroValuation
      fourFormula (fiveFormula ⋏ tail) atomResource
      (transparentHybridConjunctionPayloadEnvelope otherModeZeroValuation
        fiveFormula tail atomResource tailResource)) htwoResource hfourTail
  let oneTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    oneCertificate twoTail
  have honeTail := transparentHybridConjunctionPayloadBound_le
    oneCertificate twoTail atomResource
    (transparentHybridConjunctionPayloadEnvelope otherModeZeroValuation
      twoFormula (fourFormula ⋏ (fiveFormula ⋏ tail)) atomResource
      (transparentHybridConjunctionPayloadEnvelope otherModeZeroValuation
        fourFormula (fiveFormula ⋏ tail) atomResource
        (transparentHybridConjunctionPayloadEnvelope otherModeZeroValuation
          fiveFormula tail atomResource tailResource))) honeResource htwoTail
  have hdirect := transparentHybridConjunctionPayloadBound_le
    zeroCertificate oneTail atomResource
    (transparentHybridConjunctionPayloadEnvelope otherModeZeroValuation
      oneFormula (twoFormula ⋏ (fourFormula ⋏ (fiveFormula ⋏ tail)))
      atomResource
      (transparentHybridConjunctionPayloadEnvelope otherModeZeroValuation
        twoFormula (fourFormula ⋏ (fiveFormula ⋏ tail)) atomResource
        (transparentHybridConjunctionPayloadEnvelope otherModeZeroValuation
          fourFormula (fiveFormula ⋏ tail) atomResource
          (transparentHybridConjunctionPayloadEnvelope otherModeZeroValuation
            fiveFormula tail atomResource tailResource)))) hzeroResource honeTail
  have hzeroFormulaClosed :=
    nativeNeClosed_otherMode mode zeroLiteral hzeroClosed
  have honeFormulaClosed :=
    nativeNeClosed_otherMode mode oneLiteral honeClosed
  have htwoFormulaClosed :=
    nativeNeClosed_otherMode mode twoLiteral htwoClosed
  have hfourFormulaClosed :=
    nativeNeClosed_otherMode mode fourLiteral hfourClosed
  have hfiveFormulaClosed :=
    nativeNeClosed_otherMode mode fiveLiteral hfiveClosed
  have hassembly :=
    transparentHybridSixConjunctionPayloadEnvelope_le_closedGeneral
      otherModeZeroValuation zeroFormula oneFormula twoFormula fourFormula
      fiveFormula tail atomResource atomResource atomResource atomResource
      atomResource tailResource syntaxResource hsyntaxPositive
      hzeroFormulaClosed honeFormulaClosed htwoFormulaClosed
      hfourFormulaClosed hfiveFormulaClosed htailClosed (by
        simpa only [otherModeWithTailFormula, modeTerm, zeroFormula, oneFormula,
          twoFormula, fourFormula, fiveFormula] using hfullCode)
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        zeroCertificate oneTail) <= _
  exact hdirect.trans (by
    unfold outputRowsOtherModeFixedPayloadPolynomial
    simpa only [atomResource] using hassembly)

#print axioms
  otherModeWithTailCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsOtherModeFixedBounds
