import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsZeroOneGuardFixedBounds

/-! # Fully fixed captured and residual guards for term-output rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 180000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds

private abbrev termRowsComparisonGuardZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

theorem capturedGuardPayloadEnvelope_le_fixed
    (consumedCount tag argument witnessCount bitBound : Nat)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (htagSize : Nat.size tag <= bitBound)
    (hargumentSize : Nat.size argument <= bitBound)
    (hwitnessCountSize : Nat.size witnessCount <= bitBound) :
    capturedGuardPayloadEnvelope consumedCount tag argument witnessCount <=
      termRowsThreeGuardFixedPayloadPolynomial bitBound := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let argumentTerm := shortBinaryNumeralTerm argument
  let witnessCountTerm := shortBinaryNumeralTerm witnessCount
  let consumedFormula := nativeEqFormula consumedTerm (‘2’ : ValuationTerm)
  let tagFormula := nativeEqFormula tagTerm (‘1’ : ValuationTerm)
  let comparisonFormula := nativeLtFormula argumentTerm witnessCountTerm
  have hconsumedTermClosed : consumedTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htagTermClosed : tagTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hargumentTermClosed : argumentTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hwitnessCountTermClosed : witnessCountTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have honeClosed : (‘1’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl))
  have htwoClosed : (‘2’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘2’ : ValuationTerm)
      (Or.inr (Or.inr (Or.inl rfl)))
  have hconsumedTermCode := termRowsShortNumeralCode_le consumedCount bitBound
    hconsumedSize
  have htagTermCode := termRowsShortNumeralCode_le tag bitBound htagSize
  have hargumentTermCode := termRowsShortNumeralCode_le argument bitBound
    hargumentSize
  have hwitnessCountTermCode := termRowsShortNumeralCode_le witnessCount
    bitBound hwitnessCountSize
  have honeCode := termRowsLiteralCode_le (‘1’ : ValuationTerm) bitBound
    (Or.inr (Or.inl rfl))
  have htwoCode := termRowsLiteralCode_le (‘2’ : ValuationTerm) bitBound
    (Or.inr (Or.inr (Or.inl rfl)))
  have hconsumedResource := termRowsNativeEqStructuralEnvelope_le_guardLeaf
    consumedTerm (‘2’ : ValuationTerm) bitBound hconsumedTermClosed htwoClosed
    hconsumedTermCode htwoCode
  have htagResource := termRowsNativeEqStructuralEnvelope_le_guardLeaf
    tagTerm (‘1’ : ValuationTerm) bitBound htagTermClosed honeClosed
    htagTermCode honeCode
  have hcomparisonResource := termRowsNativeLtStructuralEnvelope_le_guardLeaf
    argumentTerm witnessCountTerm bitBound hargumentTermClosed
    hwitnessCountTermClosed hargumentTermCode hwitnessCountTermCode
  have hconsumedFormulaClosed := termRowsNativeEqFormula_closed consumedTerm
    (‘2’ : ValuationTerm) hconsumedTermClosed htwoClosed
  have htagFormulaClosed := termRowsNativeEqFormula_closed tagTerm
    (‘1’ : ValuationTerm) htagTermClosed honeClosed
  have hcomparisonFormulaClosed := termRowsNativeLtFormula_closed argumentTerm
    witnessCountTerm hargumentTermClosed hwitnessCountTermClosed
  have hclosed := termRowsThreeGuardFormula_closed consumedFormula tagFormula
    comparisonFormula hconsumedFormulaClosed htagFormulaClosed
    hcomparisonFormulaClosed
  have hconsumedFormulaCode :=
    termRowsNativeEqFormula_code_le_guardComponent consumedTerm
      (‘2’ : ValuationTerm) bitBound hconsumedTermCode htwoCode
  have htagFormulaCode := termRowsNativeEqFormula_code_le_guardComponent
    tagTerm (‘1’ : ValuationTerm) bitBound htagTermCode honeCode
  have hcomparisonFormulaCode :=
    termRowsNativeLtFormula_code_le_guardComponent argumentTerm
      witnessCountTerm bitBound hargumentTermCode hwitnessCountTermCode
  have hcode := termRowsThreeGuardFormula_code_le consumedFormula tagFormula
    comparisonFormula bitBound hconsumedFormulaCode htagFormulaCode
    hcomparisonFormulaCode
  have hfixed := termRowsThreeGuardEnvelope_le_fixed
    termRowsComparisonGuardZeroValuation consumedFormula tagFormula
    comparisonFormula
    (termRowsNativeEqStructuralEnvelope consumedTerm (‘2’ : ValuationTerm))
    (termRowsNativeEqStructuralEnvelope tagTerm (‘1’ : ValuationTerm))
    (termRowsNativeLtStructuralEnvelope argumentTerm witnessCountTerm)
    bitBound hconsumedResource htagResource hcomparisonResource hclosed hcode
  simpa only [capturedGuardPayloadEnvelope, consumedTerm, tagTerm, argumentTerm,
    witnessCountTerm, consumedFormula, tagFormula, comparisonFormula,
    termRowsComparisonGuardZeroValuation] using hfixed

theorem capturedGuardCertificate_structuralPayloadBound_le_fixed
    (consumedCount tag argument witnessCount bitBound : Nat)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ argument < witnessCount)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (htagSize : Nat.size tag <= bitBound)
    (hargumentSize : Nat.size argument <= bitBound)
    (hwitnessCountSize : Nat.size witnessCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (capturedGuardCertificate consumedCount tag argument witnessCount
          hguard) <=
      termRowsThreeGuardFixedPayloadPolynomial bitBound :=
  (capturedGuardCertificate_structuralPayloadBound_le_transparent
    consumedCount tag argument witnessCount hguard).trans
      (capturedGuardPayloadEnvelope_le_fixed consumedCount tag argument
        witnessCount bitBound hconsumedSize htagSize hargumentSize
        hwitnessCountSize)

theorem residualGuardPayloadEnvelope_le_fixed
    (consumedCount tag argument witnessCount bitBound : Nat)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (htagSize : Nat.size tag <= bitBound)
    (hargumentSize : Nat.size argument <= bitBound)
    (hwitnessCountSize : Nat.size witnessCount <= bitBound) :
    residualGuardPayloadEnvelope consumedCount tag argument witnessCount <=
      termRowsThreeGuardFixedPayloadPolynomial bitBound := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let argumentTerm := shortBinaryNumeralTerm argument
  let witnessCountTerm := shortBinaryNumeralTerm witnessCount
  let consumedFormula := nativeEqFormula consumedTerm (‘2’ : ValuationTerm)
  let tagFormula := nativeEqFormula tagTerm (‘1’ : ValuationTerm)
  let comparisonFormula := nativeLeFormula witnessCountTerm argumentTerm
  have hconsumedTermClosed : consumedTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htagTermClosed : tagTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hargumentTermClosed : argumentTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hwitnessCountTermClosed : witnessCountTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have honeClosed : (‘1’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl))
  have htwoClosed : (‘2’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘2’ : ValuationTerm)
      (Or.inr (Or.inr (Or.inl rfl)))
  have hconsumedTermCode := termRowsShortNumeralCode_le consumedCount bitBound
    hconsumedSize
  have htagTermCode := termRowsShortNumeralCode_le tag bitBound htagSize
  have hargumentTermCode := termRowsShortNumeralCode_le argument bitBound
    hargumentSize
  have hwitnessCountTermCode := termRowsShortNumeralCode_le witnessCount
    bitBound hwitnessCountSize
  have honeCode := termRowsLiteralCode_le (‘1’ : ValuationTerm) bitBound
    (Or.inr (Or.inl rfl))
  have htwoCode := termRowsLiteralCode_le (‘2’ : ValuationTerm) bitBound
    (Or.inr (Or.inr (Or.inl rfl)))
  have hconsumedResource := termRowsNativeEqStructuralEnvelope_le_guardLeaf
    consumedTerm (‘2’ : ValuationTerm) bitBound hconsumedTermClosed htwoClosed
    hconsumedTermCode htwoCode
  have htagResource := termRowsNativeEqStructuralEnvelope_le_guardLeaf
    tagTerm (‘1’ : ValuationTerm) bitBound htagTermClosed honeClosed
    htagTermCode honeCode
  have hcomparisonResource := termRowsNativeLeStructuralEnvelope_le_guardLeaf
    witnessCountTerm argumentTerm bitBound hwitnessCountTermClosed
    hargumentTermClosed hwitnessCountTermCode hargumentTermCode
  have hconsumedFormulaClosed := termRowsNativeEqFormula_closed consumedTerm
    (‘2’ : ValuationTerm) hconsumedTermClosed htwoClosed
  have htagFormulaClosed := termRowsNativeEqFormula_closed tagTerm
    (‘1’ : ValuationTerm) htagTermClosed honeClosed
  have hcomparisonFormulaClosed := termRowsNativeLeFormula_closed
    witnessCountTerm argumentTerm hwitnessCountTermClosed hargumentTermClosed
  have hclosed := termRowsThreeGuardFormula_closed consumedFormula tagFormula
    comparisonFormula hconsumedFormulaClosed htagFormulaClosed
    hcomparisonFormulaClosed
  have hconsumedFormulaCode :=
    termRowsNativeEqFormula_code_le_guardComponent consumedTerm
      (‘2’ : ValuationTerm) bitBound hconsumedTermCode htwoCode
  have htagFormulaCode := termRowsNativeEqFormula_code_le_guardComponent
    tagTerm (‘1’ : ValuationTerm) bitBound htagTermCode honeCode
  have hcomparisonFormulaCode :=
    termRowsNativeLeFormula_code_le_guardComponent witnessCountTerm
      argumentTerm bitBound hwitnessCountTermCode hargumentTermCode
  have hcode := termRowsThreeGuardFormula_code_le consumedFormula tagFormula
    comparisonFormula bitBound hconsumedFormulaCode htagFormulaCode
    hcomparisonFormulaCode
  have hfixed := termRowsThreeGuardEnvelope_le_fixed
    termRowsComparisonGuardZeroValuation consumedFormula tagFormula
    comparisonFormula
    (termRowsNativeEqStructuralEnvelope consumedTerm (‘2’ : ValuationTerm))
    (termRowsNativeEqStructuralEnvelope tagTerm (‘1’ : ValuationTerm))
    (termRowsNativeLeStructuralEnvelope witnessCountTerm argumentTerm)
    bitBound hconsumedResource htagResource hcomparisonResource hclosed hcode
  simpa only [residualGuardPayloadEnvelope, consumedTerm, tagTerm, argumentTerm,
    witnessCountTerm, consumedFormula, tagFormula, comparisonFormula,
    termRowsComparisonGuardZeroValuation] using hfixed

theorem residualGuardCertificate_structuralPayloadBound_le_fixed
    (consumedCount tag argument witnessCount bitBound : Nat)
    (hguard : consumedCount = 2 ∧ tag = 1 ∧ witnessCount <= argument)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (htagSize : Nat.size tag <= bitBound)
    (hargumentSize : Nat.size argument <= bitBound)
    (hwitnessCountSize : Nat.size witnessCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (residualGuardCertificate consumedCount tag argument witnessCount
          hguard) <=
      termRowsThreeGuardFixedPayloadPolynomial bitBound :=
  (residualGuardCertificate_structuralPayloadBound_le_transparent
    consumedCount tag argument witnessCount hguard).trans
      (residualGuardPayloadEnvelope_le_fixed consumedCount tag argument
        witnessCount bitBound hconsumedSize htagSize hargumentSize
        hwitnessCountSize)

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds
