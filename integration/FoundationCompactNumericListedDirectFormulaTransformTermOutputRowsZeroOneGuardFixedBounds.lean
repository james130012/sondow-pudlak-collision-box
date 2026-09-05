import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardAssemblyFixedCore

/-! # Fully fixed zero-tag and one-tag guards for term-output rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 180000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds

private abbrev termRowsGuardZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

theorem zeroTagGuardPayloadEnvelope_le_fixed
    (consumedCount tag argument binderArity bitBound : Nat)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (htagSize : Nat.size tag <= bitBound)
    (hargumentSize : Nat.size argument <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound) :
    zeroTagGuardPayloadEnvelope consumedCount tag argument binderArity <=
      termRowsThreeGuardFixedPayloadPolynomial bitBound := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let argumentTerm := nativeAddTerm (shortBinaryNumeralTerm argument)
    (‘1’ : ValuationTerm)
  let binderArityTerm := shortBinaryNumeralTerm binderArity
  let consumedFormula := nativeEqFormula consumedTerm (‘2’ : ValuationTerm)
  let tagFormula := nativeEqFormula tagTerm (‘0’ : ValuationTerm)
  let argumentFormula := nativeEqFormula argumentTerm binderArityTerm
  have hconsumedTermClosed : consumedTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htagTermClosed : tagTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hargumentTermClosed : argumentTerm.freeVariables = ∅ := by
    dsimp only [argumentTerm]
    exact failureAddArgumentOne_closed argument
  have hbinderArityTermClosed : binderArityTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hzeroClosed : (‘0’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘0’ : ValuationTerm) (Or.inl rfl)
  have honeClosed : (‘1’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl))
  have htwoClosed : (‘2’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘2’ : ValuationTerm)
      (Or.inr (Or.inr (Or.inl rfl)))
  have hconsumedTermCode := termRowsShortNumeralCode_le consumedCount bitBound
    hconsumedSize
  have htagTermCode := termRowsShortNumeralCode_le tag bitBound htagSize
  have hargumentTermCode := failureAddArgumentOneCode_le argument bitBound
    hargumentSize
  have hbinderArityTermCode := termRowsShortNumeralCode_le binderArity bitBound
    hbinderAritySize
  have hzeroCode := termRowsLiteralCode_le (‘0’ : ValuationTerm) bitBound
    (Or.inl rfl)
  have htwoCode := termRowsLiteralCode_le (‘2’ : ValuationTerm) bitBound
    (Or.inr (Or.inr (Or.inl rfl)))
  have hconsumedResource := termRowsNativeEqStructuralEnvelope_le_guardLeaf
    consumedTerm (‘2’ : ValuationTerm) bitBound hconsumedTermClosed htwoClosed
    hconsumedTermCode htwoCode
  have htagResource := termRowsNativeEqStructuralEnvelope_le_guardLeaf
    tagTerm (‘0’ : ValuationTerm) bitBound htagTermClosed hzeroClosed
    htagTermCode hzeroCode
  have hargumentResource := termRowsNativeEqStructuralEnvelope_le_guardLeaf
    argumentTerm binderArityTerm bitBound hargumentTermClosed
    hbinderArityTermClosed hargumentTermCode hbinderArityTermCode
  have hconsumedFormulaClosed := termRowsNativeEqFormula_closed consumedTerm
    (‘2’ : ValuationTerm) hconsumedTermClosed htwoClosed
  have htagFormulaClosed := termRowsNativeEqFormula_closed tagTerm
    (‘0’ : ValuationTerm) htagTermClosed hzeroClosed
  have hargumentFormulaClosed := termRowsNativeEqFormula_closed argumentTerm
    binderArityTerm hargumentTermClosed hbinderArityTermClosed
  have hclosed := termRowsThreeGuardFormula_closed consumedFormula tagFormula
    argumentFormula hconsumedFormulaClosed htagFormulaClosed
    hargumentFormulaClosed
  have hconsumedFormulaCode :=
    termRowsNativeEqFormula_code_le_guardComponent consumedTerm
      (‘2’ : ValuationTerm) bitBound hconsumedTermCode htwoCode
  have htagFormulaCode := termRowsNativeEqFormula_code_le_guardComponent
    tagTerm (‘0’ : ValuationTerm) bitBound htagTermCode hzeroCode
  have hargumentFormulaCode :=
    termRowsNativeEqFormula_code_le_guardComponent argumentTerm binderArityTerm
      bitBound hargumentTermCode hbinderArityTermCode
  have hcode := termRowsThreeGuardFormula_code_le consumedFormula tagFormula
    argumentFormula bitBound hconsumedFormulaCode htagFormulaCode
    hargumentFormulaCode
  have hfixed := termRowsThreeGuardEnvelope_le_fixed termRowsGuardZeroValuation
    consumedFormula tagFormula argumentFormula
    (termRowsNativeEqStructuralEnvelope consumedTerm (‘2’ : ValuationTerm))
    (termRowsNativeEqStructuralEnvelope tagTerm (‘0’ : ValuationTerm))
    (termRowsNativeEqStructuralEnvelope argumentTerm binderArityTerm)
    bitBound hconsumedResource htagResource hargumentResource hclosed hcode
  simpa only [zeroTagGuardPayloadEnvelope, consumedTerm, tagTerm, argumentTerm,
    binderArityTerm, consumedFormula, tagFormula, argumentFormula,
    termRowsGuardZeroValuation] using hfixed

theorem zeroTagGuardCertificate_structuralPayloadBound_le_fixed
    (consumedCount tag argument binderArity bitBound : Nat)
    (hguard : consumedCount = 2 ∧ tag = 0 ∧
      argument + 1 = binderArity)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (htagSize : Nat.size tag <= bitBound)
    (hargumentSize : Nat.size argument <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (zeroTagGuardCertificate consumedCount tag argument binderArity
          hguard) <=
      termRowsThreeGuardFixedPayloadPolynomial bitBound :=
  (zeroTagGuardCertificate_structuralPayloadBound_le_transparent
    consumedCount tag argument binderArity hguard).trans
      (zeroTagGuardPayloadEnvelope_le_fixed consumedCount tag argument
        binderArity bitBound hconsumedSize htagSize hargumentSize
        hbinderAritySize)

theorem oneTagGuardPayloadEnvelope_le_fixed
    (consumedCount tag bitBound : Nat)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (htagSize : Nat.size tag <= bitBound) :
    oneTagGuardPayloadEnvelope consumedCount tag <=
      termRowsTwoGuardFixedPayloadPolynomial bitBound := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let consumedFormula := nativeEqFormula consumedTerm (‘2’ : ValuationTerm)
  let tagFormula := nativeEqFormula tagTerm (‘1’ : ValuationTerm)
  have hconsumedTermClosed : consumedTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htagTermClosed : tagTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have honeClosed : (‘1’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl))
  have htwoClosed : (‘2’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘2’ : ValuationTerm)
      (Or.inr (Or.inr (Or.inl rfl)))
  have hconsumedTermCode := termRowsShortNumeralCode_le consumedCount bitBound
    hconsumedSize
  have htagTermCode := termRowsShortNumeralCode_le tag bitBound htagSize
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
  have hconsumedFormulaClosed := termRowsNativeEqFormula_closed consumedTerm
    (‘2’ : ValuationTerm) hconsumedTermClosed htwoClosed
  have htagFormulaClosed := termRowsNativeEqFormula_closed tagTerm
    (‘1’ : ValuationTerm) htagTermClosed honeClosed
  have hclosed := termRowsTwoGuardFormula_closed consumedFormula tagFormula
    hconsumedFormulaClosed htagFormulaClosed
  have hconsumedFormulaCode :=
    termRowsNativeEqFormula_code_le_guardComponent consumedTerm
      (‘2’ : ValuationTerm) bitBound hconsumedTermCode htwoCode
  have htagFormulaCode := termRowsNativeEqFormula_code_le_guardComponent
    tagTerm (‘1’ : ValuationTerm) bitBound htagTermCode honeCode
  have hcode := termRowsTwoGuardFormula_code_le consumedFormula tagFormula
    bitBound hconsumedFormulaCode htagFormulaCode
  have hfixed := termRowsTwoGuardEnvelope_le_fixed termRowsGuardZeroValuation
    consumedFormula tagFormula
    (termRowsNativeEqStructuralEnvelope consumedTerm (‘2’ : ValuationTerm))
    (termRowsNativeEqStructuralEnvelope tagTerm (‘1’ : ValuationTerm))
    bitBound hconsumedResource htagResource hclosed hcode
  simpa only [oneTagGuardPayloadEnvelope, consumedTerm, tagTerm,
    consumedFormula, tagFormula, termRowsGuardZeroValuation] using hfixed

theorem oneTagGuardCertificate_structuralPayloadBound_le_fixed
    (consumedCount tag bitBound : Nat)
    (hguard : consumedCount = 2 ∧ tag = 1)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (htagSize : Nat.size tag <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (oneTagGuardCertificate consumedCount tag hguard) <=
      termRowsTwoGuardFixedPayloadPolynomial bitBound :=
  (oneTagGuardCertificate_structuralPayloadBound_le_transparent
    consumedCount tag hguard).trans
      (oneTagGuardPayloadEnvelope_le_fixed consumedCount tag bitBound
        hconsumedSize htagSize)

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds
