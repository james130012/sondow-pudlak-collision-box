import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureDisjunctionFixedCore

/-! # Double-failure fixed resource for term-output rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

theorem doubleFailurePublicFinitePayloadEnvelope_le_fullyFixed
    (consumedCount tag bitBound : Nat)
    (hconsumed : Nat.size consumedCount <= bitBound)
    (htag : Nat.size tag <= bitBound) :
    doubleFailurePublicFinitePayloadEnvelope consumedCount tag <=
      termOutputDoubleFailureFixedPayloadPolynomial bitBound := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let two : ValuationTerm := ‘2’
  let one : ValuationTerm := ‘1’
  let consumedFormula := nativeNeFormula consumedTerm two
  let tagFormula := nativeNeFormula tagTerm one
  have hconsumedTermClosed : consumedTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htagTermClosed : tagTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htwoClosed : two.freeVariables = ∅ :=
    failureLiteral_closed two (Or.inr (Or.inr rfl))
  have honeClosed : one.freeVariables = ∅ :=
    failureLiteral_closed one (Or.inr (Or.inl rfl))
  have hconsumedTermCode := failureShortNumeralCode_le consumedCount bitBound
    hconsumed
  have htagTermCode := failureShortNumeralCode_le tag bitBound htag
  have htwoCode := failureLiteralCode_le two bitBound (Or.inr (Or.inr rfl))
  have honeCode := failureLiteralCode_le one bitBound (Or.inr (Or.inl rfl))
  have hconsumedAtom := termRowsNativeNeStructuralEnvelope_le_fixed
    consumedTerm two bitBound hconsumedTermClosed htwoClosed hconsumedTermCode
    htwoCode
  have htagAtom := termRowsNativeNeStructuralEnvelope_le_fixed
    tagTerm one bitBound htagTermClosed honeClosed htagTermCode honeCode
  have hconsumedFormulaClosed := failureNativeNeFormula_closed consumedTerm two
    hconsumedTermClosed htwoClosed
  have htagFormulaClosed := failureNativeNeFormula_closed tagTerm one
    htagTermClosed honeClosed
  have htargetClosed := failureDisjunction_closed consumedFormula tagFormula
    hconsumedFormulaClosed htagFormulaClosed
  have hconsumedFormulaAtomCode := failureNativeNeFormula_code_le consumedTerm
    two bitBound hconsumedTermCode htwoCode
  have htagFormulaAtomCode := failureNativeNeFormula_code_le tagTerm one bitBound
    htagTermCode honeCode
  have hconsumedFormulaCode : (binaryFormulaCode consumedFormula).length <=
      termOutputFailureFormulaCodePolynomial bitBound :=
    hconsumedFormulaAtomCode.trans (by
      unfold termOutputFailureFormulaCodePolynomial
      omega)
  have htagFormulaCode : (binaryFormulaCode tagFormula).length <=
      termOutputFailureFormulaCodePolynomial bitBound :=
    htagFormulaAtomCode.trans (by
      unfold termOutputFailureFormulaCodePolynomial
      omega)
  have htargetInnerCode := failureInnerDisjunction_code_le consumedFormula
    tagFormula bitBound hconsumedFormulaAtomCode htagFormulaAtomCode
  have htargetCode : (binaryFormulaCode (consumedFormula ⋎ tagFormula)).length <=
      termOutputFailureFormulaCodePolynomial bitBound :=
    htargetInnerCode.trans (by
      unfold termOutputFailureFormulaCodePolynomial
      omega)
  have hleft := failureDisjunctionPathLeft_le_fixed termRowsZeroValuation
    consumedFormula tagFormula
    (termRowsNativeNeStructuralEnvelope consumedTerm two) bitBound htargetClosed
    hconsumedFormulaCode htagFormulaCode htargetCode hconsumedAtom
  have hright := failureDisjunctionPathRight_le_fixed termRowsZeroValuation
    consumedFormula tagFormula
    (termRowsNativeNeStructuralEnvelope tagTerm one) bitBound htargetClosed
    hconsumedFormulaCode htagFormulaCode htargetCode htagAtom
  unfold doubleFailurePublicFinitePayloadEnvelope
    termOutputDoubleFailureFixedPayloadPolynomial
  dsimp only [consumedTerm, tagTerm, two, one, consumedFormula, tagFormula]
    at hleft hright ⊢
  omega

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
