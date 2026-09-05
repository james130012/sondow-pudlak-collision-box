import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds

/-! # Triple-failure fixed resource for term-output rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureTripleFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds

theorem tripleFailurePublicFinitePayloadEnvelope_le_fullyFixed
    (consumedCount tag argument binderArity bitBound : Nat)
    (hconsumed : Nat.size consumedCount <= bitBound)
    (htag : Nat.size tag <= bitBound)
    (hargument : Nat.size argument <= bitBound)
    (hbinderArity : Nat.size binderArity <= bitBound) :
    tripleFailurePublicFinitePayloadEnvelope consumedCount tag argument
        binderArity <=
      termOutputTripleFailureFixedPayloadPolynomial bitBound := by
  let consumedTerm := shortBinaryNumeralTerm consumedCount
  let tagTerm := shortBinaryNumeralTerm tag
  let argumentTerm := shortBinaryNumeralTerm argument
  let binderArityTerm := shortBinaryNumeralTerm binderArity
  let two : ValuationTerm := ‘2’
  let zero : ValuationTerm := ‘0’
  let one : ValuationTerm := ‘1’
  let argumentAddOne := nativeAddTerm argumentTerm one
  let consumedFormula := nativeNeFormula consumedTerm two
  let tagFormula := nativeNeFormula tagTerm zero
  let argumentFormula := nativeNeFormula argumentAddOne binderArityTerm
  let innerFormula := tagFormula ⋎ argumentFormula
  have hconsumedTermClosed : consumedTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htagTermClosed : tagTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hbinderTermClosed : binderArityTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have htwoClosed : two.freeVariables = ∅ :=
    failureLiteral_closed two (Or.inr (Or.inr rfl))
  have hzeroClosed : zero.freeVariables = ∅ :=
    failureLiteral_closed zero (Or.inl rfl)
  have haddClosed : argumentAddOne.freeVariables = ∅ := by
    simpa only [argumentAddOne, argumentTerm, one] using
      failureAddArgumentOne_closed argument
  have hconsumedTermCode := failureShortNumeralCode_le consumedCount bitBound
    hconsumed
  have htagTermCode := failureShortNumeralCode_le tag bitBound htag
  have hbinderTermCode := failureShortNumeralCode_le binderArity bitBound
    hbinderArity
  have htwoCode := failureLiteralCode_le two bitBound (Or.inr (Or.inr rfl))
  have hzeroCode := failureLiteralCode_le zero bitBound (Or.inl rfl)
  have haddCode : (binaryTermCode argumentAddOne).length <=
      termOutputFailureTermCodePolynomial bitBound := by
    simpa only [argumentAddOne, argumentTerm, one] using
      failureAddArgumentOneCode_le argument bitBound hargument
  have hconsumedAtom := termRowsNativeNeStructuralEnvelope_le_fixed
    consumedTerm two bitBound hconsumedTermClosed htwoClosed hconsumedTermCode
    htwoCode
  have htagAtom := termRowsNativeNeStructuralEnvelope_le_fixed tagTerm zero
    bitBound htagTermClosed hzeroClosed htagTermCode hzeroCode
  have hargumentAtom := termRowsNativeNeStructuralEnvelope_le_fixed
    argumentAddOne binderArityTerm bitBound haddClosed hbinderTermClosed
    haddCode hbinderTermCode
  have hconsumedFormulaClosed := failureNativeNeFormula_closed consumedTerm two
    hconsumedTermClosed htwoClosed
  have htagFormulaClosed := failureNativeNeFormula_closed tagTerm zero
    htagTermClosed hzeroClosed
  have hargumentFormulaClosed := failureNativeNeFormula_closed argumentAddOne
    binderArityTerm haddClosed hbinderTermClosed
  have hinnerClosed := failureDisjunction_closed tagFormula argumentFormula
    htagFormulaClosed hargumentFormulaClosed
  have houterClosed := failureDisjunction_closed consumedFormula innerFormula
    hconsumedFormulaClosed hinnerClosed
  have hconsumedAtomCode := failureNativeNeFormula_code_le consumedTerm two
    bitBound hconsumedTermCode htwoCode
  have htagAtomCode := failureNativeNeFormula_code_le tagTerm zero bitBound
    htagTermCode hzeroCode
  have hargumentAtomCode := failureNativeNeFormula_code_le argumentAddOne
    binderArityTerm bitBound haddCode hbinderTermCode
  have hconsumedFormulaCode : (binaryFormulaCode consumedFormula).length <=
      termOutputFailureFormulaCodePolynomial bitBound :=
    hconsumedAtomCode.trans (by
      unfold termOutputFailureFormulaCodePolynomial
      omega)
  have htagFormulaCode : (binaryFormulaCode tagFormula).length <=
      termOutputFailureFormulaCodePolynomial bitBound :=
    htagAtomCode.trans (by
      unfold termOutputFailureFormulaCodePolynomial
      omega)
  have hargumentFormulaCode : (binaryFormulaCode argumentFormula).length <=
      termOutputFailureFormulaCodePolynomial bitBound :=
    hargumentAtomCode.trans (by
      unfold termOutputFailureFormulaCodePolynomial
      omega)
  have hinnerCodeRaw := failureInnerDisjunction_code_le tagFormula
    argumentFormula bitBound htagAtomCode hargumentAtomCode
  have hinnerCode : (binaryFormulaCode innerFormula).length <=
      termOutputFailureFormulaCodePolynomial bitBound :=
    hinnerCodeRaw.trans (by
      unfold termOutputFailureFormulaCodePolynomial
      omega)
  have houterCode := failureOuterDisjunction_code_le consumedFormula
    innerFormula bitBound hconsumedAtomCode hinnerCodeRaw
  have hconsumedPath := failureDisjunctionPathLeft_le_fixed
    termRowsZeroValuation consumedFormula
    innerFormula (termRowsNativeNeStructuralEnvelope consumedTerm two) bitBound
    houterClosed hconsumedFormulaCode hinnerCode houterCode hconsumedAtom
  have htagInner := failureDisjunctionPathLeft_le_fixed termRowsZeroValuation
    tagFormula
    argumentFormula (termRowsNativeNeStructuralEnvelope tagTerm zero) bitBound
    hinnerClosed htagFormulaCode hargumentFormulaCode hinnerCode htagAtom
  have hargumentInner := failureDisjunctionPathRight_le_fixed
    termRowsZeroValuation tagFormula
    argumentFormula
    (termRowsNativeNeStructuralEnvelope argumentAddOne binderArityTerm) bitBound
    hinnerClosed htagFormulaCode hargumentFormulaCode hinnerCode hargumentAtom
  have htagOuterRaw := transparentHybridDisjunctionRightPayloadEnvelope_le_general
    termRowsZeroValuation consumedFormula innerFormula
    (termOutputFailurePathPayloadPolynomial bitBound)
    (termOutputFailureFormulaCodePolynomial bitBound)
    (by unfold termOutputFailureFormulaCodePolynomial; omega)
    (by rw [houterClosed]; simp [valuationContext, formulaCodeSum])
    hconsumedFormulaCode hinnerCode houterCode
  have hargumentOuterRaw := htagOuterRaw
  have hpath_le_outer :
      termOutputFailurePathPayloadPolynomial bitBound <=
        hybridDisjunctionGeneralPayloadEnvelope
          (termOutputFailureFormulaCodePolynomial bitBound)
          (termOutputFailurePathPayloadPolynomial bitBound) := by
    unfold hybridDisjunctionGeneralPayloadEnvelope
    omega
  have hconsumedOuter := hconsumedPath.trans hpath_le_outer
  have htagPath :
      transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
          consumedFormula
          innerFormula
          (transparentHybridDisjunctionLeftPayloadEnvelope termRowsZeroValuation
            tagFormula
            argumentFormula
            (termRowsNativeNeStructuralEnvelope tagTerm zero)) <=
        hybridDisjunctionGeneralPayloadEnvelope
          (termOutputFailureFormulaCodePolynomial bitBound)
          (termOutputFailurePathPayloadPolynomial bitBound) := by
    exact (transparentHybridDisjunctionRightPayloadEnvelope_mono
      termRowsZeroValuation consumedFormula innerFormula htagInner).trans
        htagOuterRaw
  have hargumentPath :
      transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
          consumedFormula
          innerFormula
          (transparentHybridDisjunctionRightPayloadEnvelope termRowsZeroValuation
            tagFormula
            argumentFormula
            (termRowsNativeNeStructuralEnvelope argumentAddOne
              binderArityTerm)) <=
        hybridDisjunctionGeneralPayloadEnvelope
          (termOutputFailureFormulaCodePolynomial bitBound)
          (termOutputFailurePathPayloadPolynomial bitBound) := by
    exact (transparentHybridDisjunctionRightPayloadEnvelope_mono
      termRowsZeroValuation consumedFormula innerFormula hargumentInner).trans
        hargumentOuterRaw
  unfold tripleFailurePublicFinitePayloadEnvelope
    termOutputTripleFailureFixedPayloadPolynomial
  dsimp only [consumedTerm, tagTerm, argumentTerm, binderArityTerm, two, zero,
    one, argumentAddOne, consumedFormula, tagFormula, argumentFormula,
    innerFormula] at hconsumedOuter htagPath hargumentPath ⊢
  omega

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureTripleFixedBound
