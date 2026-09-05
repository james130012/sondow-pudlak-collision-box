import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedCore
import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds

/-! # Fully fixed append-[0, binderArity+argument] certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 160000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAppendCapturedFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds

private abbrev capturedRowsValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsAdditiveBitBound (bitBound : Nat) : Nat :=
  bitBound + bitBound + 1

private theorem capturedRowsValue_size_le (left right : Nat) :
    Nat.size (left + right) <= Nat.size left + Nat.size right + 1 := by
  rw [Nat.size_le]
  have hleft : left < 2 ^ Nat.size left := Nat.lt_size_self left
  have hright : right < 2 ^ Nat.size right := Nat.lt_size_self right
  have hleftPower : 2 ^ Nat.size left <=
      2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_right (Nat.size left) (Nat.size right))
  have hrightPower : 2 ^ Nat.size right <=
      2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_left (Nat.size right) (Nat.size left))
  calc
    left + right < 2 ^ Nat.size left + 2 ^ Nat.size right :=
      Nat.add_lt_add hleft hright
    _ <= 2 ^ (Nat.size left + Nat.size right) +
        2 ^ (Nat.size left + Nat.size right) :=
      Nat.add_le_add hleftPower hrightPower
    _ = 2 ^ (Nat.size left + Nat.size right + 1) := by
      rw [pow_succ]
      omega

theorem termRowsAppendTwoCapturedCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 0 (binderArity + argument))
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnextOutputCountBound : next.outputCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    let capturedTerm := nativeAddTerm (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm argument)
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 0 (binderArity + argument) (‘0’ : ValuationTerm)
          capturedTerm (termValue_arithmeticZero capturedRowsValuation)
          (by
            simp [capturedTerm, nativeAddTerm, termValue_arithmeticAdd,
              termValue_shortBinaryNumeralTerm]) hrows) <=
      appendTwoFullyFixedPayloadPolynomial numericBound
        (termRowsAdditiveBitBound bitBound) := by
  let capturedTerm := nativeAddTerm (shortBinaryNumeralTerm binderArity)
    (shortBinaryNumeralTerm argument)
  let branchBitBound := termRowsAdditiveBitBound bitBound
  have henvironmentLarge : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <=
        branchBitBound := by
    intro coordinate
    exact (henvironmentSize coordinate).trans (by
      unfold branchBitBound termRowsAdditiveBitBound
      omega)
  have htableSize : Nat.size tokenTable <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (0 : Fin 33)
  have hwidthSize : Nat.size width <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (1 : Fin 33)
  have htokenCountSize : Nat.size tokenCount <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (2 : Fin 33)
  have hcurrentFinishSize : Nat.size current.finish <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (4 : Fin 33)
  have hcurrentParserFinishSize : Nat.size current.parserFinish <=
      branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (5 : Fin 33)
  have hcurrentOutputCountSize : Nat.size current.outputCount <=
      branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (13 : Fin 33)
  have hnextFinishSize : Nat.size next.finish <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (15 : Fin 33)
  have hnextParserFinishSize : Nat.size next.parserFinish <=
      branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (16 : Fin 33)
  have hnextOutputBoundarySize : Nat.size next.outputBoundary <=
      branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (23 : Fin 33)
  have hnextOutputCountSize : Nat.size next.outputCount <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (24 : Fin 33)
  have hbinderAritySize : Nat.size binderArity <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (26 : Fin 33)
  have hargumentSize : Nat.size argument <= bitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentSize (28 : Fin 33)
  have hzeroSize : Nat.size 0 <= branchBitBound := by simp
  have hcapturedSize : Nat.size (binderArity + argument) <= branchBitBound :=
    (capturedRowsValue_size_le binderArity argument).trans (by
      unfold branchBitBound termRowsAdditiveBitBound
      omega)
  have hnumericSizeLarge : Nat.size numericBound <= branchBitBound :=
    hnumericSize.trans (by
      unfold branchBitBound termRowsAdditiveBitBound
      omega)
  have hzeroClosed : (‘0’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘0’ : ValuationTerm) (Or.inl rfl)
  have hcapturedClosed : capturedTerm.freeVariables = ∅ := by
    simpa only [capturedTerm] using
      termRowsAddShortNumerals_closed binderArity argument
  have hzeroCode : (binaryTermCode (‘0’ : ValuationTerm)).length <=
      appendTwoExactTermCodePolynomial branchBitBound :=
    appendTwoShortNumeralCode_le 0 branchBitBound (by simp)
  have hcapturedCode : (binaryTermCode capturedTerm).length <=
      appendTwoExactTermCodePolynomial branchBitBound := by
    have hleftCode := binaryNumeralTerm_code_length_le_envelope binderArity
      branchBitBound (hbinderAritySize.trans (by
        unfold branchBitBound termRowsAdditiveBitBound
        omega))
    have hrightCode := binaryNumeralTerm_code_length_le_envelope argument
      branchBitBound (hargumentSize.trans (by
        unfold branchBitBound termRowsAdditiveBitBound
        omega))
    have hadd := paAddTerm_code_length_le
      (shortBinaryNumeralTerm binderArity) (shortBinaryNumeralTerm argument)
    change (binaryTermCode
      (paAddTerm (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm argument))).length <= _
    unfold appendTwoExactTermCodePolynomial
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds.appendSourcePrefixCompositeTermCodePolynomial
    omega
  exact
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 0 (binderArity + argument) numericBound branchBitBound
      (‘0’ : ValuationTerm) capturedTerm
      (termValue_arithmeticZero capturedRowsValuation)
      (by
        simp [capturedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_shortBinaryNumeralTerm])
      hzeroClosed hcapturedClosed hrows htableSize hwidthSize htokenCountSize
      hcurrentParserFinishSize hcurrentFinishSize hcurrentOutputCountSize
      hnextParserFinishSize hnextFinishSize hnextOutputBoundarySize
      hnextOutputCountSize hzeroSize hcapturedSize hzeroCode hcapturedCode
      hwidthBound htokenCountBound hnextOutputCountBound hnumericSizeLarge

#print axioms
  termRowsAppendTwoCapturedCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAppendCapturedFullyFixedBounds
