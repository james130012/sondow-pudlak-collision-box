import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedCore
import integration.FoundationCompactNumericListedDirectNatListAppendTwoValuesFullyFixedBounds

/-! # Fully fixed append-[1, argument+1] certificate for term-output rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 140000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAppendShiftedFullyFixedBounds

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

private abbrev shiftedRowsValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsShiftedBitBound (bitBound : Nat) : Nat := bitBound + 1

private theorem shiftedRowsValue_size_le (value : Nat) :
    Nat.size (value + 1) <= Nat.size value + 1 := by
  rw [Nat.size_le]
  have hvalue : value + 1 <= 2 ^ Nat.size value :=
    Nat.succ_le_iff.mpr (Nat.lt_size_self value)
  exact hvalue.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat))
      (Nat.lt_succ_self (Nat.size value)))

theorem termRowsAppendTwoShiftedCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hrows : CompactFormulaTransformOutputTwoValuesRows tokenTable width
      tokenCount current next 1 (argument + 1))
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnextOutputCountBound : next.outputCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    let shiftedTerm := nativeAddTerm (shortBinaryNumeralTerm argument)
      (‘1’ : ValuationTerm)
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectNatListAppendTwoValuesExplicitHybridCertificate.compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parserFinish current.finish
          current.outputCount next.parserFinish next.finish next.outputBoundary
          next.outputCount 1 (argument + 1) (‘1’ : ValuationTerm) shiftedTerm
          (termValue_arithmeticOne shiftedRowsValuation)
          (by
            simp [shiftedTerm, nativeAddTerm, termValue_arithmeticAdd,
              termValue_arithmeticOne, termValue_shortBinaryNumeralTerm])
          hrows) <=
      appendTwoFullyFixedPayloadPolynomial numericBound
        (termRowsShiftedBitBound bitBound) := by
  let shiftedTerm := nativeAddTerm (shortBinaryNumeralTerm argument)
    (‘1’ : ValuationTerm)
  let branchBitBound := termRowsShiftedBitBound bitBound
  have henvironmentLarge : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <=
        branchBitBound := by
    intro coordinate
    exact (henvironmentSize coordinate).trans (by
      unfold branchBitBound termRowsShiftedBitBound
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
  have hargumentSize : Nat.size argument <= branchBitBound := by
    simpa [compactFormulaTransformTermOutputRowsEnvironment] using
      henvironmentLarge (28 : Fin 33)
  have honeSize : Nat.size 1 <= branchBitBound := by
    unfold branchBitBound termRowsShiftedBitBound
    simp
  have hshiftedSize : Nat.size (argument + 1) <= branchBitBound :=
    (shiftedRowsValue_size_le argument).trans (by
      have hraw := henvironmentSize (28 : Fin 33)
      simpa [compactFormulaTransformTermOutputRowsEnvironment,
        branchBitBound, termRowsShiftedBitBound] using Nat.add_le_add_right hraw 1)
  have hnumericSizeLarge : Nat.size numericBound <= branchBitBound :=
    hnumericSize.trans (by
      unfold branchBitBound termRowsShiftedBitBound
      omega)
  have honeClosed : (‘1’ : ValuationTerm).freeVariables = ∅ :=
    termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl))
  have hshiftedClosed : shiftedTerm.freeVariables = ∅ := by
    simpa only [shiftedTerm] using failureAddArgumentOne_closed argument
  have honeCode : (binaryTermCode (‘1’ : ValuationTerm)).length <=
      appendTwoExactTermCodePolynomial branchBitBound := by
    unfold appendTwoExactTermCodePolynomial
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds.appendSourcePrefixCompositeTermCodePolynomial
    omega
  have hshiftedCode : (binaryTermCode shiftedTerm).length <=
      appendTwoExactTermCodePolynomial branchBitBound := by
    have hargumentCode := binaryNumeralTerm_code_length_le_envelope argument
      branchBitBound hargumentSize
    have hadd := paAddTerm_code_length_le
      (shortBinaryNumeralTerm argument) (‘1’ : ValuationTerm)
    change (binaryTermCode
      (paAddTerm (shortBinaryNumeralTerm argument)
        (‘1’ : ValuationTerm))).length <= _
    unfold appendTwoExactTermCodePolynomial
      FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds.appendSourcePrefixCompositeTermCodePolynomial
    omega
  exact
    compactAdditiveNatListAppendTwoValuesAtValuationValuesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.parserFinish current.finish
      current.outputCount next.parserFinish next.finish next.outputBoundary
      next.outputCount 1 (argument + 1) numericBound branchBitBound
      (‘1’ : ValuationTerm) shiftedTerm
      (termValue_arithmeticOne shiftedRowsValuation)
      (by
        simp [shiftedTerm, nativeAddTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne, termValue_shortBinaryNumeralTerm])
      honeClosed hshiftedClosed hrows htableSize hwidthSize htokenCountSize
      hcurrentParserFinishSize hcurrentFinishSize hcurrentOutputCountSize
      hnextParserFinishSize hnextFinishSize hnextOutputBoundarySize
      hnextOutputCountSize honeSize hshiftedSize honeCode hshiftedCode
      hwidthBound htokenCountBound hnextOutputCountBound hnumericSizeLarge

#print axioms
  termRowsAppendTwoShiftedCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAppendShiftedFullyFixedBounds
