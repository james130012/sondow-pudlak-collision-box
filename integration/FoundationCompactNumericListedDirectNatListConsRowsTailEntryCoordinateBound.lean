import integration.FoundationCompactNumericListedDirectNatListConsRowsTailEntryFixedBounds

/-! # Public coordinate ceiling for a natural-list cons tail entry -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 320000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailEntryCoordinateBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailEntryFixedBounds

theorem natListConsRowsTailEntryCoordinateScale_le_public
    (valuation : Nat -> Nat)
    (boundary tokenCount value numericBound bitBound : Nat)
    (indexTerm : ValuationTerm)
    (htokenCount : tokenCount <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (hboundarySize : Nat.size boundary <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      natListConsRowsTailOpenIndexTermCodeBound) :
    fixedWidthOpenIndexAtomicCoordinateScale valuation
        (shortBinaryNumeralTerm boundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm value) <=
      natListConsRowsTailEntryFixedScale numericBound bitBound := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm boundary
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let valueTerm := shortBinaryNumeralTerm value
  let productTerm := fixedWidthIndexWidthTerm widthTerm indexTerm
  let coordinate := fixedWidthOpenIndexShortNumeralAtTermCoordinate
    numericBound bitBound natListConsRowsTailOpenIndexTermCodeBound
  have htableCode : (binaryTermCode tableTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope boundary bitBound hboundarySize
  have hwidthCode : (binaryTermCode widthTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
      htokenCountSize
  have hvalueCode : (binaryTermCode valueTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
  have hproductCode :
      (binaryTermCode productTerm).length <=
        natListConsRowsTailOpenIndexTermCodeBound + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul := by
    have hraw := paMulTerm_code_length_le indexTerm widthTerm
    simpa only [productTerm, fixedWidthIndexWidthTerm] using
      hraw.trans (by omega)
  have hshiftedProductCode :
      (binaryTermCode (Rew.shift productTerm)).length <=
        2 * (natListConsRowsTailOpenIndexTermCodeBound + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) :=
    (binaryTermCode_shift_length_le productTerm).trans
      (Nat.mul_le_mul_left 2 hproductCode)
  have hleftIndexCodeRaw := paAddTerm_code_length_le
    (Rew.shift productTerm) (&0 : ValuationTerm)
  have hleftIndexCode :
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
      2 * (natListConsRowsTailOpenIndexTermCodeBound + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) +
        (binaryTermCode (&0 : ValuationTerm)).length +
          binaryFunctionTermCodeOverhead Language.Add.add := by
    unfold fixedWidthLeftBitIndexTerm
    simpa only [productTerm] using hleftIndexCodeRaw.trans (by omega)
  have hleftValueCode :
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <=
        2 * numeralCode := by
    unfold fixedWidthLeftBitValueTerm
    exact (binaryTermCode_shift_length_le tableTerm).trans
      (Nat.mul_le_mul_left 2 htableCode)
  have hrightValueCode :
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <=
        2 * numeralCode := by
    unfold fixedWidthRightBitValueTerm
    exact (binaryTermCode_shift_length_le valueTerm).trans
      (Nat.mul_le_mul_left 2 hvalueCode)
  have htermCodes :
      numeralCode <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            natListConsRowsTailOpenIndexTermCodeBound ∧
      natListConsRowsTailOpenIndexTermCodeBound <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            natListConsRowsTailOpenIndexTermCodeBound ∧
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            natListConsRowsTailOpenIndexTermCodeBound ∧
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            natListConsRowsTailOpenIndexTermCodeBound ∧
      (binaryTermCode fixedWidthRightBitIndexTerm).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            natListConsRowsTailOpenIndexTermCodeBound ∧
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <=
          fixedWidthOpenIndexShortNumeralAtTermCodeCeiling bitBound
            natListConsRowsTailOpenIndexTermCodeBound := by
    unfold fixedWidthOpenIndexShortNumeralAtTermCodeCeiling
    dsimp only [numeralCode]
    constructor
    · omega
    constructor
    · omega
    constructor
    · exact hleftIndexCode.trans (by omega)
    constructor
    · exact hleftValueCode.trans (by omega)
    constructor
    · omega
    · exact hrightValueCode.trans (by omega)
  unfold natListConsRowsTailEntryFixedScale
  apply fixedWidthOpenIndexAtomicCoordinateScale_le_uniformCeiling valuation
    tableTerm widthTerm indexTerm valueTerm coordinate
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      htokenCount.trans (by
        unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
        omega)
  · exact hindexValue.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · exact hvaluation.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · simpa only [tableTerm, termValue_shortBinaryNumeralTerm] using
      hboundarySize.trans (by
        unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
        omega)
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      htokenCountSize.trans (by
        unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
        omega)
  · exact hindexSize.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · simpa only [valueTerm, termValue_shortBinaryNumeralTerm] using
      hvalueSize.trans (by
        unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
        omega)
  · exact htermCodes.2.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · exact htermCodes.2.2.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
    exact htermCodes.2.2.2.2.1.trans (by omega)
  · exact htermCodes.2.2.2.2.2.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega)
  · exact htableCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega))
  · exact hwidthCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega))
  · exact hindexCode.trans (htermCodes.2.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega))
  · exact hvalueCode.trans (htermCodes.1.trans (by
      unfold coordinate fixedWidthOpenIndexShortNumeralAtTermCoordinate
      omega))

#print axioms natListConsRowsTailEntryCoordinateScale_le_public

theorem natListConsRowsTailEntryPayload_le_fixed
    (valuation : Nat -> Nat)
    (boundary tokenCount value numericBound bitBound : Nat)
    (indexTerm : ValuationTerm)
    (htokenCount : tokenCount <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (hboundarySize : Nat.size boundary <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      natListConsRowsTailOpenIndexTermCodeBound)
    (hindexVariables : indexTerm.freeVariables ⊆ {0}) :
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm boundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm value) <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound := by
  have hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation
          (shortBinaryNumeralTerm boundary)
          (shortBinaryNumeralTerm tokenCount) indexTerm
          (shortBinaryNumeralTerm value) <=
        natListConsRowsTailEntryFixedScale numericBound bitBound :=
    natListConsRowsTailEntryCoordinateScale_le_public valuation boundary
      tokenCount value numericBound bitBound indexTerm htokenCount hindexValue
      hvaluation hboundarySize htokenCountSize hindexSize hvalueSize hindexCode
  unfold natListConsRowsTailEntryFixedPayloadPolynomial
  exact
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      valuation (shortBinaryNumeralTerm boundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
          (shortBinaryNumeralTerm value)
            (natListConsRowsTailEntryFixedScale numericBound bitBound) hscale
      (shortBinaryNumeralTerm_freeVariables_eq_empty boundary)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      hindexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty value)

#print axioms natListConsRowsTailEntryPayload_le_fixed

end FoundationCompactNumericListedDirectNatListConsRowsTailEntryCoordinateBound
