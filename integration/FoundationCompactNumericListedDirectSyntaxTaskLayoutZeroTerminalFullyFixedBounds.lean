import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed terminal bound for a zero syntax-task layout

The zero task stores fixed native zero terms for its kind and repeat count,
and a short binary numeral for `binderArity`. The three real token-cell
certificates are charged separately and reassembled in the original
right-associated conjunction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutZeroTerminalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

def zeroTaskLayoutTerminalBitBound (bitBound : Nat) : Nat :=
  bitBound + binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (fixedNumeralTerm 0)).length + 3

def zeroTaskLayoutTerminalFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  3 * additiveTokenCellClosedValueFormulaCodeEnvelope
      (zeroTaskLayoutTerminalBitBound bitBound) +
    2 * (binaryNatCode 4).length + 1

def zeroTaskLayoutTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (zeroTaskLayoutTerminalFormulaCodeEnvelope bitBound)
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (zeroTaskLayoutTerminalBitBound bitBound))
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (zeroTaskLayoutTerminalBitBound bitBound))
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (zeroTaskLayoutTerminalBitBound bitBound))

private theorem binaryNumeralTermCodeEnvelope_ge_bit_zero
    (bitBound : Nat) :
    bitBound <= binaryNumeralTermCodeEnvelope bitBound := by
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hmul := Nat.mul_le_mul_right bitBound hstep
  unfold binaryNumeralTermCodeEnvelope
  omega

private theorem zeroTaskLayout_bit_le (bitBound : Nat) :
    bitBound <= zeroTaskLayoutTerminalBitBound bitBound := by
  unfold zeroTaskLayoutTerminalBitBound
  omega

private theorem fixedNumeralTerm_freeVariables_eq_empty_zero
    (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

@[simp] private theorem termValue_fixedNumeralTerm_zero
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  simp [fixedNumeralTerm, termValue]

private theorem fixedZero_code_le_zeroTerminalEnvelope
    (bitBound : Nat) :
    (binaryTermCode (fixedNumeralTerm 0)).length <=
      binaryNumeralTermCodeEnvelope
        (zeroTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_
    (binaryNumeralTermCodeEnvelope_ge_bit_zero
      (zeroTaskLayoutTerminalBitBound bitBound))
  unfold zeroTaskLayoutTerminalBitBound
  omega

private theorem binderShort_code_le_zeroTerminalEnvelope
    (binderArity bitBound : Nat)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm binderArity)).length <=
      binaryNumeralTermCodeEnvelope
        (zeroTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope binderArity
    (zeroTaskLayoutTerminalBitBound bitBound)
    (hbinderSize.trans (zeroTaskLayout_bit_le bitBound))

private theorem threeFormulaCode_le_zeroTerminalEnvelope
    (formula1 formula2 formula3 : ValuationFormula)
    (bitBound : Nat)
    (hformula1 : (binaryFormulaCode formula1).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (zeroTaskLayoutTerminalBitBound bitBound))
    (hformula2 : (binaryFormulaCode formula2).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (zeroTaskLayoutTerminalBitBound bitBound))
    (hformula3 : (binaryFormulaCode formula3).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (zeroTaskLayoutTerminalBitBound bitBound)) :
    (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
      zeroTaskLayoutTerminalFormulaCodeEnvelope bitBound := by
  have hinner := binaryFormulaCode_and_length_le_local formula2 formula3
  have houter := binaryFormulaCode_and_length_le_local formula1
    (formula2 ⋏ formula3)
  unfold zeroTaskLayoutTerminalFormulaCodeEnvelope
  omega

theorem
    zeroTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount start finish binderArity
      numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (0, binderArity, 0)) :
    let binderStart := Classical.choose hlayout
    let countStart := Classical.choose (Classical.choose_spec hlayout)
    let certificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm start) (fixedNumeralTerm 0)
          (shortBinaryNumeralTerm binderStart) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_fixedNumeralTerm_zero] using
                (Classical.choose_spec
                  (Classical.choose_spec hlayout)).1))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm binderStart)
            (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm countStart) (by
              simpa only [termValue_shortBinaryNumeralTerm] using
                (Classical.choose_spec
                  (Classical.choose_spec hlayout)).2.1))
          (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm countStart)
            (fixedNumeralTerm 0)
            (shortBinaryNumeralTerm finish) (by
              simpa only [termValue_shortBinaryNumeralTerm,
                termValue_fixedNumeralTerm_zero] using
                  (Classical.choose_spec
                    (Classical.choose_spec hlayout)).2.2)))
    hybridFormulaStructuralPayloadBound certificate <=
      zeroTaskLayoutTerminalPayloadEnvelope numericBound bitBound := by
  dsimp only
  let binderStart := Classical.choose hlayout
  have hbinderData := Classical.choose_spec hlayout
  let countStart := Classical.choose hbinderData
  have hcells := Classical.choose_spec hbinderData
  have hkind := hcells.1
  have hbinder := hcells.2.1
  have hrepeat := hcells.2.2
  have hstartLe : start <= tokenCount := Nat.le_of_lt hkind.1
  have hbinderStartLe : binderStart <= tokenCount :=
    Nat.le_of_lt hbinder.1
  have hcountStartLe : countStart <= tokenCount :=
    Nat.le_of_lt hrepeat.1
  have hbit := zeroTaskLayout_bit_le bitBound
  have hbinderStartSize :
      Nat.size binderStart <= zeroTaskLayoutTerminalBitBound bitBound :=
    (Nat.size_le_size hbinderStartLe).trans (htokenCountSize.trans hbit)
  have hcountStartSize :
      Nat.size countStart <= zeroTaskLayoutTerminalBitBound bitBound :=
    (Nat.size_le_size hcountStartLe).trans (htokenCountSize.trans hbit)
  have hkindResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount start binderStart numericBound
      (zeroTaskLayoutTerminalBitBound bitBound) (fixedNumeralTerm 0)
      hwidthValue (hstartLe.trans htokenCountValue)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hstartSize.trans hbit) (by
        rw [termValue_fixedNumeralTerm_zero]
        exact (by decide : Nat.size 0 <= 2) |>.trans (by
          unfold zeroTaskLayoutTerminalBitBound
          omega))
      hbinderStartSize (fixedZero_code_le_zeroTerminalEnvelope bitBound)
      (fixedNumeralTerm_freeVariables_eq_empty_zero 0) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_fixedNumeralTerm_zero] using hkind)
  have hbinderResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount binderStart countStart numericBound
      (zeroTaskLayoutTerminalBitBound bitBound)
      (shortBinaryNumeralTerm binderArity) hwidthValue
      (hbinderStartLe.trans htokenCountValue) (htableSize.trans hbit)
      (hwidthSize.trans hbit) (htokenCountSize.trans hbit)
      hbinderStartSize (by
        simpa only [termValue_shortBinaryNumeralTerm] using
          hbinderSize.trans hbit) hcountStartSize
      (binderShort_code_le_zeroTerminalEnvelope binderArity bitBound
        hbinderSize)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hbinder)
  have hrepeatResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount countStart finish numericBound
      (zeroTaskLayoutTerminalBitBound bitBound)
      (fixedNumeralTerm 0)
      hwidthValue (hcountStartLe.trans htokenCountValue)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) hcountStartSize (by
        rw [termValue_fixedNumeralTerm_zero]
        exact (by decide : Nat.size 0 <= 2) |>.trans (by
          unfold zeroTaskLayoutTerminalBitBound
          omega))
      (hfinishSize.trans hbit)
      (fixedZero_code_le_zeroTerminalEnvelope bitBound)
      (fixedNumeralTerm_freeVariables_eq_empty_zero 0) (by
        simpa only [
          FoundationCompactPAValuationTermCompiler.termValue_shortBinaryNumeralTerm,
          termValue_fixedNumeralTerm_zero] using hrepeat)
  let formula1 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm start)
    (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderStart)
  let formula2 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm binderStart)
    (shortBinaryNumeralTerm binderArity)
    (shortBinaryNumeralTerm countStart)
  let formula3 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm countStart)
    (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm finish)
  have hformula1Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount start binderStart
      (zeroTaskLayoutTerminalBitBound bitBound) (fixedNumeralTerm 0)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hstartSize.trans hbit)
      hbinderStartSize (fixedZero_code_le_zeroTerminalEnvelope bitBound)
  have hformula2Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount binderStart countStart
      (zeroTaskLayoutTerminalBitBound bitBound)
      (shortBinaryNumeralTerm binderArity) (htableSize.trans hbit)
      (hwidthSize.trans hbit) (htokenCountSize.trans hbit)
      hbinderStartSize hcountStartSize
      (binderShort_code_le_zeroTerminalEnvelope binderArity bitBound
        hbinderSize)
  have hformula3Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount countStart finish
      (zeroTaskLayoutTerminalBitBound bitBound)
      (fixedNumeralTerm 0)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) hcountStartSize (hfinishSize.trans hbit)
      (fixedZero_code_le_zeroTerminalEnvelope bitBound)
  have htotalCode :
      (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
        zeroTaskLayoutTerminalFormulaCodeEnvelope bitBound :=
    threeFormulaCode_le_zeroTerminalEnvelope formula1 formula2 formula3
      bitBound hformula1Code hformula2Code hformula3Code
  have htotalClosed :
      (formula1 ⋏ (formula2 ⋏ formula3)).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_and]
    rw [
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount start binderStart (fixedNumeralTerm 0)
        (fixedNumeralTerm_freeVariables_eq_empty_zero 0),
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount binderStart countStart
        (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity),
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount countStart finish
        (fixedNumeralTerm 0)
        (fixedNumeralTerm_freeVariables_eq_empty_zero 0)]
    simp
  have hpositive :
      1 <= zeroTaskLayoutTerminalFormulaCodeEnvelope bitBound := by
    unfold zeroTaskLayoutTerminalFormulaCodeEnvelope
    omega
  have henvelope :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      layoutZeroValuation formula1 formula2 formula3
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (zeroTaskLayoutTerminalBitBound bitBound))
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (zeroTaskLayoutTerminalBitBound bitBound))
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (zeroTaskLayoutTerminalBitBound bitBound))
      (zeroTaskLayoutTerminalFormulaCodeEnvelope bitBound)
      hpositive htotalClosed htotalCode
  let certificate1 :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm start)
      (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderStart) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_fixedNumeralTerm_zero] using hkind)
  let certificate2 :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm binderStart)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm countStart) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hbinder)
  let certificate3 :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm countStart)
      (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm finish) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_fixedNumeralTerm_zero] using hrepeat)
  let certificate23 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate2
      certificate3
  have hcertificate23 := transparentHybridConjunctionPayloadBound_le
    certificate2 certificate3 _ _ hbinderResource hrepeatResource
  let certificate123 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate1
      certificate23
  have hcertificate123 := transparentHybridConjunctionPayloadBound_le
    certificate1 certificate23 _ _ hkindResource hcertificate23
  change hybridFormulaStructuralPayloadBound certificate123 <= _
  exact hcertificate123.trans (by
    simpa only [formula1, formula2, formula3,
      zeroTaskLayoutTerminalPayloadEnvelope] using henvelope)

#print axioms
  zeroTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutZeroTerminalFullyFixedBounds
