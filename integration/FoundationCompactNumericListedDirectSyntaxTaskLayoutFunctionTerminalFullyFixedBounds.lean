import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed terminal bound for a function syntax-task layout

The function task stores the fixed kind term `2` and the short binary
numerals for `binderArity` and `functionArity`.  The three real token-cell
certificates are charged separately and reassembled in the original
right-associated conjunction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutFunctionTerminalFullyFixedBounds

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
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

def functionTaskLayoutTerminalBitBound (bitBound : Nat) : Nat :=
  bitBound + binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (fixedNumeralTerm 2)).length + 3

def functionTaskLayoutTerminalFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  3 * additiveTokenCellClosedValueFormulaCodeEnvelope
      (functionTaskLayoutTerminalBitBound bitBound) +
    2 * (binaryNatCode 4).length + 1

def functionTaskLayoutTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (functionTaskLayoutTerminalFormulaCodeEnvelope bitBound)
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (functionTaskLayoutTerminalBitBound bitBound))
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (functionTaskLayoutTerminalBitBound bitBound))
    (additiveTokenCellFullyUniformPayloadPolynomial numericBound
      (functionTaskLayoutTerminalBitBound bitBound))

private theorem binaryNumeralTermCodeEnvelope_ge_bit_function
    (bitBound : Nat) :
    bitBound <= binaryNumeralTermCodeEnvelope bitBound := by
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hmul := Nat.mul_le_mul_right bitBound hstep
  unfold binaryNumeralTermCodeEnvelope
  omega

private theorem functionTaskLayout_bit_le (bitBound : Nat) :
    bitBound <= functionTaskLayoutTerminalBitBound bitBound := by
  unfold functionTaskLayoutTerminalBitBound
  omega

private theorem fixedNumeralTerm_freeVariables_eq_empty_function
    (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

@[simp] private theorem termValue_fixedNumeralTerm_function
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  simp [fixedNumeralTerm, termValue]

private theorem fixedTwo_code_le_functionTerminalEnvelope
    (bitBound : Nat) :
    (binaryTermCode (fixedNumeralTerm 2)).length <=
      binaryNumeralTermCodeEnvelope
        (functionTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_
    (binaryNumeralTermCodeEnvelope_ge_bit_function
      (functionTaskLayoutTerminalBitBound bitBound))
  unfold functionTaskLayoutTerminalBitBound
  omega

private theorem binderShort_code_le_functionTerminalEnvelope
    (binderArity bitBound : Nat)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm binderArity)).length <=
      binaryNumeralTermCodeEnvelope
        (functionTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope binderArity
    (functionTaskLayoutTerminalBitBound bitBound)
    (hbinderSize.trans (functionTaskLayout_bit_le bitBound))

private theorem functionShort_code_le_functionTerminalEnvelope
    (functionArity bitBound : Nat)
    (hfunctionSize : Nat.size functionArity <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm functionArity)).length <=
      binaryNumeralTermCodeEnvelope
        (functionTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope functionArity
    (functionTaskLayoutTerminalBitBound bitBound)
    (hfunctionSize.trans (functionTaskLayout_bit_le bitBound))

private theorem threeFormulaCode_le_functionTerminalEnvelope
    (formula1 formula2 formula3 : ValuationFormula)
    (bitBound : Nat)
    (hformula1 : (binaryFormulaCode formula1).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (functionTaskLayoutTerminalBitBound bitBound))
    (hformula2 : (binaryFormulaCode formula2).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (functionTaskLayoutTerminalBitBound bitBound))
    (hformula3 : (binaryFormulaCode formula3).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope
        (functionTaskLayoutTerminalBitBound bitBound)) :
    (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
      functionTaskLayoutTerminalFormulaCodeEnvelope bitBound := by
  have hinner := binaryFormulaCode_and_length_le_local formula2 formula3
  have houter := binaryFormulaCode_and_length_le_local formula1
    (formula2 ⋏ formula3)
  unfold functionTaskLayoutTerminalFormulaCodeEnvelope
  omega

theorem
    functionTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount start finish binderArity functionArity
      numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hfunctionSize : Nat.size functionArity <= bitBound)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (2, binderArity, functionArity)) :
    let binderStart := Classical.choose hlayout
    let countStart := Classical.choose (Classical.choose_spec hlayout)
    let certificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm start) (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderStart) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_fixedNumeralTerm_function] using
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
            (shortBinaryNumeralTerm functionArity)
            (shortBinaryNumeralTerm finish) (by
              simpa only [termValue_shortBinaryNumeralTerm] using
                  (Classical.choose_spec
                    (Classical.choose_spec hlayout)).2.2)))
    hybridFormulaStructuralPayloadBound certificate <=
      functionTaskLayoutTerminalPayloadEnvelope numericBound bitBound := by
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
  have hbit := functionTaskLayout_bit_le bitBound
  have hbinderStartSize :
      Nat.size binderStart <= functionTaskLayoutTerminalBitBound bitBound :=
    (Nat.size_le_size hbinderStartLe).trans (htokenCountSize.trans hbit)
  have hcountStartSize :
      Nat.size countStart <= functionTaskLayoutTerminalBitBound bitBound :=
    (Nat.size_le_size hcountStartLe).trans (htokenCountSize.trans hbit)
  have hkindResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount start binderStart numericBound
      (functionTaskLayoutTerminalBitBound bitBound) (fixedNumeralTerm 2)
      hwidthValue (hstartLe.trans htokenCountValue)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hstartSize.trans hbit) (by
        rw [termValue_fixedNumeralTerm_function]
        exact (by decide : Nat.size 2 <= 2) |>.trans (by
          unfold functionTaskLayoutTerminalBitBound
          omega))
      hbinderStartSize (fixedTwo_code_le_functionTerminalEnvelope bitBound)
      (fixedNumeralTerm_freeVariables_eq_empty_function 2) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_fixedNumeralTerm_function] using hkind)
  have hbinderResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount binderStart countStart numericBound
      (functionTaskLayoutTerminalBitBound bitBound)
      (shortBinaryNumeralTerm binderArity) hwidthValue
      (hbinderStartLe.trans htokenCountValue) (htableSize.trans hbit)
      (hwidthSize.trans hbit) (htokenCountSize.trans hbit)
      hbinderStartSize (by
        simpa only [termValue_shortBinaryNumeralTerm] using
          hbinderSize.trans hbit) hcountStartSize
      (binderShort_code_le_functionTerminalEnvelope binderArity bitBound
        hbinderSize)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hbinder)
  have hrepeatResource :=
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount countStart finish numericBound
      (functionTaskLayoutTerminalBitBound bitBound)
      (shortBinaryNumeralTerm functionArity)
      hwidthValue (hcountStartLe.trans htokenCountValue)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) hcountStartSize (by
        rw [termValue_shortBinaryNumeralTerm]
        exact hfunctionSize.trans hbit)
      (hfinishSize.trans hbit)
      (functionShort_code_le_functionTerminalEnvelope functionArity bitBound
        hfunctionSize)
      (shortBinaryNumeralTerm_freeVariables_eq_empty functionArity) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hrepeat)
  let formula1 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm start)
    (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderStart)
  let formula2 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm binderStart)
    (shortBinaryNumeralTerm binderArity)
    (shortBinaryNumeralTerm countStart)
  let formula3 := compactAdditiveTokenCellAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm countStart)
    (shortBinaryNumeralTerm functionArity)
      (shortBinaryNumeralTerm finish)
  have hformula1Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount start binderStart
      (functionTaskLayoutTerminalBitBound bitBound) (fixedNumeralTerm 2)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) (hstartSize.trans hbit)
      hbinderStartSize (fixedTwo_code_le_functionTerminalEnvelope bitBound)
  have hformula2Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount binderStart countStart
      (functionTaskLayoutTerminalBitBound bitBound)
      (shortBinaryNumeralTerm binderArity) (htableSize.trans hbit)
      (hwidthSize.trans hbit) (htokenCountSize.trans hbit)
      hbinderStartSize hcountStartSize
      (binderShort_code_le_functionTerminalEnvelope binderArity bitBound
        hbinderSize)
  have hformula3Code :=
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
      tokenTable width tokenCount countStart finish
      (functionTaskLayoutTerminalBitBound bitBound)
      (shortBinaryNumeralTerm functionArity)
      (htableSize.trans hbit) (hwidthSize.trans hbit)
      (htokenCountSize.trans hbit) hcountStartSize (hfinishSize.trans hbit)
      (functionShort_code_le_functionTerminalEnvelope functionArity bitBound
        hfunctionSize)
  have htotalCode :
      (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
        functionTaskLayoutTerminalFormulaCodeEnvelope bitBound :=
    threeFormulaCode_le_functionTerminalEnvelope formula1 formula2 formula3
      bitBound hformula1Code hformula2Code hformula3Code
  have htotalClosed :
      (formula1 ⋏ (formula2 ⋏ formula3)).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_and]
    rw [
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount start binderStart (fixedNumeralTerm 2)
        (fixedNumeralTerm_freeVariables_eq_empty_function 2),
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount binderStart countStart
        (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity),
      compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
        tokenTable width tokenCount countStart finish
        (shortBinaryNumeralTerm functionArity)
        (shortBinaryNumeralTerm_freeVariables_eq_empty functionArity)]
    simp
  have hpositive :
      1 <= functionTaskLayoutTerminalFormulaCodeEnvelope bitBound := by
    unfold functionTaskLayoutTerminalFormulaCodeEnvelope
    omega
  have henvelope :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      layoutZeroValuation formula1 formula2 formula3
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (functionTaskLayoutTerminalBitBound bitBound))
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (functionTaskLayoutTerminalBitBound bitBound))
      (additiveTokenCellFullyUniformPayloadPolynomial numericBound
        (functionTaskLayoutTerminalBitBound bitBound))
      (functionTaskLayoutTerminalFormulaCodeEnvelope bitBound)
      hpositive htotalClosed htotalCode
  let certificate1 :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm start)
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderStart) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_fixedNumeralTerm_function] using hkind)
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
      (shortBinaryNumeralTerm functionArity)
      (shortBinaryNumeralTerm finish) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hrepeat)
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
      functionTaskLayoutTerminalPayloadEnvelope] using henvelope)

#print axioms
  functionTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutFunctionTerminalFullyFixedBounds
