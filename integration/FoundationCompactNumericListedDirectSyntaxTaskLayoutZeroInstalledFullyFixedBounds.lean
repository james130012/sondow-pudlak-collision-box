import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutZeroTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed installation of a zero syntax-task layout

The genuine `(0, binderArity, 0)` three-cell terminal is installed
below its two bounded cursor witnesses. Its open body has a fixed code
envelope and empty valuation context, so no finite sum or caller-supplied
syntax bound remains.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 350000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutZeroInstalledFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutZeroTerminalFullyFixedBounds

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

def zeroTaskLayoutInstalledBodyCodeEnvelope (bitBound : Nat) : Nat :=
  compactSyntaxTaskDirectLayoutTerminalBodyCodeEnvelope
    (binaryNumeralTermCodeEnvelope
      (zeroTaskLayoutTerminalBitBound bitBound))

def zeroTaskLayoutInstalledPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (zeroTaskLayoutInstalledBodyCodeEnvelope bitBound)
    (zeroTaskLayoutTerminalPayloadEnvelope numericBound bitBound)

def zeroTaskLayoutFormulaCodeEnvelope
    (tokenCount bitBound : Nat) : Nat :=
  let body02 := zeroTaskLayoutInstalledBodyCodeEnvelope bitBound
  let body01 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount body02
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 0 tokenCount body01

private theorem binaryNumeralTermCodeEnvelope_ge_bit_installed
    (bitBound : Nat) :
    bitBound <= binaryNumeralTermCodeEnvelope bitBound := by
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hmul := Nat.mul_le_mul_right bitBound hstep
  unfold binaryNumeralTermCodeEnvelope
  omega

private theorem fixedNumeralTerm_freeVariables_eq_empty_installed
    (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

@[simp] private theorem termValue_fixedNumeralTerm_installed
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  simp [fixedNumeralTerm, termValue]

private theorem fixedZero_code_le_installedTermEnvelope_zero
    (bitBound : Nat) :
    (binaryTermCode (fixedNumeralTerm 0)).length <=
      binaryNumeralTermCodeEnvelope
        (zeroTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_
    (binaryNumeralTermCodeEnvelope_ge_bit_installed
      (zeroTaskLayoutTerminalBitBound bitBound))
  unfold zeroTaskLayoutTerminalBitBound
  omega

private theorem binderShort_code_le_installedTermEnvelope_zero
    (binderArity bitBound : Nat)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm binderArity)).length <=
      binaryNumeralTermCodeEnvelope
        (zeroTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope binderArity
    (zeroTaskLayoutTerminalBitBound bitBound)
    (hbinderSize.trans (by
      unfold zeroTaskLayoutTerminalBitBound
      omega))

private theorem binaryLayoutBexsLTSucc_freeVariables_eq_empty
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity)
    (hbody : body.freeVariables = ∅)
    (hbound : bound.freeVariables = ∅) :
    (body.bexsLTSucc bound).freeVariables = ∅ := by
  have hone : (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    simp [LO.FirstOrder.Semiterm.Operator.operator,
      LO.FirstOrder.Semiterm.Operator.numeral_one,
      LO.FirstOrder.Semiterm.Operator.One.term_eq]
  have hsuccessor :
      (‘!!bound + 1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    rw [arithmeticAddTerm_freeVariables_eq_union, hbound, hone]
    simp
  have hshifted :
      (Rew.bShift
        (‘!!bound + 1’ : ArithmeticSemiterm Nat arity)).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty _ hsuccessor
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
    LO.FirstOrder.Semiformula.bexsLT LO.FirstOrder.bexs
  rw [LO.FirstOrder.Semiformula.freeVariables_exs,
    LO.FirstOrder.Semiformula.freeVariables_and,
    lessThanFormula_freeVariables, hshifted, hbody]
  simp

theorem zeroTaskLayoutFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount start finish binderArity
      bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryFormulaCode
      (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
        tokenCount start finish (fixedNumeralTerm 0)
        (shortBinaryNumeralTerm binderArity)
        (fixedNumeralTerm 0))).length <=
      zeroTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
  let body :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  have hbit : bitBound <= zeroTaskLayoutTerminalBitBound bitBound := by
    unfold zeroTaskLayoutTerminalBitBound
    omega
  have hbody :
      (binaryFormulaCode body).length <=
        zeroTaskLayoutInstalledBodyCodeEnvelope bitBound := by
    apply
      compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_code_length_le_uniform
    · exact binaryNumeralTerm_code_length_le_envelope tokenTable _
        (htableSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope width _
        (hwidthSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope tokenCount _
        (htokenCountSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope start _
        (hstartSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope finish _
        (hfinishSize.trans hbit)
    · exact fixedZero_code_le_installedTermEnvelope_zero bitBound
    · exact binderShort_code_le_installedTermEnvelope_zero binderArity
        bitBound hbinderSize
    · exact fixedZero_code_le_installedTermEnvelope_zero bitBound
  let body01 : ArithmeticSemiformula Nat 1 :=
    body.bexsLTSucc
      (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
        1 (shortBinaryNumeralTerm tokenCount))
  have hbody01 :
      (binaryFormulaCode body01).length <=
        explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount
          (zeroTaskLayoutInstalledBodyCodeEnvelope bitBound) :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (zeroTaskLayoutInstalledBodyCodeEnvelope bitBound) body hbody
  have hbody00 :
      (binaryFormulaCode
        (body01.bexsLTSucc (shortBinaryNumeralTerm tokenCount))).length <=
        zeroTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
    have hraw :=
      explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount
          (zeroTaskLayoutInstalledBodyCodeEnvelope bitBound))
        body01 hbody01
    simpa only [zeroTaskLayoutFormulaCodeEnvelope, body01,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using hraw
  rw [compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment]
  simpa only [explicitBoundedWitnessFormula, body, body01,
    FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
    using hbody00

theorem zeroTaskLayoutFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount start finish binderArity : Nat) :
    (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
      tokenCount start finish (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)).freeVariables = ∅ := by
  rw [compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment]
  unfold explicitBoundedWitnessFormula
  have hbody :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty
      tokenTable width tokenCount start finish (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
      (fixedNumeralTerm_freeVariables_eq_empty_installed 0)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (fixedNumeralTerm_freeVariables_eq_empty_installed 0)
  change
    (((compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)).bexsLTSucc
        (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
          1 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (shortBinaryNumeralTerm tokenCount)).freeVariables = ∅
  apply binaryLayoutBexsLTSucc_freeVariables_eq_empty
  · apply binaryLayoutBexsLTSucc_freeVariables_eq_empty
    · exact hbody
    · apply bShift_freeVariables_eq_empty_of_empty
      exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount

theorem
    zeroTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
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
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start finish 0 binderArity 0
          (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0)
          (termValue_fixedNumeralTerm_installed · 0)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_fixedNumeralTerm_installed · 0) hlayout) <=
      zeroTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
  let binderStart := Classical.choose hlayout
  have hbinderData := Classical.choose_spec hlayout
  let countStart := Classical.choose hbinderData
  have hcells := Classical.choose_spec hbinderData
  have hkind := hcells.1
  have hbinder := hcells.2.1
  have hrepeat := hcells.2.2
  have hbinderStartLe : binderStart <= tokenCount :=
    Nat.le_of_lt hbinder.1
  have hcountStartLe : countStart <= tokenCount :=
    Nat.le_of_lt hrepeat.1
  let values : Fin 2 -> Nat := ![countStart, binderStart]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact hcountStartLe
    · exact hbinderStartLe
  let body :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  have hvalueTerms :
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm (values coordinate)) =
          ![shortBinaryNumeralTerm countStart,
            shortBinaryNumeralTerm binderStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm start) (fixedNumeralTerm 0)
        (shortBinaryNumeralTerm binderStart) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_fixedNumeralTerm_installed] using hkind))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm binderStart)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm countStart) (by
            simpa only [termValue_shortBinaryNumeralTerm] using hbinder))
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm countStart)
          (fixedNumeralTerm 0)
          (shortBinaryNumeralTerm finish) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_fixedNumeralTerm_installed] using hrepeat)))
  let terminal :
      CheckedHybridValuationBoundedFormulaCertificate layoutZeroValuation
        (body ⇜ fun coordinate =>
          shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_substitution_alignment
          tokenTable width tokenCount start finish binderStart countStart
          (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0)).symm) terminalParts
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        zeroTaskLayoutTerminalPayloadEnvelope numericBound bitBound := by
    change hybridFormulaStructuralPayloadBound terminalParts <= _
    simpa only [binderStart, countStart, terminalParts] using
      (zeroTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount start finish binderArity
        numericBound bitBound hwidthValue htokenCountValue htableSize
        hwidthSize htokenCountSize hstartSize hfinishSize hbinderSize
        hlayout)
  have hbit : bitBound <= zeroTaskLayoutTerminalBitBound bitBound := by
    unfold zeroTaskLayoutTerminalBitBound
    omega
  have hbody :
      (binaryFormulaCode body).length <=
        zeroTaskLayoutInstalledBodyCodeEnvelope bitBound := by
    apply
      compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_code_length_le_uniform
    · exact binaryNumeralTerm_code_length_le_envelope tokenTable _
        (htableSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope width _
        (hwidthSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope tokenCount _
        (htokenCountSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope start _
        (hstartSize.trans hbit)
    · exact binaryNumeralTerm_code_length_le_envelope finish _
        (hfinishSize.trans hbit)
    · exact fixedZero_code_le_installedTermEnvelope_zero bitBound
    · exact binderShort_code_le_installedTermEnvelope_zero binderArity
        bitBound hbinderSize
    · exact fixedZero_code_le_installedTermEnvelope_zero bitBound
  have hbodyClosed : body.freeVariables = ∅ := by
    exact
      compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty
        tokenTable width tokenCount start finish (fixedNumeralTerm 0)
        (shortBinaryNumeralTerm binderArity)
        (fixedNumeralTerm 0)
        (fixedNumeralTerm_freeVariables_eq_empty_installed 0)
        (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
        (fixedNumeralTerm_freeVariables_eq_empty_installed 0)
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables layoutZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hbuilt :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values hvalues terminal
      (zeroTaskLayoutTerminalPayloadEnvelope numericBound bitBound)
      hterminal
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      layoutZeroValuation 0 tokenCount numericBound
      (zeroTaskLayoutInstalledBodyCodeEnvelope bitBound) body values
      hvalues htokenCountValue hbody hcontext (le_refl
        (zeroTaskLayoutTerminalPayloadEnvelope numericBound bitBound))
  have hinstalled := hbuilt.trans hfixed
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment
          tokenTable width tokenCount start finish (fixedNumeralTerm 0)
          (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0)).symm
        (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
          hvalues terminal)) <= _
  simpa only [hybridFormulaStructuralPayloadBound,
    zeroTaskLayoutInstalledPayloadEnvelope] using hinstalled

#print axioms zeroTaskLayoutFormula_code_length_le_fullyFixed
#print axioms zeroTaskLayoutFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  zeroTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutZeroInstalledFullyFixedBounds
