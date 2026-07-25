import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed installation of a generic syntax-task layout

The genuine arbitrary three-field terminal is installed below its two
bounded cursor witnesses. Its open body has a fixed code envelope and empty
valuation context, so no finite sum or caller-supplied syntax bound remains.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 350000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericInstalledFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericTerminalFullyFixedBounds

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

def genericTaskLayoutInstalledBodyCodeEnvelope (bitBound : Nat) : Nat :=
  compactSyntaxTaskDirectLayoutTerminalBodyCodeEnvelope
    (binaryNumeralTermCodeEnvelope
      (genericTaskLayoutTerminalBitBound bitBound))

def genericTaskLayoutInstalledPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (genericTaskLayoutInstalledBodyCodeEnvelope bitBound)
    (genericTaskLayoutTerminalPayloadEnvelope numericBound bitBound)

def genericTaskLayoutFormulaCodeEnvelope
    (tokenCount bitBound : Nat) : Nat :=
  let body02 := genericTaskLayoutInstalledBodyCodeEnvelope bitBound
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

private theorem kindShort_code_le_installedTermEnvelope_generic
    (headKind bitBound : Nat)
    (hheadKindSize : Nat.size headKind <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm headKind)).length <=
      binaryNumeralTermCodeEnvelope
        (genericTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope headKind
    (genericTaskLayoutTerminalBitBound bitBound)
    (hheadKindSize.trans (by
      unfold genericTaskLayoutTerminalBitBound
      omega))

private theorem binderShort_code_le_installedTermEnvelope_generic
    (headBinderArity bitBound : Nat)
    (hheadBinderSize : Nat.size headBinderArity <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm headBinderArity)).length <=
      binaryNumeralTermCodeEnvelope
        (genericTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope headBinderArity
    (genericTaskLayoutTerminalBitBound bitBound)
    (hheadBinderSize.trans (by
      unfold genericTaskLayoutTerminalBitBound
      omega))

private theorem repeatShort_code_le_installedTermEnvelope_generic
    (headRepeatCount bitBound : Nat)
    (hheadRepeatSize : Nat.size headRepeatCount <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm headRepeatCount)).length <=
      binaryNumeralTermCodeEnvelope
        (genericTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope headRepeatCount
    (genericTaskLayoutTerminalBitBound bitBound)
    (hheadRepeatSize.trans (by
      unfold genericTaskLayoutTerminalBitBound
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

theorem genericTaskLayoutFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount start finish headKind headBinderArity
      headRepeatCount bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hheadKindSize : Nat.size headKind <= bitBound)
    (hheadBinderSize : Nat.size headBinderArity <= bitBound)
    (hheadRepeatSize : Nat.size headRepeatCount <= bitBound) :
    (binaryFormulaCode
      (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
        tokenCount start finish (shortBinaryNumeralTerm headKind)
        (shortBinaryNumeralTerm headBinderArity)
        (shortBinaryNumeralTerm headRepeatCount))).length <=
      genericTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
  let body :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
  have hbit : bitBound <= genericTaskLayoutTerminalBitBound bitBound := by
    unfold genericTaskLayoutTerminalBitBound
    omega
  have hbody :
      (binaryFormulaCode body).length <=
        genericTaskLayoutInstalledBodyCodeEnvelope bitBound := by
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
    · exact kindShort_code_le_installedTermEnvelope_generic headKind bitBound
        hheadKindSize
    · exact binderShort_code_le_installedTermEnvelope_generic headBinderArity
        bitBound hheadBinderSize
    · exact repeatShort_code_le_installedTermEnvelope_generic
        headRepeatCount bitBound hheadRepeatSize
  let body01 : ArithmeticSemiformula Nat 1 :=
    body.bexsLTSucc
      (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
        1 (shortBinaryNumeralTerm tokenCount))
  have hbody01 :
      (binaryFormulaCode body01).length <=
        explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount
          (genericTaskLayoutInstalledBodyCodeEnvelope bitBound) :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (genericTaskLayoutInstalledBodyCodeEnvelope bitBound) body hbody
  have hbody00 :
      (binaryFormulaCode
        (body01.bexsLTSucc (shortBinaryNumeralTerm tokenCount))).length <=
        genericTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
    have hraw :=
      explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount
          (genericTaskLayoutInstalledBodyCodeEnvelope bitBound))
        body01 hbody01
    simpa only [genericTaskLayoutFormulaCodeEnvelope, body01,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using hraw
  rw [compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment]
  simpa only [explicitBoundedWitnessFormula, body, body01,
    FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
    using hbody00

theorem genericTaskLayoutFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount start finish headKind headBinderArity
      headRepeatCount : Nat) :
    (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
      tokenCount start finish (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)).freeVariables = ∅ := by
  rw [compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment]
  unfold explicitBoundedWitnessFormula
  have hbody :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty
      tokenTable width tokenCount start finish (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headKind)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headBinderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headRepeatCount)
  change
    (((compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)).bexsLTSucc
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
    genericTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount start finish headKind headBinderArity
      headRepeatCount numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hheadKindSize : Nat.size headKind <= bitBound)
    (hheadBinderSize : Nat.size headBinderArity <= bitBound)
    (hheadRepeatSize : Nat.size headRepeatCount <= bitBound)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (headKind, headBinderArity, headRepeatCount)) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start finish headKind headBinderArity
          headRepeatCount
          (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount)
          (termValue_shortBinaryNumeralTerm · headKind)
          (termValue_shortBinaryNumeralTerm · headBinderArity)
          (termValue_shortBinaryNumeralTerm · headRepeatCount) hlayout) <=
      genericTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
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
      tokenCount start finish (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
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
        (shortBinaryNumeralTerm start) (shortBinaryNumeralTerm headKind)
        (shortBinaryNumeralTerm binderStart) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_shortBinaryNumeralTerm] using hkind))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm binderStart)
          (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm countStart) (by
            simpa only [termValue_shortBinaryNumeralTerm] using hbinder))
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm countStart)
          (shortBinaryNumeralTerm headRepeatCount)
          (shortBinaryNumeralTerm finish) (by
            simpa only [termValue_shortBinaryNumeralTerm] using hrepeat)))
  let terminal :
      CheckedHybridValuationBoundedFormulaCertificate layoutZeroValuation
        (body ⇜ fun coordinate =>
          shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_substitution_alignment
          tokenTable width tokenCount start finish binderStart countStart
          (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount)).symm) terminalParts
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        genericTaskLayoutTerminalPayloadEnvelope numericBound bitBound := by
    change hybridFormulaStructuralPayloadBound terminalParts <= _
    simpa only [binderStart, countStart, terminalParts] using
      (genericTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount start finish headKind headBinderArity
        headRepeatCount numericBound bitBound hwidthValue htokenCountValue
        htableSize hwidthSize htokenCountSize hstartSize hfinishSize
        hheadKindSize hheadBinderSize hheadRepeatSize hlayout)
  have hbit : bitBound <= genericTaskLayoutTerminalBitBound bitBound := by
    unfold genericTaskLayoutTerminalBitBound
    omega
  have hbody :
      (binaryFormulaCode body).length <=
        genericTaskLayoutInstalledBodyCodeEnvelope bitBound := by
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
    · exact kindShort_code_le_installedTermEnvelope_generic headKind bitBound
        hheadKindSize
    · exact binderShort_code_le_installedTermEnvelope_generic headBinderArity
        bitBound hheadBinderSize
    · exact repeatShort_code_le_installedTermEnvelope_generic
        headRepeatCount bitBound hheadRepeatSize
  have hbodyClosed : body.freeVariables = ∅ := by
    exact
      compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty
        tokenTable width tokenCount start finish (shortBinaryNumeralTerm headKind)
        (shortBinaryNumeralTerm headBinderArity)
        (shortBinaryNumeralTerm headRepeatCount)
        (shortBinaryNumeralTerm_freeVariables_eq_empty headKind)
        (shortBinaryNumeralTerm_freeVariables_eq_empty headBinderArity)
        (shortBinaryNumeralTerm_freeVariables_eq_empty headRepeatCount)
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables layoutZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hbuilt :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values hvalues terminal
      (genericTaskLayoutTerminalPayloadEnvelope numericBound bitBound)
      hterminal
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      layoutZeroValuation 0 tokenCount numericBound
      (genericTaskLayoutInstalledBodyCodeEnvelope bitBound) body values
      hvalues htokenCountValue hbody hcontext (le_refl
        (genericTaskLayoutTerminalPayloadEnvelope numericBound bitBound))
  have hinstalled := hbuilt.trans hfixed
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment
          tokenTable width tokenCount start finish (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount)).symm
        (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
          hvalues terminal)) <= _
  simpa only [hybridFormulaStructuralPayloadBound,
    genericTaskLayoutInstalledPayloadEnvelope] using hinstalled

#print axioms genericTaskLayoutFormula_code_length_le_fullyFixed
#print axioms genericTaskLayoutFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  genericTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericInstalledFullyFixedBounds
