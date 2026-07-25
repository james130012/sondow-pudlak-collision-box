import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutFunctionTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed installation of a function syntax-task layout

The genuine `(2, binderArity, functionArity)` three-cell terminal is installed
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

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutFunctionInstalledFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskLayoutFunctionTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

def functionTaskLayoutInstalledBodyCodeEnvelope (bitBound : Nat) : Nat :=
  compactSyntaxTaskDirectLayoutTerminalBodyCodeEnvelope
    (binaryNumeralTermCodeEnvelope
      (functionTaskLayoutTerminalBitBound bitBound))

def functionTaskLayoutInstalledPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (functionTaskLayoutInstalledBodyCodeEnvelope bitBound)
    (functionTaskLayoutTerminalPayloadEnvelope numericBound bitBound)

def functionTaskLayoutFormulaCodeEnvelope
    (tokenCount bitBound : Nat) : Nat :=
  let body02 := functionTaskLayoutInstalledBodyCodeEnvelope bitBound
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

private theorem fixedTwo_code_le_installedTermEnvelope_function
    (bitBound : Nat) :
    (binaryTermCode (fixedNumeralTerm 2)).length <=
      binaryNumeralTermCodeEnvelope
        (functionTaskLayoutTerminalBitBound bitBound) := by
  apply le_trans ?_
    (binaryNumeralTermCodeEnvelope_ge_bit_installed
      (functionTaskLayoutTerminalBitBound bitBound))
  unfold functionTaskLayoutTerminalBitBound
  omega

private theorem binderShort_code_le_installedTermEnvelope_function
    (binderArity bitBound : Nat)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm binderArity)).length <=
      binaryNumeralTermCodeEnvelope
        (functionTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope binderArity
    (functionTaskLayoutTerminalBitBound bitBound)
    (hbinderSize.trans (by
      unfold functionTaskLayoutTerminalBitBound
      omega))

private theorem functionShort_code_le_installedTermEnvelope_function
    (functionArity bitBound : Nat)
    (hfunctionSize : Nat.size functionArity <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm functionArity)).length <=
      binaryNumeralTermCodeEnvelope
        (functionTaskLayoutTerminalBitBound bitBound) := by
  exact binaryNumeralTerm_code_length_le_envelope functionArity
    (functionTaskLayoutTerminalBitBound bitBound)
    (hfunctionSize.trans (by
      unfold functionTaskLayoutTerminalBitBound
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

theorem functionTaskLayoutFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount start finish binderArity functionArity
      bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hfunctionSize : Nat.size functionArity <= bitBound) :
    (binaryFormulaCode
      (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
        tokenCount start finish (fixedNumeralTerm 2)
        (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm functionArity))).length <=
      functionTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
  let body :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
  have hbit : bitBound <= functionTaskLayoutTerminalBitBound bitBound := by
    unfold functionTaskLayoutTerminalBitBound
    omega
  have hbody :
      (binaryFormulaCode body).length <=
        functionTaskLayoutInstalledBodyCodeEnvelope bitBound := by
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
    · exact fixedTwo_code_le_installedTermEnvelope_function bitBound
    · exact binderShort_code_le_installedTermEnvelope_function binderArity
        bitBound hbinderSize
    · exact functionShort_code_le_installedTermEnvelope_function
        functionArity bitBound hfunctionSize
  let body01 : ArithmeticSemiformula Nat 1 :=
    body.bexsLTSucc
      (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
        1 (shortBinaryNumeralTerm tokenCount))
  have hbody01 :
      (binaryFormulaCode body01).length <=
        explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount
          (functionTaskLayoutInstalledBodyCodeEnvelope bitBound) :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (functionTaskLayoutInstalledBodyCodeEnvelope bitBound) body hbody
  have hbody00 :
      (binaryFormulaCode
        (body01.bexsLTSucc (shortBinaryNumeralTerm tokenCount))).length <=
        functionTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
    have hraw :=
      explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 tokenCount
          (functionTaskLayoutInstalledBodyCodeEnvelope bitBound))
        body01 hbody01
    simpa only [functionTaskLayoutFormulaCodeEnvelope, body01,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using hraw
  rw [compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment]
  simpa only [explicitBoundedWitnessFormula, body, body01,
    FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
    using hbody00

theorem functionTaskLayoutFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount start finish binderArity functionArity :
      Nat) :
    (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
      tokenCount start finish (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)).freeVariables = ∅ := by
  rw [compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment]
  unfold explicitBoundedWitnessFormula
  have hbody :=
    compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty
      tokenTable width tokenCount start finish (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
      (fixedNumeralTerm_freeVariables_eq_empty_installed 2)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty functionArity)
  change
    (((compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)).bexsLTSucc
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
    functionTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
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
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start finish 2 binderArity functionArity
          (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm functionArity)
          (termValue_fixedNumeralTerm_installed · 2)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_shortBinaryNumeralTerm · functionArity) hlayout) <=
      functionTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
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
      tokenCount start finish (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
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
        (shortBinaryNumeralTerm start) (fixedNumeralTerm 2)
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
          (shortBinaryNumeralTerm functionArity)
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
          (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm functionArity)).symm) terminalParts
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        functionTaskLayoutTerminalPayloadEnvelope numericBound bitBound := by
    change hybridFormulaStructuralPayloadBound terminalParts <= _
    simpa only [binderStart, countStart, terminalParts] using
      (functionTaskLayoutTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount start finish binderArity functionArity
        numericBound bitBound hwidthValue htokenCountValue htableSize
        hwidthSize htokenCountSize hstartSize hfinishSize hbinderSize
        hfunctionSize hlayout)
  have hbit : bitBound <= functionTaskLayoutTerminalBitBound bitBound := by
    unfold functionTaskLayoutTerminalBitBound
    omega
  have hbody :
      (binaryFormulaCode body).length <=
        functionTaskLayoutInstalledBodyCodeEnvelope bitBound := by
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
    · exact fixedTwo_code_le_installedTermEnvelope_function bitBound
    · exact binderShort_code_le_installedTermEnvelope_function binderArity
        bitBound hbinderSize
    · exact functionShort_code_le_installedTermEnvelope_function
        functionArity bitBound hfunctionSize
  have hbodyClosed : body.freeVariables = ∅ := by
    exact
      compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_freeVariables_eq_empty
        tokenTable width tokenCount start finish (fixedNumeralTerm 2)
        (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm functionArity)
        (fixedNumeralTerm_freeVariables_eq_empty_installed 2)
        (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
        (shortBinaryNumeralTerm_freeVariables_eq_empty functionArity)
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables layoutZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hbuilt :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values hvalues terminal
      (functionTaskLayoutTerminalPayloadEnvelope numericBound bitBound)
      hterminal
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      layoutZeroValuation 0 tokenCount numericBound
      (functionTaskLayoutInstalledBodyCodeEnvelope bitBound) body values
      hvalues htokenCountValue hbody hcontext (le_refl
        (functionTaskLayoutTerminalPayloadEnvelope numericBound bitBound))
  have hinstalled := hbuilt.trans hfixed
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment
          tokenTable width tokenCount start finish (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm functionArity)).symm
        (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
          hvalues terminal)) <= _
  simpa only [hybridFormulaStructuralPayloadBound,
    functionTaskLayoutInstalledPayloadEnvelope] using hinstalled

#print axioms functionTaskLayoutFormula_code_length_le_fullyFixed
#print axioms functionTaskLayoutFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  functionTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskLayoutFunctionInstalledFullyFixedBounds
