import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed installation of a generic task-list head

The two target-boundary witnesses are installed above the genuine three-leaf
head terminal.  The body code, empty context, witness bounds, and terminal
resource are all derived internally.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadInstalledFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadTerminalFullyFixedBounds

private abbrev headZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

def taskConsGenericHeadInstalledTermCodeEnvelope (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope
      (genericTaskLayoutTerminalBitBound bitBound) +
    (binaryTermCode (unaryNumeralTerm 0)).length +
    (binaryTermCode (unaryNumeralTerm 1)).length + 1

def taskConsGenericHeadInstalledBodyCodeEnvelope (bitBound : Nat) : Nat :=
  syntaxTaskListConsHeadTerminalBodyCodeEnvelope
    (taskConsGenericHeadInstalledTermCodeEnvelope bitBound)

def taskConsGenericHeadInstalledPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (taskConsGenericHeadInstalledBodyCodeEnvelope bitBound)
    (taskConsGenericHeadTerminalPayloadEnvelope tokenCount numericBound bitBound)

private theorem shortNumeral_code_le_headEnvelope
    (value bitBound : Nat)
    (hsize : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      taskConsGenericHeadInstalledTermCodeEnvelope bitBound := by
  have hbit : bitBound <= genericTaskLayoutTerminalBitBound bitBound := by
    simp only [genericTaskLayoutTerminalBitBound]
    omega
  exact (binaryNumeralTerm_code_length_le_envelope value
    (genericTaskLayoutTerminalBitBound bitBound) (hsize.trans hbit)).trans
      (by
        unfold taskConsGenericHeadInstalledTermCodeEnvelope
        omega)

private theorem unaryZero_code_le_headEnvelope (bitBound : Nat) :
    (binaryTermCode (unaryNumeralTerm 0)).length <=
      taskConsGenericHeadInstalledTermCodeEnvelope bitBound := by
  unfold taskConsGenericHeadInstalledTermCodeEnvelope
  omega

private theorem unaryOne_code_le_headEnvelope (bitBound : Nat) :
    (binaryTermCode (unaryNumeralTerm 1)).length <=
      taskConsGenericHeadInstalledTermCodeEnvelope bitBound := by
  unfold taskConsGenericHeadInstalledTermCodeEnvelope
  omega

theorem taskConsGenericHeadBody_freeVariables_eq_empty
    (tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount : Nat) :
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable
      width tokenCount targetBoundary (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
      tokenTable width tokenCount targetBoundary (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
  let body01 := terminal.bexsLTSucc
    (syntaxTaskListConsRowsClosedShift 1
      (shortBinaryNumeralTerm tokenCount))
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    exact
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_freeVariables_eq_empty
        tokenTable width tokenCount targetBoundary (shortBinaryNumeralTerm headKind)
        (shortBinaryNumeralTerm headBinderArity)
        (shortBinaryNumeralTerm headRepeatCount)
        (shortBinaryNumeralTerm_freeVariables_eq_empty headKind)
        (shortBinaryNumeralTerm_freeVariables_eq_empty headBinderArity)
        (shortBinaryNumeralTerm_freeVariables_eq_empty headRepeatCount)
  have hbody01subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount terminal
  have hbody01 : body01.freeVariables = ∅ :=
    Finset.subset_empty.mp (hbody01subset.trans (by rw [hterminal]))
  have hbody00subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount body01
  have hbody00 :
      (body01.bexsLTSucc
        (shortBinaryNumeralTerm tokenCount)).freeVariables = ∅ :=
    Finset.subset_empty.mp (hbody00subset.trans (by rw [hbody01]))
  simpa only [
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody,
    syntaxTaskListConsRowsClosedShift, body01, terminal] using hbody00

theorem
    taskConsGenericHeadCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hheadKindSize : Nat.size headKind <= bitBound)
    (hheadBinderSize : Nat.size headBinderArity <= bitBound)
    (hheadRepeatSize : Nat.size headRepeatCount <= bitBound)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary headKind headBinderArity headRepeatCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate
          tokenTable width tokenCount targetBoundary headKind headBinderArity
          headRepeatCount
          (shortBinaryNumeralTerm headKind) (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount)
          (termValue_shortBinaryNumeralTerm · headKind)
          (termValue_shortBinaryNumeralTerm · headBinderArity)
          (termValue_shortBinaryNumeralTerm · headRepeatCount) data) <=
      taskConsGenericHeadInstalledPayloadEnvelope tokenCount numericBound
        bitBound := by
  let values : Fin 2 -> Nat := ![data.targetRight, data.targetLeft]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact data.targetRight_le
    · exact data.targetLeft_le
  let body :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
      tokenTable width tokenCount targetBoundary (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
  have hvalueTerms :
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm (values coordinate)) =
          ![shortBinaryNumeralTerm data.targetRight,
            shortBinaryNumeralTerm data.targetLeft] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        headZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
        (shortBinaryNumeralTerm data.targetLeft) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetLeft_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          headZeroValuation (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
          (shortBinaryNumeralTerm data.targetRight) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_unaryNumeralTerm] using data.targetRight_entry))
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount data.targetLeft data.targetRight
          headKind headBinderArity headRepeatCount
          (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount)
          (termValue_shortBinaryNumeralTerm · headKind)
          (termValue_shortBinaryNumeralTerm · headBinderArity)
          (termValue_shortBinaryNumeralTerm · headRepeatCount) data.layout))
  let terminal :
      CheckedHybridValuationBoundedFormulaCertificate headZeroValuation
        (body ⇜ fun coordinate =>
          shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_substitution_alignment
          tokenTable width tokenCount targetBoundary data.targetLeft
          data.targetRight (shortBinaryNumeralTerm headKind)
          (shortBinaryNumeralTerm headBinderArity)
          (shortBinaryNumeralTerm headRepeatCount)).symm)
      terminalParts
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        taskConsGenericHeadTerminalPayloadEnvelope tokenCount numericBound
          bitBound := by
    simpa only [hybridFormulaStructuralPayloadBound, body, values,
      terminalParts, terminal] using
      (taskConsGenericHeadTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount targetBoundary headKind headBinderArity
        headRepeatCount numericBound bitBound hwidthValue htokenCountValue
        htableSize hwidthSize htokenCountSize htargetBoundarySize
        hheadKindSize hheadBinderSize hheadRepeatSize data)
  have hbody :
      (binaryFormulaCode body).length <=
        taskConsGenericHeadInstalledBodyCodeEnvelope bitBound := by
    apply
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_code_length_le_uniform
    · exact shortNumeral_code_le_headEnvelope tokenTable bitBound htableSize
    · exact shortNumeral_code_le_headEnvelope width bitBound hwidthSize
    · exact shortNumeral_code_le_headEnvelope tokenCount bitBound
        htokenCountSize
    · exact shortNumeral_code_le_headEnvelope targetBoundary bitBound
        htargetBoundarySize
    · exact unaryZero_code_le_headEnvelope bitBound
    · exact unaryOne_code_le_headEnvelope bitBound
    · exact shortNumeral_code_le_headEnvelope headKind bitBound hheadKindSize
    · exact shortNumeral_code_le_headEnvelope headBinderArity bitBound
        hheadBinderSize
    · exact shortNumeral_code_le_headEnvelope headRepeatCount bitBound
        hheadRepeatSize
  have hbodyClosed : body.freeVariables = ∅ :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_freeVariables_eq_empty
      tokenTable width tokenCount targetBoundary (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headKind)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headBinderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty headRepeatCount)
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables headZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hbuilt :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values hvalues terminal
      (taskConsGenericHeadTerminalPayloadEnvelope tokenCount numericBound bitBound)
      hterminal
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      headZeroValuation 0 tokenCount numericBound
      (taskConsGenericHeadInstalledBodyCodeEnvelope bitBound) body values hvalues
      htokenCountValue hbody hcontext (le_refl
        (taskConsGenericHeadTerminalPayloadEnvelope tokenCount numericBound
          bitBound))
  have hinstalled := hbuilt.trans hfixed
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast rfl
        (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
          hvalues terminal)) <= _
  simpa only [hybridFormulaStructuralPayloadBound,
    taskConsGenericHeadInstalledPayloadEnvelope] using hinstalled

#print axioms
  taskConsGenericHeadBody_freeVariables_eq_empty
#print axioms
  taskConsGenericHeadCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadInstalledFullyFixedBounds
