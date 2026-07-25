import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsHeadTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed installation of the quantifier task-list head

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

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsHeadInstalledFullyFixedBounds

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
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayoutTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsHeadTerminalFullyFixedBounds

private abbrev headZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

def taskConsHeadInstalledTermCodeEnvelope (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope
      (quantifierTaskLayoutTerminalBitBound bitBound) +
    (binaryTermCode (unaryNumeralTerm 0)).length +
    (binaryTermCode (unaryNumeralTerm 1)).length + 1

def taskConsHeadInstalledBodyCodeEnvelope (bitBound : Nat) : Nat :=
  syntaxTaskListConsHeadTerminalBodyCodeEnvelope
    (taskConsHeadInstalledTermCodeEnvelope bitBound)

def taskConsHeadInstalledPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (taskConsHeadInstalledBodyCodeEnvelope bitBound)
    (taskConsHeadTerminalPayloadEnvelope tokenCount numericBound bitBound)

private theorem shortNumeral_code_le_headEnvelope
    (value bitBound : Nat)
    (hsize : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      taskConsHeadInstalledTermCodeEnvelope bitBound := by
  have hbit : bitBound <= quantifierTaskLayoutTerminalBitBound bitBound := by
    simp only [quantifierTaskLayoutTerminalBitBound,
      quantifierBinderSuccessorTokenCellBitBound]
    omega
  exact (binaryNumeralTerm_code_length_le_envelope value
    (quantifierTaskLayoutTerminalBitBound bitBound) (hsize.trans hbit)).trans
      (by
        unfold taskConsHeadInstalledTermCodeEnvelope
        omega)

private theorem unaryZero_code_le_headEnvelope (bitBound : Nat) :
    (binaryTermCode (unaryNumeralTerm 0)).length <=
      taskConsHeadInstalledTermCodeEnvelope bitBound := by
  unfold taskConsHeadInstalledTermCodeEnvelope
  omega

private theorem unaryOne_code_le_headEnvelope (bitBound : Nat) :
    (binaryTermCode (unaryNumeralTerm 1)).length <=
      taskConsHeadInstalledTermCodeEnvelope bitBound := by
  unfold taskConsHeadInstalledTermCodeEnvelope
  omega

private theorem nativeZero_code_le_headEnvelope (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 0)).length <=
      taskConsHeadInstalledTermCodeEnvelope bitBound := by
  have hraw :
      (binaryTermCode (nativeNumeralTerm 0)).length <=
        quantifierTaskLayoutTerminalBitBound bitBound := by
    simp only [quantifierTaskLayoutTerminalBitBound]
    omega
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hnumeral :
      quantifierTaskLayoutTerminalBitBound bitBound <=
        binaryNumeralTermCodeEnvelope
          (quantifierTaskLayoutTerminalBitBound bitBound) := by
    unfold binaryNumeralTermCodeEnvelope
    have := Nat.mul_le_mul_right
      (quantifierTaskLayoutTerminalBitBound bitBound) hstep
    omega
  exact hraw.trans (hnumeral.trans (by
    unfold taskConsHeadInstalledTermCodeEnvelope
    omega))

private theorem nativeOne_code_le_headEnvelope (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 1)).length <=
      taskConsHeadInstalledTermCodeEnvelope bitBound := by
  have hraw :
      (binaryTermCode (nativeNumeralTerm 1)).length <=
        quantifierTaskLayoutTerminalBitBound bitBound := by
    simp only [quantifierTaskLayoutTerminalBitBound]
    omega
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hnumeral :
      quantifierTaskLayoutTerminalBitBound bitBound <=
        binaryNumeralTermCodeEnvelope
          (quantifierTaskLayoutTerminalBitBound bitBound) := by
    unfold binaryNumeralTermCodeEnvelope
    have := Nat.mul_le_mul_right
      (quantifierTaskLayoutTerminalBitBound bitBound) hstep
    omega
  exact hraw.trans (hnumeral.trans (by
    unfold taskConsHeadInstalledTermCodeEnvelope
    omega))

private theorem binderSuccessor_code_le_headEnvelope
    (binderArity bitBound : Nat)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryTermCode (binderSuccessorTerm binderArity)).length <=
      taskConsHeadInstalledTermCodeEnvelope bitBound := by
  have hraw :=
    binderSuccessorTerm_code_length_le_tokenCellEnvelope binderArity
      bitBound hbinderSize
  have hbits :
      quantifierBinderSuccessorTokenCellBitBound bitBound <=
        quantifierTaskLayoutTerminalBitBound bitBound := by
    simp only [quantifierTaskLayoutTerminalBitBound]
    omega
  have hmono :
      binaryNumeralTermCodeEnvelope
          (quantifierBinderSuccessorTokenCellBitBound bitBound) <=
        binaryNumeralTermCodeEnvelope
          (quantifierTaskLayoutTerminalBitBound bitBound) := by
    have hmul := Nat.mul_le_mul_left binaryNumeralStepBudget hbits
    unfold binaryNumeralTermCodeEnvelope
    omega
  exact hraw.trans (hmono.trans (by
    unfold taskConsHeadInstalledTermCodeEnvelope
    omega))

theorem taskConsQuantifierHeadBody_freeVariables_eq_empty
    (tokenTable width tokenCount targetBoundary binderArity : Nat) :
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable
      width tokenCount targetBoundary (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity)
      (nativeNumeralTerm 0)).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
      tokenTable width tokenCount targetBoundary (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
  let body01 := terminal.bexsLTSucc
    (syntaxTaskListConsRowsClosedShift 1
      (shortBinaryNumeralTerm tokenCount))
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    exact
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_freeVariables_eq_empty
        tokenTable width tokenCount targetBoundary (nativeNumeralTerm 1)
        (binderSuccessorTerm binderArity) (nativeNumeralTerm 0) (by
          unfold nativeNumeralTerm
          simp [LO.FirstOrder.Semiterm.Operator.operator])
        (FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds.binderSuccessorTerm_freeVariables_eq_empty_fixed
          binderArity) (by
          unfold nativeNumeralTerm
          simp [LO.FirstOrder.Semiterm.Operator.operator])
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
    taskConsHeadCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount targetBoundary binderArity numericBound
      bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary 1 (binderArity + 1) 0) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate
          tokenTable width tokenCount targetBoundary 1 (binderArity + 1) 0
          (nativeNumeralTerm 1) (binderSuccessorTerm binderArity)
          (nativeNumeralTerm 0) (termValue_nativeNumeralTerm · 1)
          (termValue_binderSuccessorTerm · binderArity)
          (termValue_nativeNumeralTerm · 0) data) <=
      taskConsHeadInstalledPayloadEnvelope tokenCount numericBound
        bitBound := by
  let values : Fin 2 -> Nat := ![data.targetRight, data.targetLeft]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact data.targetRight_le
    · exact data.targetLeft_le
  let body :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
      tokenTable width tokenCount targetBoundary (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
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
          1 (binderArity + 1) 0 (nativeNumeralTerm 1)
          (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
          (termValue_nativeNumeralTerm · 1)
          (termValue_binderSuccessorTerm · binderArity)
          (termValue_nativeNumeralTerm · 0) data.layout))
  let terminal :
      CheckedHybridValuationBoundedFormulaCertificate headZeroValuation
        (body ⇜ fun coordinate =>
          shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_substitution_alignment
          tokenTable width tokenCount targetBoundary data.targetLeft
          data.targetRight (nativeNumeralTerm 1)
          (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)).symm)
      terminalParts
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        taskConsHeadTerminalPayloadEnvelope tokenCount numericBound
          bitBound := by
    simpa only [hybridFormulaStructuralPayloadBound, body, values,
      terminalParts, terminal] using
      (taskConsHeadTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount targetBoundary binderArity numericBound
        bitBound hwidthValue htokenCountValue htableSize hwidthSize
        htokenCountSize htargetBoundarySize hbinderSize data)
  have hbody :
      (binaryFormulaCode body).length <=
        taskConsHeadInstalledBodyCodeEnvelope bitBound := by
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
    · exact nativeOne_code_le_headEnvelope bitBound
    · exact binderSuccessor_code_le_headEnvelope binderArity bitBound
        hbinderSize
    · exact nativeZero_code_le_headEnvelope bitBound
  have hbodyClosed : body.freeVariables = ∅ :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_freeVariables_eq_empty
      tokenTable width tokenCount targetBoundary (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (nativeNumeralTerm 0) (by
        unfold nativeNumeralTerm
        simp [LO.FirstOrder.Semiterm.Operator.operator])
      (FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds.binderSuccessorTerm_freeVariables_eq_empty_fixed
        binderArity) (by
          unfold nativeNumeralTerm
          simp [LO.FirstOrder.Semiterm.Operator.operator])
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables headZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hbuilt :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values hvalues terminal
      (taskConsHeadTerminalPayloadEnvelope tokenCount numericBound bitBound)
      hterminal
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      headZeroValuation 0 tokenCount numericBound
      (taskConsHeadInstalledBodyCodeEnvelope bitBound) body values hvalues
      htokenCountValue hbody hcontext (le_refl
        (taskConsHeadTerminalPayloadEnvelope tokenCount numericBound
          bitBound))
  have hinstalled := hbuilt.trans hfixed
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast rfl
        (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
          hvalues terminal)) <= _
  simpa only [hybridFormulaStructuralPayloadBound,
    taskConsHeadInstalledPayloadEnvelope] using hinstalled

#print axioms
  taskConsQuantifierHeadBody_freeVariables_eq_empty
#print axioms
  taskConsHeadCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsHeadInstalledFullyFixedBounds
