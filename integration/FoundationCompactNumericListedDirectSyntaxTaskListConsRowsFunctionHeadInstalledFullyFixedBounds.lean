import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionHeadTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed installation of the function task-list head

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

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionHeadInstalledFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskLayoutFunctionTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionHeadTerminalFullyFixedBounds

private abbrev headZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

def taskConsFunctionHeadInstalledTermCodeEnvelope (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope
      (functionTaskLayoutTerminalBitBound bitBound) +
    (binaryTermCode (unaryNumeralTerm 0)).length +
    (binaryTermCode (unaryNumeralTerm 1)).length + 1

def taskConsFunctionHeadInstalledBodyCodeEnvelope (bitBound : Nat) : Nat :=
  syntaxTaskListConsHeadTerminalBodyCodeEnvelope
    (taskConsFunctionHeadInstalledTermCodeEnvelope bitBound)

def taskConsFunctionHeadInstalledPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (taskConsFunctionHeadInstalledBodyCodeEnvelope bitBound)
    (taskConsFunctionHeadTerminalPayloadEnvelope tokenCount numericBound bitBound)

private theorem shortNumeral_code_le_headEnvelope
    (value bitBound : Nat)
    (hsize : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      taskConsFunctionHeadInstalledTermCodeEnvelope bitBound := by
  have hbit : bitBound <= functionTaskLayoutTerminalBitBound bitBound := by
    simp only [functionTaskLayoutTerminalBitBound]
    omega
  exact (binaryNumeralTerm_code_length_le_envelope value
    (functionTaskLayoutTerminalBitBound bitBound) (hsize.trans hbit)).trans
      (by
        unfold taskConsFunctionHeadInstalledTermCodeEnvelope
        omega)

private theorem unaryZero_code_le_headEnvelope (bitBound : Nat) :
    (binaryTermCode (unaryNumeralTerm 0)).length <=
      taskConsFunctionHeadInstalledTermCodeEnvelope bitBound := by
  unfold taskConsFunctionHeadInstalledTermCodeEnvelope
  omega

private theorem unaryOne_code_le_headEnvelope (bitBound : Nat) :
    (binaryTermCode (unaryNumeralTerm 1)).length <=
      taskConsFunctionHeadInstalledTermCodeEnvelope bitBound := by
  unfold taskConsFunctionHeadInstalledTermCodeEnvelope
  omega

private theorem fixedTwo_code_le_headEnvelope (bitBound : Nat) :
    (binaryTermCode (fixedNumeralTerm 2)).length <=
      taskConsFunctionHeadInstalledTermCodeEnvelope bitBound := by
  have hraw :
      (binaryTermCode (fixedNumeralTerm 2)).length <=
        functionTaskLayoutTerminalBitBound bitBound := by
    simp only [functionTaskLayoutTerminalBitBound]
    omega
  have hstep : 1 <= binaryNumeralStepBudget := by decide
  have hnumeral :
      functionTaskLayoutTerminalBitBound bitBound <=
        binaryNumeralTermCodeEnvelope
          (functionTaskLayoutTerminalBitBound bitBound) := by
    unfold binaryNumeralTermCodeEnvelope
    have := Nat.mul_le_mul_right
      (functionTaskLayoutTerminalBitBound bitBound) hstep
    omega
  exact hraw.trans (hnumeral.trans (by
    unfold taskConsFunctionHeadInstalledTermCodeEnvelope
    omega))

@[simp] private theorem termValue_fixedNumeralTerm_functionHeadInstalled
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  simp [fixedNumeralTerm, termValue]

private theorem fixedNumeralTerm_freeVariables_eq_empty_installed
    (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

theorem taskConsFunctionHeadBody_freeVariables_eq_empty
    (tokenTable width tokenCount targetBoundary binderArity functionArity :
      Nat) :
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable
      width tokenCount targetBoundary (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
      tokenTable width tokenCount targetBoundary (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
  let body01 := terminal.bexsLTSucc
    (syntaxTaskListConsRowsClosedShift 1
      (shortBinaryNumeralTerm tokenCount))
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    exact
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_freeVariables_eq_empty
        tokenTable width tokenCount targetBoundary (fixedNumeralTerm 2)
        (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm functionArity)
        (fixedNumeralTerm_freeVariables_eq_empty_installed 2)
        (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
        (shortBinaryNumeralTerm_freeVariables_eq_empty functionArity)
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
    taskConsFunctionHeadCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount targetBoundary binderArity functionArity
      numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hfunctionSize : Nat.size functionArity <= bitBound)
    (data : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary 2 binderArity functionArity) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate
          tokenTable width tokenCount targetBoundary 2 binderArity functionArity
          (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm functionArity)
          (termValue_fixedNumeralTerm_functionHeadInstalled · 2)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_shortBinaryNumeralTerm · functionArity) data) <=
      taskConsFunctionHeadInstalledPayloadEnvelope tokenCount numericBound
        bitBound := by
  let values : Fin 2 -> Nat := ![data.targetRight, data.targetLeft]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact data.targetRight_le
    · exact data.targetLeft_le
  let body :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal
      tokenTable width tokenCount targetBoundary (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
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
          2 binderArity functionArity (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm functionArity)
          (termValue_fixedNumeralTerm_functionHeadInstalled · 2)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_shortBinaryNumeralTerm · functionArity) data.layout))
  let terminal :
      CheckedHybridValuationBoundedFormulaCertificate headZeroValuation
        (body ⇜ fun coordinate =>
          shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_substitution_alignment
          tokenTable width tokenCount targetBoundary data.targetLeft
          data.targetRight (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm functionArity)).symm)
      terminalParts
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        taskConsFunctionHeadTerminalPayloadEnvelope tokenCount numericBound
          bitBound := by
    simpa only [hybridFormulaStructuralPayloadBound, body, values,
      terminalParts, terminal] using
      (taskConsFunctionHeadTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount targetBoundary binderArity functionArity
        numericBound bitBound hwidthValue htokenCountValue htableSize
        hwidthSize htokenCountSize htargetBoundarySize hbinderSize
        hfunctionSize data)
  have hbody :
      (binaryFormulaCode body).length <=
        taskConsFunctionHeadInstalledBodyCodeEnvelope bitBound := by
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
    · exact fixedTwo_code_le_headEnvelope bitBound
    · exact shortNumeral_code_le_headEnvelope binderArity bitBound
        hbinderSize
    · exact shortNumeral_code_le_headEnvelope functionArity bitBound
        hfunctionSize
  have hbodyClosed : body.freeVariables = ∅ :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_freeVariables_eq_empty
      tokenTable width tokenCount targetBoundary (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
      (fixedNumeralTerm_freeVariables_eq_empty_installed 2)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty functionArity)
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables headZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hbuilt :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values hvalues terminal
      (taskConsFunctionHeadTerminalPayloadEnvelope tokenCount numericBound bitBound)
      hterminal
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      headZeroValuation 0 tokenCount numericBound
      (taskConsFunctionHeadInstalledBodyCodeEnvelope bitBound) body values hvalues
      htokenCountValue hbody hcontext (le_refl
        (taskConsFunctionHeadTerminalPayloadEnvelope tokenCount numericBound
          bitBound))
  have hinstalled := hbuilt.trans hfixed
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast rfl
        (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
          hvalues terminal)) <= _
  simpa only [hybridFormulaStructuralPayloadBound,
    taskConsFunctionHeadInstalledPayloadEnvelope] using hinstalled

#print axioms
  taskConsFunctionHeadBody_freeVariables_eq_empty
#print axioms
  taskConsFunctionHeadCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionHeadInstalledFullyFixedBounds
