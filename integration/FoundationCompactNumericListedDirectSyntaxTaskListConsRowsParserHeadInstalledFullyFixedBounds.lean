import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserHeadTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-! # Fully fixed witness installation for the parser formula-task head -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserHeadInstalledFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserHeadTerminalFullyFixedBounds

private abbrev parserHeadZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

private abbrev parserFixedNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
    value

def taskConsParserHeadInstalledTermCodeEnvelope (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (unaryNumeralTerm 0)).length +
    (binaryTermCode (unaryNumeralTerm 1)).length +
    (binaryTermCode (parserFixedNumeralTerm 0)).length +
    (binaryTermCode (parserFixedNumeralTerm 1)).length + 1

def taskConsParserHeadInstalledBodyCodeEnvelope (bitBound : Nat) : Nat :=
  syntaxTaskListConsHeadTerminalBodyCodeEnvelope
    (taskConsParserHeadInstalledTermCodeEnvelope bitBound)

def taskConsParserHeadInstalledPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (taskConsParserHeadInstalledBodyCodeEnvelope bitBound)
    (taskConsParserHeadTerminalPayloadEnvelope numericBound bitBound)

private theorem shortNumeral_code_le_parserHeadEnvelope
    (value bitBound : Nat) (hsize : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      taskConsParserHeadInstalledTermCodeEnvelope bitBound := by
  exact (binaryNumeralTerm_code_length_le_envelope value bitBound hsize).trans
    (by unfold taskConsParserHeadInstalledTermCodeEnvelope; omega)

private theorem unaryZero_code_le_parserHeadEnvelope (bitBound : Nat) :
    (binaryTermCode (unaryNumeralTerm 0)).length <=
      taskConsParserHeadInstalledTermCodeEnvelope bitBound := by
  unfold taskConsParserHeadInstalledTermCodeEnvelope
  omega

private theorem unaryOne_code_le_parserHeadEnvelope (bitBound : Nat) :
    (binaryTermCode (unaryNumeralTerm 1)).length <=
      taskConsParserHeadInstalledTermCodeEnvelope bitBound := by
  unfold taskConsParserHeadInstalledTermCodeEnvelope
  omega

private theorem fixedZero_code_le_parserHeadEnvelope (bitBound : Nat) :
    (binaryTermCode (parserFixedNumeralTerm 0)).length <=
      taskConsParserHeadInstalledTermCodeEnvelope bitBound := by
  unfold taskConsParserHeadInstalledTermCodeEnvelope
  omega

private theorem fixedOne_code_le_parserHeadEnvelope (bitBound : Nat) :
    (binaryTermCode (parserFixedNumeralTerm 1)).length <=
      taskConsParserHeadInstalledTermCodeEnvelope bitBound := by
  unfold taskConsParserHeadInstalledTermCodeEnvelope
  omega

theorem taskConsParserHeadBody_freeVariables_eq_empty
    (tokenTable width tokenCount targetBoundary binderArity : Nat) :
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable
      width tokenCount targetBoundary (parserFixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity)
      (parserFixedNumeralTerm 0)).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal tokenTable
      width tokenCount targetBoundary (parserFixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
  let body01 := terminal.bexsLTSucc
    (syntaxTaskListConsRowsClosedShift 1
      (shortBinaryNumeralTerm tokenCount))
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    exact
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_freeVariables_eq_empty
        tokenTable width tokenCount targetBoundary (parserFixedNumeralTerm 1)
        (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
        (by
          unfold parserFixedNumeralTerm
            FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          simp [LO.FirstOrder.Semiterm.Operator.operator])
        (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
        (by
          unfold parserFixedNumeralTerm
            FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
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
    taskConsParserHeadCertificate_structuralPayloadBound_le_fullyFixed
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
      tokenCount targetBoundary 1 binderArity 0) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate
          tokenTable width tokenCount targetBoundary 1 binderArity 0
          (parserFixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
          (parserFixedNumeralTerm 0)
          (fun valuation => by
            simp [parserFixedNumeralTerm,
              FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
              termValue])
          (termValue_shortBinaryNumeralTerm · binderArity)
          (fun valuation => by
            simp [parserFixedNumeralTerm,
              FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
              termValue])
          data) <=
      taskConsParserHeadInstalledPayloadEnvelope numericBound bitBound := by
  let values : Fin 2 -> Nat := ![data.targetRight, data.targetLeft]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact data.targetRight_le
    · exact data.targetLeft_le
  let body :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal tokenTable
      width tokenCount targetBoundary (parserFixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
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
        parserHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
        (shortBinaryNumeralTerm data.targetLeft) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetLeft_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          parserHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
          (shortBinaryNumeralTerm data.targetRight) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_unaryNumeralTerm] using data.targetRight_entry))
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount data.targetLeft data.targetRight 1
          binderArity 0 (parserFixedNumeralTerm 1)
          (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
          (fun valuation => by
            simp [parserFixedNumeralTerm,
              FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
              termValue])
          (termValue_shortBinaryNumeralTerm · binderArity)
          (fun valuation => by
            simp [parserFixedNumeralTerm,
              FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
              termValue])
          data.layout))
  let terminal :
      CheckedHybridValuationBoundedFormulaCertificate parserHeadZeroValuation
        (body ⇜ fun coordinate =>
          shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_substitution_alignment
          tokenTable width tokenCount targetBoundary data.targetLeft
          data.targetRight (parserFixedNumeralTerm 1)
          (shortBinaryNumeralTerm binderArity)
          (parserFixedNumeralTerm 0)).symm)
      terminalParts
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        taskConsParserHeadTerminalPayloadEnvelope numericBound bitBound := by
    simpa only [hybridFormulaStructuralPayloadBound, body, values,
      terminalParts, terminal] using
      (taskConsParserHeadTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount targetBoundary binderArity numericBound
        bitBound hwidthValue htokenCountValue htableSize hwidthSize
        htokenCountSize htargetBoundarySize hbinderSize data)
  have hbody :
      (binaryFormulaCode body).length <=
        taskConsParserHeadInstalledBodyCodeEnvelope bitBound := by
    apply
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_code_length_le_uniform
    · exact shortNumeral_code_le_parserHeadEnvelope tokenTable bitBound htableSize
    · exact shortNumeral_code_le_parserHeadEnvelope width bitBound hwidthSize
    · exact shortNumeral_code_le_parserHeadEnvelope tokenCount bitBound
        htokenCountSize
    · exact shortNumeral_code_le_parserHeadEnvelope targetBoundary bitBound
        htargetBoundarySize
    · exact unaryZero_code_le_parserHeadEnvelope bitBound
    · exact unaryOne_code_le_parserHeadEnvelope bitBound
    · exact fixedOne_code_le_parserHeadEnvelope bitBound
    · exact shortNumeral_code_le_parserHeadEnvelope binderArity bitBound
        hbinderSize
    · exact fixedZero_code_le_parserHeadEnvelope bitBound
  have hbodyClosed : body.freeVariables = ∅ :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsTerminal_freeVariables_eq_empty
      tokenTable width tokenCount targetBoundary (parserFixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
      (by
        unfold parserFixedNumeralTerm
          FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        simp [LO.FirstOrder.Semiterm.Operator.operator])
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (by
        unfold parserFixedNumeralTerm
          FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        simp [LO.FirstOrder.Semiterm.Operator.operator])
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables parserHeadZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hbuilt :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount body values hvalues terminal
      (taskConsParserHeadTerminalPayloadEnvelope numericBound bitBound)
      hterminal
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      parserHeadZeroValuation 0 tokenCount numericBound
      (taskConsParserHeadInstalledBodyCodeEnvelope bitBound) body values hvalues
      htokenCountValue hbody hcontext (le_refl
        (taskConsParserHeadTerminalPayloadEnvelope numericBound bitBound))
  have hinstalled := hbuilt.trans hfixed
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast rfl
        (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
          hvalues terminal)) <= _
  simpa only [hybridFormulaStructuralPayloadBound,
    taskConsParserHeadInstalledPayloadEnvelope] using hinstalled

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserHeadInstalledFullyFixedBounds
