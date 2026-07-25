import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadTerminalFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutParserHeadFullyFixedBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fully fixed three-leaf terminal for the parser formula-task head -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserHeadTerminalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayoutParserHeadFullyFixedBounds
open FoundationCompactNumericListedDirectNativeNumeralTermCompatibility

private abbrev parserHeadZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

private abbrev parserFixedNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
    value

def taskConsParserHeadTerminalFormulaCodeEnvelope
    (numericBound bitBound : Nat) : Nat :=
  taskConsGenericHeadEntryResource (unaryNumeralTerm 0) numericBound bitBound +
    taskConsGenericHeadEntryResource (unaryNumeralTerm 1) numericBound bitBound +
    binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound +
    2 * (binaryNatCode 4).length + 1

def taskConsParserHeadTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (taskConsParserHeadTerminalFormulaCodeEnvelope numericBound bitBound)
    (taskConsGenericHeadEntryResource (unaryNumeralTerm 0) numericBound bitBound)
    (taskConsGenericHeadEntryResource (unaryNumeralTerm 1) numericBound bitBound)
    (binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound)

private theorem unaryNumeralTerm_freeVariables_eq_empty_parserHead
    (value : Nat) :
    (unaryNumeralTerm value).freeVariables = ∅ := by
  unfold unaryNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem parserHeadEntryFormula_freeVariables_eq_empty
    (table width value : Nat) (indexTerm : ValuationTerm)
    (hindex : indexTerm.freeVariables = ∅) :
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      indexTerm (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
  unfold compactFixedWidthEntryAtValuationFormula
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    compactFixedWidthEntryDef.val
    ![shortBinaryNumeralTerm table, shortBinaryNumeralTerm width,
      indexTerm, shortBinaryNumeralTerm value] (by
        intro coordinate
        fin_cases coordinate
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty table
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
        · exact hindex
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty value)

theorem
    taskConsParserHeadTerminalCertificate_structuralPayloadBound_le_fullyFixed
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
    let leftCertificate :=
      compactFixedWidthEntryAtValuationExplicitHybridCertificate
        parserHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
        (shortBinaryNumeralTerm data.targetLeft) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetLeft_entry)
    let rightCertificate :=
      compactFixedWidthEntryAtValuationExplicitHybridCertificate
        parserHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
        (shortBinaryNumeralTerm data.targetRight) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetRight_entry)
    let layoutCertificate :=
      compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
        tokenTable width tokenCount data.targetLeft data.targetRight 1
        binderArity 0 (parserFixedNumeralTerm 1)
        (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
        (fun valuation => by simp [parserFixedNumeralTerm,
          FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
          termValue])
        (termValue_shortBinaryNumeralTerm · binderArity)
        (fun valuation => by simp [parserFixedNumeralTerm,
          FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
          termValue]) data.layout
    let certificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction leftCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          rightCertificate layoutCertificate)
    hybridFormulaStructuralPayloadBound certificate <=
      taskConsParserHeadTerminalPayloadEnvelope numericBound bitBound := by
  dsimp only
  have hpositive : 1 <= tokenCount := by
    rcases data.layout with ⟨binderStart, countStart, hfirst, hsecond, hthird⟩
    exact Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hfirst.1)
  have hnumericPositive : 1 <= numericBound :=
    hpositive.trans htokenCountValue
  have hbitPositive : 1 <= bitBound := by
    exact le_trans (Nat.size_pos.mpr hpositive) htokenCountSize
  have hleftSize : Nat.size data.targetLeft <= bitBound :=
    (Nat.size_le_size data.targetLeft_le).trans htokenCountSize
  have hrightSize : Nat.size data.targetRight <= bitBound :=
    (Nat.size_le_size data.targetRight_le).trans htokenCountSize
  have hleft :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
      parserHeadZeroValuation targetBoundary tokenCount data.targetLeft
      (unaryNumeralTerm 0) numericBound bitBound
      (binaryTermCode (unaryNumeralTerm 0)).length htokenCountValue
      (by simpa only [termValue_unaryNumeralTerm] using
        (Nat.zero_le numericBound))
      (Nat.zero_le numericBound) htargetBoundarySize htokenCountSize
      (by simpa only [termValue_unaryNumeralTerm] using
        (show Nat.size 0 <= bitBound by
          simpa [Nat.size] using (Nat.zero_le bitBound)))
      hleftSize le_rfl (by
        rw [unaryNumeralTerm_freeVariables_eq_empty_parserHead]
        simp) data.targetLeft_entry
  have hright :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
      parserHeadZeroValuation targetBoundary tokenCount data.targetRight
      (unaryNumeralTerm 1) numericBound bitBound
      (binaryTermCode (unaryNumeralTerm 1)).length htokenCountValue
      (by simpa only [termValue_unaryNumeralTerm] using hnumericPositive)
      (Nat.zero_le numericBound) htargetBoundarySize htokenCountSize
      (by
        rw [termValue_unaryNumeralTerm]
        simpa [Nat.size] using hbitPositive)
      hrightSize le_rfl (by
        rw [unaryNumeralTerm_freeVariables_eq_empty_parserHead]
        simp) data.targetRight_entry
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      parserHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
      (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
      (shortBinaryNumeralTerm data.targetLeft) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm] using data.targetLeft_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      parserHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
      (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
      (shortBinaryNumeralTerm data.targetRight) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm] using data.targetRight_entry)
  let layoutCertificate :=
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
      tokenTable width tokenCount data.targetLeft data.targetRight 1 binderArity 0
      (parserFixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (parserFixedNumeralTerm 0)
      (fun valuation => by simp [parserFixedNumeralTerm,
        FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
        termValue])
      (termValue_shortBinaryNumeralTerm · binderArity)
      (fun valuation => by simp [parserFixedNumeralTerm,
        FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
        termValue]) data.layout
  have hleftCertificate :
      hybridFormulaStructuralPayloadBound leftCertificate <=
        taskConsGenericHeadEntryResource (unaryNumeralTerm 0) numericBound
          bitBound := by
    have hopen :=
      compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
        parserHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
        (shortBinaryNumeralTerm data.targetLeft)
        (shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount) (by
          rw [unaryNumeralTerm_freeVariables_eq_empty_parserHead]
          simp)
        (shortBinaryNumeralTerm_freeVariables_eq_empty data.targetLeft) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetLeft_entry)
    exact hopen.trans (by
      simpa only [taskConsGenericHeadEntryResource] using hleft.1)
  have hrightCertificate :
      hybridFormulaStructuralPayloadBound rightCertificate <=
        taskConsGenericHeadEntryResource (unaryNumeralTerm 1) numericBound
          bitBound := by
    have hopen :=
      compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
        parserHeadZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
        (shortBinaryNumeralTerm data.targetRight)
        (shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount) (by
          rw [unaryNumeralTerm_freeVariables_eq_empty_parserHead]
          simp)
        (shortBinaryNumeralTerm_freeVariables_eq_empty data.targetRight) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetRight_entry)
    exact hopen.trans (by
      simpa only [taskConsGenericHeadEntryResource] using hright.1)
  have hlayoutCertificate :
      hybridFormulaStructuralPayloadBound layoutCertificate <=
        binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
    exact
      (parserHeadTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount data.targetLeft data.targetRight binderArity
        numericBound bitBound hwidthValue htokenCountValue htableSize hwidthSize
        htokenCountSize hleftSize hrightSize hbinderSize data.layout)
  have hrightLayout :=
    transparentHybridConjunctionPayloadBound_le rightCertificate
      layoutCertificate _ _ hrightCertificate hlayoutCertificate
  have hparts :=
    transparentHybridConjunctionPayloadBound_le leftCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        rightCertificate layoutCertificate) _ _ hleftCertificate hrightLayout
  have hleftCode :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      leftCertificate).trans hleftCertificate
  have hrightCode :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      rightCertificate).trans hrightCertificate
  have hlayoutCode :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      layoutCertificate).trans hlayoutCertificate
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
    (shortBinaryNumeralTerm data.targetLeft)
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
    (shortBinaryNumeralTerm data.targetRight)
  let layoutFormula :=
    compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
      tokenCount data.targetLeft data.targetRight (parserFixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
  change (binaryFormulaCode leftFormula).length <=
    taskConsGenericHeadEntryResource (unaryNumeralTerm 0) numericBound bitBound
      at hleftCode
  change (binaryFormulaCode rightFormula).length <=
    taskConsGenericHeadEntryResource (unaryNumeralTerm 1) numericBound bitBound
      at hrightCode
  change (binaryFormulaCode layoutFormula).length <=
    binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound at hlayoutCode
  have hclosed :
      (leftFormula ⋏ (rightFormula ⋏ layoutFormula)).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_and, Finset.union_eq_empty,
      Finset.union_eq_empty]
    exact ⟨
      parserHeadEntryFormula_freeVariables_eq_empty targetBoundary tokenCount
        data.targetLeft (unaryNumeralTerm 0)
        (unaryNumeralTerm_freeVariables_eq_empty_parserHead 0),
      parserHeadEntryFormula_freeVariables_eq_empty targetBoundary tokenCount
        data.targetRight (unaryNumeralTerm 1)
        (unaryNumeralTerm_freeVariables_eq_empty_parserHead 1),
      by
        simpa only [layoutFormula, parserFixedNumeralTerm,
          fixedNumeralTerm_eq_nativeNumeralTerm] using
          binaryTaskLayoutFormula_freeVariables_eq_empty_fullyFixed tokenTable
            width tokenCount data.targetLeft data.targetRight binderArity⟩
  have hcode :
      (binaryFormulaCode (leftFormula ⋏ (rightFormula ⋏ layoutFormula))).length <=
        taskConsParserHeadTerminalFormulaCodeEnvelope numericBound bitBound := by
    simp only [binaryFormulaCode, List.length_append]
    unfold taskConsParserHeadTerminalFormulaCodeEnvelope
    omega
  have hgeneral :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      parserHeadZeroValuation leftFormula rightFormula layoutFormula
      (taskConsGenericHeadEntryResource (unaryNumeralTerm 0) numericBound
        bitBound)
      (taskConsGenericHeadEntryResource (unaryNumeralTerm 1) numericBound
        bitBound)
      (binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
      (taskConsParserHeadTerminalFormulaCodeEnvelope numericBound bitBound)
      (by unfold taskConsParserHeadTerminalFormulaCodeEnvelope; omega)
      hclosed hcode
  unfold taskConsParserHeadTerminalPayloadEnvelope
  exact hparts.trans hgeneral

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserHeadTerminalFullyFixedBounds
