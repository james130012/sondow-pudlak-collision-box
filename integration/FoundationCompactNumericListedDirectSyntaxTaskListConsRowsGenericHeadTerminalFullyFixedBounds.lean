import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericInstalledFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed three-leaf terminal for a generic task-list head

The two boundary entries retain their native unary index terms `0` and `1`.
Their syntax is charged directly.  The third leaf is the already fixed
generic task layout, not a witness-dependent public envelope.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadTerminalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
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
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate

private abbrev headZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

def taskConsGenericHeadEntryResource
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtTermCoordinate numericBound bitBound
        (binaryTermCode indexTerm).length))

def taskConsGenericHeadTerminalFormulaCodeEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  taskConsGenericHeadEntryResource (unaryNumeralTerm 0) numericBound bitBound +
    taskConsGenericHeadEntryResource (unaryNumeralTerm 1) numericBound bitBound +
    genericTaskLayoutFormulaCodeEnvelope tokenCount bitBound +
    2 * (binaryNatCode 4).length + 1

def taskConsGenericHeadTerminalPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (taskConsGenericHeadTerminalFormulaCodeEnvelope tokenCount numericBound bitBound)
    (taskConsGenericHeadEntryResource (unaryNumeralTerm 0) numericBound bitBound)
    (taskConsGenericHeadEntryResource (unaryNumeralTerm 1) numericBound bitBound)
    (genericTaskLayoutInstalledPayloadEnvelope numericBound bitBound)

private theorem unaryNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (unaryNumeralTerm value).freeVariables = ∅ := by
  unfold unaryNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem entryFormula_freeVariables_eq_empty
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

private theorem layoutFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start finish headKind headBinderArity
      headRepeatCount : Nat) :
    (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
      tokenCount start finish (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)).freeVariables = ∅ :=
  genericTaskLayoutFormula_freeVariables_eq_empty_fullyFixed tokenTable width
    tokenCount start finish headKind headBinderArity headRepeatCount

theorem taskConsGenericHeadTerminalCertificate_structuralPayloadBound_le_fullyFixed
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
    let leftCertificate :=
      compactFixedWidthEntryAtValuationExplicitHybridCertificate
        headZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
        (shortBinaryNumeralTerm data.targetLeft) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetLeft_entry)
    let rightCertificate :=
      compactFixedWidthEntryAtValuationExplicitHybridCertificate
        headZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
        (shortBinaryNumeralTerm data.targetRight) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetRight_entry)
    let layoutCertificate :=
      compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
        tokenTable width tokenCount data.targetLeft data.targetRight
        headKind headBinderArity headRepeatCount
        (shortBinaryNumeralTerm headKind)
        (shortBinaryNumeralTerm headBinderArity)
        (shortBinaryNumeralTerm headRepeatCount)
        (termValue_shortBinaryNumeralTerm · headKind)
        (termValue_shortBinaryNumeralTerm · headBinderArity)
        (termValue_shortBinaryNumeralTerm · headRepeatCount) data.layout
    let certificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        leftCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          rightCertificate layoutCertificate)
    hybridFormulaStructuralPayloadBound certificate <=
      taskConsGenericHeadTerminalPayloadEnvelope tokenCount numericBound bitBound := by
  dsimp only
  have hpositive : 1 <= tokenCount := by
    rcases data.layout with ⟨binderStart, countStart, hfirst, hsecond, hthird⟩
    exact Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hfirst.1)
  have hnumericPositive : 1 <= numericBound :=
    hpositive.trans htokenCountValue
  have hbitPositive : 1 <= bitBound := by
    have : Nat.size tokenCount <= bitBound := htokenCountSize
    have hsizePositive : 1 <= Nat.size tokenCount := by
      exact Nat.size_pos.mpr hpositive
    exact hsizePositive.trans this
  have hleftSize : Nat.size data.targetLeft <= bitBound :=
    (Nat.size_le_size data.targetLeft_le).trans htokenCountSize
  have hrightSize : Nat.size data.targetRight <= bitBound :=
    (Nat.size_le_size data.targetRight_le).trans htokenCountSize
  have hleft :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
      headZeroValuation targetBoundary tokenCount data.targetLeft
      (unaryNumeralTerm 0) numericBound bitBound
      (binaryTermCode (unaryNumeralTerm 0)).length htokenCountValue
      (by simpa only [termValue_unaryNumeralTerm] using
        (Nat.zero_le numericBound))
      (Nat.zero_le numericBound) htargetBoundarySize htokenCountSize
      (by simpa only [termValue_unaryNumeralTerm] using
        (show Nat.size 0 <= bitBound by
          simpa [Nat.size] using (Nat.zero_le bitBound)))
      hleftSize le_rfl (by
        rw [unaryNumeralTerm_freeVariables_eq_empty]
        simp) data.targetLeft_entry
  have hright :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
      headZeroValuation targetBoundary tokenCount data.targetRight
      (unaryNumeralTerm 1) numericBound bitBound
      (binaryTermCode (unaryNumeralTerm 1)).length htokenCountValue
      (by simpa only [termValue_unaryNumeralTerm] using hnumericPositive)
      (Nat.zero_le numericBound) htargetBoundarySize htokenCountSize
      (by
        rw [termValue_unaryNumeralTerm]
        simpa [Nat.size] using hbitPositive)
      hrightSize le_rfl (by
        rw [unaryNumeralTerm_freeVariables_eq_empty]
        simp) data.targetRight_entry
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
      tokenCount data.targetLeft data.targetRight (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
  have hlayoutResource :=
    genericTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount data.targetLeft data.targetRight headKind
      headBinderArity headRepeatCount numericBound bitBound hwidthValue
      htokenCountValue htableSize hwidthSize htokenCountSize hleftSize
      hrightSize hheadKindSize hheadBinderSize hheadRepeatSize data.layout
  have hlayoutCode :=
    genericTaskLayoutFormula_code_length_le_fullyFixed tokenTable width
      tokenCount data.targetLeft data.targetRight headKind headBinderArity
      headRepeatCount bitBound htableSize hwidthSize htokenCountSize hleftSize
      hrightSize hheadKindSize hheadBinderSize hheadRepeatSize
  have htotalCode :
      (binaryFormulaCode
        (leftFormula ⋏ (rightFormula ⋏ layoutFormula))).length <=
        taskConsGenericHeadTerminalFormulaCodeEnvelope tokenCount numericBound
          bitBound := by
    have hinner :
        (binaryFormulaCode (rightFormula ⋏ layoutFormula)).length <=
          (binaryFormulaCode rightFormula).length +
            (binaryFormulaCode layoutFormula).length +
            (binaryNatCode 4).length := by
      simp [binaryFormulaCode]
      omega
    have houter :
        (binaryFormulaCode
          (leftFormula ⋏ (rightFormula ⋏ layoutFormula))).length <=
          (binaryFormulaCode leftFormula).length +
            (binaryFormulaCode (rightFormula ⋏ layoutFormula)).length +
            (binaryNatCode 4).length := by
      simp [binaryFormulaCode]
      omega
    have hleftCode :
        (binaryFormulaCode leftFormula).length <=
          taskConsGenericHeadEntryResource (unaryNumeralTerm 0) numericBound
            bitBound := by
      simpa only [leftFormula, taskConsGenericHeadEntryResource] using hleft.2
    have hrightCode :
        (binaryFormulaCode rightFormula).length <=
          taskConsGenericHeadEntryResource (unaryNumeralTerm 1) numericBound
            bitBound := by
      simpa only [rightFormula, taskConsGenericHeadEntryResource] using hright.2
    have hlayoutCode' :
        (binaryFormulaCode layoutFormula).length <=
          genericTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
      simpa only [layoutFormula] using hlayoutCode
    unfold taskConsGenericHeadTerminalFormulaCodeEnvelope
    omega
  have htotalClosed :
      (leftFormula ⋏ (rightFormula ⋏ layoutFormula)).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_and]
    rw [show leftFormula.freeVariables = ∅ by
      exact entryFormula_freeVariables_eq_empty targetBoundary tokenCount
        data.targetLeft (unaryNumeralTerm 0)
          (unaryNumeralTerm_freeVariables_eq_empty 0)]
    rw [show rightFormula.freeVariables = ∅ by
      exact entryFormula_freeVariables_eq_empty targetBoundary tokenCount
        data.targetRight (unaryNumeralTerm 1)
          (unaryNumeralTerm_freeVariables_eq_empty 1)]
    rw [show layoutFormula.freeVariables = ∅ by
      exact layoutFormula_freeVariables_eq_empty tokenTable width tokenCount
        data.targetLeft data.targetRight headKind headBinderArity
        headRepeatCount]
    simp
  have hsyntaxPositive :
      1 <= taskConsGenericHeadTerminalFormulaCodeEnvelope tokenCount numericBound
        bitBound := by
    unfold taskConsGenericHeadTerminalFormulaCodeEnvelope
    omega
  have henvelope :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      headZeroValuation leftFormula rightFormula layoutFormula
      (taskConsGenericHeadEntryResource (unaryNumeralTerm 0) numericBound bitBound)
      (taskConsGenericHeadEntryResource (unaryNumeralTerm 1) numericBound bitBound)
      (genericTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
      (taskConsGenericHeadTerminalFormulaCodeEnvelope tokenCount numericBound
        bitBound) hsyntaxPositive htotalClosed htotalCode
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      headZeroValuation (shortBinaryNumeralTerm targetBoundary)
      (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
      (shortBinaryNumeralTerm data.targetLeft) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm] using data.targetLeft_entry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      headZeroValuation (shortBinaryNumeralTerm targetBoundary)
      (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
      (shortBinaryNumeralTerm data.targetRight) (by
        simpa only [termValue_shortBinaryNumeralTerm,
          termValue_unaryNumeralTerm] using data.targetRight_entry)
  let layoutCertificate :=
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
      tokenTable width tokenCount data.targetLeft data.targetRight
      headKind headBinderArity headRepeatCount
      (shortBinaryNumeralTerm headKind)
      (shortBinaryNumeralTerm headBinderArity)
      (shortBinaryNumeralTerm headRepeatCount)
      (termValue_shortBinaryNumeralTerm · headKind)
      (termValue_shortBinaryNumeralTerm · headBinderArity)
      (termValue_shortBinaryNumeralTerm · headRepeatCount) data.layout
  have hleftCertificate :
      hybridFormulaStructuralPayloadBound leftCertificate <=
        taskConsGenericHeadEntryResource (unaryNumeralTerm 0) numericBound
          bitBound := by
    have hopen :=
      compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
        headZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 0)
        (shortBinaryNumeralTerm data.targetLeft)
        (shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount) (by
          rw [unaryNumeralTerm_freeVariables_eq_empty]
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
        headZeroValuation (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount) (unaryNumeralTerm 1)
        (shortBinaryNumeralTerm data.targetRight)
        (shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount) (by
          rw [unaryNumeralTerm_freeVariables_eq_empty]
          simp)
        (shortBinaryNumeralTerm_freeVariables_eq_empty data.targetRight) (by
          simpa only [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetRight_entry)
    exact hopen.trans (by
      simpa only [taskConsGenericHeadEntryResource] using hright.1)
  let rightLayout :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      rightCertificate layoutCertificate
  have hrightLayout := transparentHybridConjunctionPayloadBound_le
    rightCertificate layoutCertificate _ _ hrightCertificate hlayoutResource
  let certificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate rightLayout
  have hcertificate := transparentHybridConjunctionPayloadBound_le
    leftCertificate rightLayout _ _ hleftCertificate hrightLayout
  change hybridFormulaStructuralPayloadBound certificate <= _
  exact hcertificate.trans (by
    simpa only [leftFormula, rightFormula, layoutFormula,
      taskConsGenericHeadTerminalPayloadEnvelope] using henvelope)

#print axioms
  taskConsGenericHeadTerminalCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadTerminalFullyFixedBounds
