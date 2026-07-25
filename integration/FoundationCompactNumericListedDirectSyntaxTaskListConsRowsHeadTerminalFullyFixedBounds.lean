import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutInstalledFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed three-leaf terminal for the quantifier task-list head

The two boundary entries retain their native unary index terms `0` and `1`.
Their syntax is charged directly.  The third leaf is the already fixed
quantifier task layout, not a witness-dependent public envelope.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsHeadTerminalFullyFixedBounds

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
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate

private abbrev headZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

def taskConsHeadEntryResource
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtTermCoordinate numericBound bitBound
        (binaryTermCode indexTerm).length))

def taskConsHeadTerminalFormulaCodeEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  taskConsHeadEntryResource (unaryNumeralTerm 0) numericBound bitBound +
    taskConsHeadEntryResource (unaryNumeralTerm 1) numericBound bitBound +
    quantifierTaskLayoutFormulaCodeEnvelope tokenCount bitBound +
    2 * (binaryNatCode 4).length + 1

def taskConsHeadTerminalPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (taskConsHeadTerminalFormulaCodeEnvelope tokenCount numericBound bitBound)
    (taskConsHeadEntryResource (unaryNumeralTerm 0) numericBound bitBound)
    (taskConsHeadEntryResource (unaryNumeralTerm 1) numericBound bitBound)
    (quantifierTaskLayoutInstalledPayloadEnvelope numericBound bitBound)

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
    (tokenTable width tokenCount start finish binderArity : Nat) :
    (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
      tokenCount start finish (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)).freeVariables =
        ∅ := by
  unfold compactSyntaxTaskDirectLayoutAtValuationTermsFormula
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    compactSyntaxTaskDirectLayoutDef.val
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm finish, nativeNumeralTerm 1,
      binderSuccessorTerm binderArity, nativeNumeralTerm 0] (by
        intro coordinate
        fin_cases coordinate
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty start
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty finish
        · unfold nativeNumeralTerm
          simp [LO.FirstOrder.Semiterm.Operator.operator]
        · exact
            FoundationCompactNumericListedDirectSyntaxTaskLayoutSuccessorTokenCellFixedBounds.binderSuccessorTerm_freeVariables_eq_empty_fixed
              binderArity
        · unfold nativeNumeralTerm
          simp [LO.FirstOrder.Semiterm.Operator.operator])

theorem taskConsHeadTerminalCertificate_structuralPayloadBound_le_fullyFixed
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
        1 (binderArity + 1) 0 (nativeNumeralTerm 1)
        (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
        (termValue_nativeNumeralTerm · 1)
        (termValue_binderSuccessorTerm · binderArity)
        (termValue_nativeNumeralTerm · 0) data.layout
    let certificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        leftCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          rightCertificate layoutCertificate)
    hybridFormulaStructuralPayloadBound certificate <=
      taskConsHeadTerminalPayloadEnvelope tokenCount numericBound bitBound := by
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
      tokenCount data.targetLeft data.targetRight (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
  have hlayoutResource :=
    quantifierTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount data.targetLeft data.targetRight binderArity
      numericBound bitBound hwidthValue htokenCountValue htableSize hwidthSize
      htokenCountSize hleftSize hrightSize hbinderSize data.layout
  have hlayoutCode :=
    quantifierTaskLayoutFormula_code_length_le_fullyFixed tokenTable width
      tokenCount data.targetLeft data.targetRight binderArity bitBound
      htableSize hwidthSize htokenCountSize hleftSize hrightSize hbinderSize
  have htotalCode :
      (binaryFormulaCode
        (leftFormula ⋏ (rightFormula ⋏ layoutFormula))).length <=
        taskConsHeadTerminalFormulaCodeEnvelope tokenCount numericBound
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
          taskConsHeadEntryResource (unaryNumeralTerm 0) numericBound
            bitBound := by
      simpa only [leftFormula, taskConsHeadEntryResource] using hleft.2
    have hrightCode :
        (binaryFormulaCode rightFormula).length <=
          taskConsHeadEntryResource (unaryNumeralTerm 1) numericBound
            bitBound := by
      simpa only [rightFormula, taskConsHeadEntryResource] using hright.2
    have hlayoutCode' :
        (binaryFormulaCode layoutFormula).length <=
          quantifierTaskLayoutFormulaCodeEnvelope tokenCount bitBound := by
      simpa only [layoutFormula] using hlayoutCode
    unfold taskConsHeadTerminalFormulaCodeEnvelope
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
        data.targetLeft data.targetRight binderArity]
    simp
  have hsyntaxPositive :
      1 <= taskConsHeadTerminalFormulaCodeEnvelope tokenCount numericBound
        bitBound := by
    unfold taskConsHeadTerminalFormulaCodeEnvelope
    omega
  have henvelope :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      headZeroValuation leftFormula rightFormula layoutFormula
      (taskConsHeadEntryResource (unaryNumeralTerm 0) numericBound bitBound)
      (taskConsHeadEntryResource (unaryNumeralTerm 1) numericBound bitBound)
      (quantifierTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
      (taskConsHeadTerminalFormulaCodeEnvelope tokenCount numericBound
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
      1 (binderArity + 1) 0 (nativeNumeralTerm 1)
      (binderSuccessorTerm binderArity) (nativeNumeralTerm 0)
      (termValue_nativeNumeralTerm · 1)
      (termValue_binderSuccessorTerm · binderArity)
      (termValue_nativeNumeralTerm · 0) data.layout
  have hleftCertificate :
      hybridFormulaStructuralPayloadBound leftCertificate <=
        taskConsHeadEntryResource (unaryNumeralTerm 0) numericBound
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
      simpa only [taskConsHeadEntryResource] using hleft.1)
  have hrightCertificate :
      hybridFormulaStructuralPayloadBound rightCertificate <=
        taskConsHeadEntryResource (unaryNumeralTerm 1) numericBound
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
      simpa only [taskConsHeadEntryResource] using hright.1)
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
      taskConsHeadTerminalPayloadEnvelope] using henvelope)

#print axioms
  taskConsHeadTerminalCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsHeadTerminalFullyFixedBounds
