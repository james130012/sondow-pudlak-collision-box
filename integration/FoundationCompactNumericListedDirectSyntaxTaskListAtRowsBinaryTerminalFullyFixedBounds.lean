import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryInstalledFullyFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fully fixed terminal for a binary syntax-task row lookup

The two genuine boundary-table entries and the genuine binary task layout are
bounded independently of the selected cursor witnesses and reassembled in the
original right-associated terminal formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryTerminalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

private theorem termValue_successorIndexTerm_binaryAtRows
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    termValue valuation (successorIndexTerm term) =
      termValue valuation term + 1 := by
  unfold successorIndexTerm
  rw [show
    (‘!!term + 1’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![term, (‘1’ : ValuationTerm)] by
        simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
          Rew.func, Matrix.fun_eq_vec_two]]
  calc
    termValue valuation
        (Semiterm.func Language.Add.add ![term, (‘1’ : ValuationTerm)]) =
      termValue valuation term +
        termValue valuation (‘1’ : ValuationTerm) :=
          termValue_add valuation ![term, (‘1’ : ValuationTerm)]
    _ = termValue valuation term + 1 := by
      have hone :
          termValue valuation (‘1’ : ValuationTerm) = 1 :=
        termValue_one valuation ![]
      rw [hone]

private theorem successorIndexTerm_freeVariables_eq_empty_binaryAtRows
    (term : ValuationTerm) (hterm : term.freeVariables = ∅) :
    (successorIndexTerm term).freeVariables = ∅ := by
  unfold successorIndexTerm
  rw [FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds.arithmeticAddTerm_freeVariables_eq_union,
    hterm]
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

def syntaxTaskAtRowsBinaryUniformEntryPayload
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
        numericBound bitBound))

def syntaxTaskAtRowsBinaryTerminalSyntaxEnvelope
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  let successorTerm := successorIndexTerm indexTerm
  syntaxTaskAtRowsBinaryUniformEntryPayload indexTerm numericBound bitBound +
    syntaxTaskAtRowsBinaryUniformEntryPayload successorTerm numericBound
      bitBound +
    binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound +
    2 * (binaryNatCode 4).length + 1

def syntaxTaskAtRowsBinaryTerminalFullyFixedPayloadEnvelope
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  let successorTerm := successorIndexTerm indexTerm
  let syntaxResource :=
    syntaxTaskAtRowsBinaryTerminalSyntaxEnvelope indexTerm numericBound
      bitBound
  let leftResource :=
    syntaxTaskAtRowsBinaryUniformEntryPayload indexTerm numericBound bitBound
  let rightResource :=
    syntaxTaskAtRowsBinaryUniformEntryPayload successorTerm numericBound
      bitBound
  let layoutResource :=
    binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound
  hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
      layoutResource)

theorem
    syntaxTaskAtRowsBinaryTerminalCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index binderArity
      numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    let left := Classical.choose hgraph.2
    let leftData := Classical.choose_spec hgraph.2
    let right := Classical.choose leftData.2
    let rightData := Classical.choose_spec leftData.2
    let indexTerm := nativeNumeralTerm index
    let values : Fin 2 -> Nat := ![right, left]
    let terminalParts :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount) indexTerm
          (shortBinaryNumeralTerm left) (by
            simpa only [left, leftData, right, rightData, indexTerm,
              termValue_shortBinaryNumeralTerm,
              termValue_nativeNumeralTerm] using rightData.2.1))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (successorIndexTerm indexTerm)
            (shortBinaryNumeralTerm right) (by
              simpa only [left, leftData, right, rightData, indexTerm,
                termValue_shortBinaryNumeralTerm,
                termValue_nativeNumeralTerm,
                termValue_successorIndexTerm_binaryAtRows] using
                  rightData.2.2.1))
          (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
            tokenTable width tokenCount left right 1 binderArity 0
            (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
            (nativeNumeralTerm 0) (termValue_nativeNumeralTerm · 1)
            (termValue_shortBinaryNumeralTerm · binderArity)
            (termValue_nativeNumeralTerm · 0) rightData.2.2.2))
    let terminal : CheckedHybridValuationBoundedFormulaCertificate
        atRowsZeroValuation
        ((compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
          width tokenCount boundaryTable indexTerm (nativeNumeralTerm 1)
          (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)) ⇜
            fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
      .cast (by
        have hvalueTerms :
            (fun coordinate : Fin 2 =>
              shortBinaryNumeralTerm (values coordinate)) =
              ![shortBinaryNumeralTerm right,
                shortBinaryNumeralTerm left] := by
          funext coordinate
          fin_cases coordinate <;> rfl
        rw [hvalueTerms]
        exact
          (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal_substitution_alignment
            tokenTable width tokenCount boundaryTable left right indexTerm
            (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
            (nativeNumeralTerm 0)).symm) terminalParts
    hybridFormulaStructuralPayloadBound terminal <=
      syntaxTaskAtRowsBinaryTerminalFullyFixedPayloadEnvelope indexTerm
        numericBound bitBound := by
  dsimp only
  let left := Classical.choose hgraph.2
  have hleftData := Classical.choose_spec hgraph.2
  let right := Classical.choose hleftData.2
  have hrightData := Classical.choose_spec hleftData.2
  have hleftLe := hleftData.1
  have hrightLe := hrightData.1
  have hleftEntry := hrightData.2.1
  have hrightEntry := hrightData.2.2.1
  have hlayout := hrightData.2.2.2
  let indexTerm : ValuationTerm := nativeNumeralTerm index
  let successorTerm := successorIndexTerm indexTerm
  let leftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) indexTerm
    (shortBinaryNumeralTerm left)
  let rightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm boundaryTable)
    (shortBinaryNumeralTerm tokenCount) successorTerm
    (shortBinaryNumeralTerm right)
  let layoutFormula :=
    compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
      tokenCount left right (nativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm left) (by
        simpa only [indexTerm, termValue_shortBinaryNumeralTerm,
          termValue_nativeNumeralTerm] using hleftEntry)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm right) (by
        simpa only [successorTerm, indexTerm,
          termValue_shortBinaryNumeralTerm, termValue_nativeNumeralTerm,
          termValue_successorIndexTerm_binaryAtRows] using hrightEntry)
  let layoutCertificate :=
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
      tokenTable width tokenCount left right 1 binderArity 0
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0) (termValue_nativeNumeralTerm · 1)
      (termValue_shortBinaryNumeralTerm · binderArity)
      (termValue_nativeNumeralTerm · 0) hlayout
  let leftResource :=
    syntaxTaskAtRowsBinaryUniformEntryPayload indexTerm numericBound bitBound
  let rightResource :=
    syntaxTaskAtRowsBinaryUniformEntryPayload successorTerm numericBound
      bitBound
  let layoutResource :=
    binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound
  let syntaxResource :=
    syntaxTaskAtRowsBinaryTerminalSyntaxEnvelope indexTerm numericBound
      bitBound
  have hleftSize : Nat.size left <= bitBound :=
    (Nat.size_le_size hleftLe).trans htokenCountSize
  have hrightSize : Nat.size right <= bitBound :=
    (Nat.size_le_size hrightLe).trans htokenCountSize
  have hindexValue : index <= numericBound :=
    (Nat.le_of_lt hgraph.1).trans hcountValue
  have hsuccessorValue : index + 1 <= numericBound :=
    (Nat.succ_le_iff.mpr hgraph.1).trans hcountValue
  have hindexSize : Nat.size index <= bitBound :=
    (Nat.size_le_size (Nat.le_of_lt hgraph.1)).trans hcountSize
  have hsuccessorSize : Nat.size (index + 1) <= bitBound :=
    (Nat.size_le_size (Nat.succ_le_iff.mpr hgraph.1)).trans hcountSize
  have hindexClosed : indexTerm.freeVariables ⊆ {0} := by
    dsimp only [indexTerm]
    rw [show (nativeNumeralTerm index).freeVariables = ∅ by
      unfold nativeNumeralTerm
      simp [LO.FirstOrder.Semiterm.Operator.operator]]
    simp
  have hsuccessorClosed : successorTerm.freeVariables ⊆ {0} := by
    have hempty :
        successorTerm.freeVariables = ∅ := by
      apply successorIndexTerm_freeVariables_eq_empty_binaryAtRows
      dsimp only [indexTerm]
      unfold nativeNumeralTerm
      simp [LO.FirstOrder.Semiterm.Operator.operator]
    rw [hempty]
    simp
  have hleft :
      hybridFormulaStructuralPayloadBound leftCertificate <= leftResource := by
    simpa only [leftCertificate, leftResource,
      syntaxTaskAtRowsBinaryUniformEntryPayload, indexTerm,
      termValue_nativeNumeralTerm] using
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        atRowsZeroValuation boundaryTable tokenCount left indexTerm
        numericBound bitBound htokenCountValue (by
          simpa only [indexTerm, termValue_nativeNumeralTerm] using
            hindexValue) (by
          exact Nat.zero_le numericBound)
        hboundarySize htokenCountSize (by
          simpa only [indexTerm, termValue_nativeNumeralTerm] using
            hindexSize) hleftSize hindexClosed (by
          simpa only [indexTerm, termValue_nativeNumeralTerm,
            termValue_shortBinaryNumeralTerm] using hleftEntry)
  have hright :
      hybridFormulaStructuralPayloadBound rightCertificate <=
        rightResource := by
    simpa only [rightCertificate, rightResource,
      syntaxTaskAtRowsBinaryUniformEntryPayload, successorTerm, indexTerm,
      termValue_nativeNumeralTerm, termValue_shortBinaryNumeralTerm,
      termValue_successorIndexTerm_binaryAtRows] using
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        atRowsZeroValuation boundaryTable tokenCount right successorTerm
        numericBound bitBound htokenCountValue (by
          simpa only [successorTerm, indexTerm,
            termValue_nativeNumeralTerm,
            termValue_successorIndexTerm_binaryAtRows] using
              hsuccessorValue) (by
          exact Nat.zero_le numericBound)
        hboundarySize htokenCountSize (by
          simpa only [successorTerm, indexTerm,
            termValue_nativeNumeralTerm,
            termValue_successorIndexTerm_binaryAtRows] using
              hsuccessorSize) hrightSize hsuccessorClosed (by
          simpa only [successorTerm, indexTerm,
            termValue_nativeNumeralTerm, termValue_shortBinaryNumeralTerm,
            termValue_successorIndexTerm_binaryAtRows] using hrightEntry)
  have hlayoutFixed :
      hybridFormulaStructuralPayloadBound layoutCertificate <=
        layoutResource := by
    dsimp only [layoutCertificate, layoutResource]
    exact
      binaryTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount left right binderArity numericBound
        bitBound hwidthValue htokenCountValue htableSize hwidthSize
        htokenCountSize hleftSize hrightSize hbinderSize hlayout
  have hleftClosed : leftFormula.freeVariables = ∅ := by
    dsimp only [leftFormula, indexTerm]
    unfold compactFixedWidthEntryAtValuationFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate
    all_goals
      first
      | apply shortBinaryNumeralTerm_freeVariables_eq_empty
      | unfold nativeNumeralTerm
        simp [LO.FirstOrder.Semiterm.Operator.operator]
  have hrightClosed : rightFormula.freeVariables = ∅ := by
    dsimp only [rightFormula]
    unfold compactFixedWidthEntryAtValuationFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
    · apply successorIndexTerm_freeVariables_eq_empty_binaryAtRows
      dsimp only [indexTerm]
      unfold nativeNumeralTerm
      simp [LO.FirstOrder.Semiterm.Operator.operator]
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty right
  have hlayoutClosed : layoutFormula.freeVariables = ∅ := by
    dsimp only [layoutFormula]
    exact binaryTaskLayoutFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount left right binderArity
  have hleftCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      leftCertificate
  have hrightCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      rightCertificate
  have hlayoutCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      layoutCertificate
  have hleftCodeBase :
      (binaryFormulaCode leftFormula).length <= leftResource := by
    simpa only [leftCertificate, leftFormula] using hleftCodeRaw.trans hleft
  have hrightCodeBase :
      (binaryFormulaCode rightFormula).length <= rightResource := by
    simpa only [rightCertificate, rightFormula] using
      hrightCodeRaw.trans hright
  have hrightCodeBaseNormalized :
      (binaryFormulaCode rightFormula).length <=
        syntaxTaskAtRowsBinaryUniformEntryPayload
          (successorIndexTerm indexTerm) numericBound bitBound := by
    simpa only [rightResource, successorTerm] using hrightCodeBase
  have hlayoutCodeBase :
      (binaryFormulaCode layoutFormula).length <= layoutResource := by
    simpa only [layoutCertificate, layoutFormula] using
      hlayoutCodeRaw.trans hlayoutFixed
  have hleftCode :
      (binaryFormulaCode leftFormula).length <= syntaxResource := by
    dsimp only [syntaxResource, leftResource, rightResource, layoutResource,
      successorTerm,
      syntaxTaskAtRowsBinaryTerminalSyntaxEnvelope]
    omega
  have hrightCode :
      (binaryFormulaCode rightFormula).length <= syntaxResource := by
    dsimp only [syntaxResource, leftResource, rightResource, layoutResource,
      successorTerm,
      syntaxTaskAtRowsBinaryTerminalSyntaxEnvelope]
    omega
  have hlayoutCode :
      (binaryFormulaCode layoutFormula).length <= syntaxResource := by
    dsimp only [syntaxResource, leftResource, rightResource, layoutResource,
      successorTerm,
      syntaxTaskAtRowsBinaryTerminalSyntaxEnvelope]
    omega
  have hrightTailRaw :=
    binaryFormulaCode_and_length_le_local rightFormula layoutFormula
  have hwholeRaw :=
    binaryFormulaCode_and_length_le_local leftFormula
      (rightFormula ⋏ layoutFormula)
  have hrightTailCode :
      (binaryFormulaCode (rightFormula ⋏ layoutFormula)).length <=
        syntaxResource := by
    dsimp only [syntaxResource, leftResource, rightResource, layoutResource,
      successorTerm,
      syntaxTaskAtRowsBinaryTerminalSyntaxEnvelope]
    omega
  have hwholeCode :
      (binaryFormulaCode
        (leftFormula ⋏ (rightFormula ⋏ layoutFormula))).length <=
          syntaxResource := by
    dsimp only [syntaxResource, leftResource, rightResource, layoutResource,
      successorTerm,
      syntaxTaskAtRowsBinaryTerminalSyntaxEnvelope]
    omega
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource, leftResource, rightResource, layoutResource,
      successorTerm,
      syntaxTaskAtRowsBinaryTerminalSyntaxEnvelope]
    omega
  let rightLayout :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      rightCertificate layoutCertificate
  have hrightLayoutTransparent :=
    transparentHybridConjunctionPayloadBound_le rightCertificate
      layoutCertificate _ _ hright hlayoutFixed
  have hrightLayoutGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      atRowsZeroValuation rightFormula layoutFormula rightResource
      layoutResource syntaxResource hpositive hrightClosed hlayoutClosed
      hrightCode hlayoutCode hrightTailCode
  have hrightLayout :
      hybridFormulaStructuralPayloadBound rightLayout <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
          layoutResource :=
    hrightLayoutTransparent.trans hrightLayoutGeneral
  have hrightTailClosed :
      (rightFormula ⋏ layoutFormula).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hrightClosed,
      hlayoutClosed]
    simp
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate rightLayout
  have hterminalTransparent :=
    transparentHybridConjunctionPayloadBound_le leftCertificate rightLayout
      _ _ hleft hrightLayout
  have hterminalGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      atRowsZeroValuation leftFormula (rightFormula ⋏ layoutFormula)
      leftResource
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
        layoutResource)
      syntaxResource hpositive hleftClosed hrightTailClosed hleftCode
      hrightTailCode hwholeCode
  have hterminalParts := hterminalTransparent.trans hterminalGeneral
  let values : Fin 2 -> Nat := ![right, left]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm right, shortBinaryNumeralTerm left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal : CheckedHybridValuationBoundedFormulaCertificate
      atRowsZeroValuation
      ((compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
        width tokenCount boundaryTable indexTerm (nativeNumeralTerm 1)
        (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal_substitution_alignment
          tokenTable width tokenCount boundaryTable left right indexTerm
          (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
          (nativeNumeralTerm 0)).symm) terminalParts
  unfold syntaxTaskAtRowsBinaryTerminalFullyFixedPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, indexTerm, successorTerm,
    leftResource, rightResource, layoutResource, syntaxResource,
    rightLayout, terminalParts, values, terminal] using hterminalParts

#print axioms
  syntaxTaskAtRowsBinaryTerminalCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryTerminalFullyFixedBounds
