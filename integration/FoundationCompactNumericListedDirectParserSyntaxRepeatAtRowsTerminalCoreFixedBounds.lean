import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds

/-! # Shared fixed terminal bound for Repeat task-row lookups -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreFixedBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

def repeatAtRowsUniformEntryPayload
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
        numericBound bitBound))

def repeatAtRowsTerminalPayloadEnvelope
    (indexTerm : ValuationTerm)
    (layoutResource numericBound bitBound : Nat) : Nat :=
  let successorTerm := successorIndexTerm indexTerm
  let leftResource :=
    repeatAtRowsUniformEntryPayload indexTerm numericBound bitBound
  let rightResource :=
    repeatAtRowsUniformEntryPayload successorTerm numericBound bitBound
  let rightLayoutResource :=
    hybridConjunctionGeneralPayloadEnvelope
      (repeatClosedPairSyntaxResource rightResource layoutResource)
      rightResource layoutResource
  hybridConjunctionGeneralPayloadEnvelope
    (repeatClosedPairSyntaxResource leftResource rightLayoutResource)
    leftResource rightLayoutResource

theorem
    repeatAtRowsTerminalCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count index kind binderArity
      repeatCount numericBound bitBound layoutResource : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hkindClosed : kindTerm.freeVariables = ∅)
    (hbinderClosed : binderArityTerm.freeVariables = ∅)
    (hrepeatClosed : repeatCountTerm.freeVariables = ∅)
    (hindexValue : termValue atRowsZeroValuation indexTerm = index)
    (hkindValue : forall valuation, termValue valuation kindTerm = kind)
    (hbinderValue :
      forall valuation, termValue valuation binderArityTerm = binderArity)
    (hrepeatValue :
      forall valuation, termValue valuation repeatCountTerm = repeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hlayoutBound :
      let left := Classical.choose hgraph.2
      let leftData := Classical.choose_spec hgraph.2
      let right := Classical.choose leftData.2
      hybridFormulaStructuralPayloadBound
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount left right kind binderArity repeatCount
          kindTerm binderArityTerm repeatCountTerm hkindValue hbinderValue
          hrepeatValue (Classical.choose_spec leftData.2).2.2.2) <=
        layoutResource) :
    hybridFormulaStructuralPayloadBound
        (repeatAtRowsTerminalCertificateOfGraph tokenTable width tokenCount
          boundaryTable count index kind binderArity repeatCount indexTerm
          kindTerm binderArityTerm repeatCountTerm hindexValue hkindValue
          hbinderValue hrepeatValue hgraph) <=
      repeatAtRowsTerminalPayloadEnvelope indexTerm layoutResource
        numericBound bitBound := by
  let left := Classical.choose hgraph.2
  have hleftData := Classical.choose_spec hgraph.2
  let right := Classical.choose hleftData.2
  have hrightData := Classical.choose_spec hleftData.2
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
      tokenCount left right kindTerm binderArityTerm repeatCountTerm
  let leftCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm left) (by
        simpa only [termValue_shortBinaryNumeralTerm, hindexValue] using
          hrightData.2.1)
  let rightCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) successorTerm
      (shortBinaryNumeralTerm right) (by
        simpa only [successorTerm, termValue_shortBinaryNumeralTerm,
          hindexValue, termValue_successorIndexTerm_repeatAtRows] using
          hrightData.2.2.1)
  let layoutCertificate :=
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
      tokenTable width tokenCount left right kind binderArity repeatCount
      kindTerm binderArityTerm repeatCountTerm hkindValue hbinderValue
      hrepeatValue hrightData.2.2.2
  let leftResource :=
    repeatAtRowsUniformEntryPayload indexTerm numericBound bitBound
  let rightResource :=
    repeatAtRowsUniformEntryPayload successorTerm numericBound bitBound
  have hleftSize : Nat.size left <= bitBound :=
    (Nat.size_le_size hleftData.1).trans htokenCountSize
  have hrightSize : Nat.size right <= bitBound :=
    (Nat.size_le_size hrightData.1).trans htokenCountSize
  have hindexValueBound : index <= numericBound :=
    (Nat.le_of_lt hgraph.1).trans hcountValue
  have hsuccessorValueBound : index + 1 <= numericBound :=
    (Nat.succ_le_iff.mpr hgraph.1).trans hcountValue
  have hindexSize : Nat.size index <= bitBound :=
    (Nat.size_le_size (Nat.le_of_lt hgraph.1)).trans hcountSize
  have hsuccessorSize : Nat.size (index + 1) <= bitBound :=
    (Nat.size_le_size (Nat.succ_le_iff.mpr hgraph.1)).trans hcountSize
  have hleftResource :
      hybridFormulaStructuralPayloadBound leftCertificate <= leftResource := by
    simpa only [leftCertificate, leftResource,
      repeatAtRowsUniformEntryPayload, hindexValue] using
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        atRowsZeroValuation boundaryTable tokenCount left indexTerm
        numericBound bitBound htokenCountValue (by
          simpa only [hindexValue] using hindexValueBound)
        (Nat.zero_le numericBound) hboundarySize htokenCountSize (by
          simpa only [hindexValue] using hindexSize)
        hleftSize (by rw [hindexClosed]; simp) (by
          simpa only [hindexValue, termValue_shortBinaryNumeralTerm] using
            hrightData.2.1)
  have hrightResource :
      hybridFormulaStructuralPayloadBound rightCertificate <= rightResource := by
    simpa only [rightCertificate, rightResource,
      repeatAtRowsUniformEntryPayload, successorTerm, hindexValue,
      termValue_successorIndexTerm_repeatAtRows] using
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        atRowsZeroValuation boundaryTable tokenCount right successorTerm
        numericBound bitBound htokenCountValue (by
          simpa only [successorTerm, hindexValue,
            termValue_successorIndexTerm_repeatAtRows] using
            hsuccessorValueBound)
        (Nat.zero_le numericBound) hboundarySize htokenCountSize (by
          simpa only [successorTerm, hindexValue,
            termValue_successorIndexTerm_repeatAtRows] using hsuccessorSize)
        hrightSize (by
          rw [successorIndexTerm_freeVariables_eq_empty_repeatAtRows
            indexTerm hindexClosed]
          simp) (by
          simpa only [successorTerm, hindexValue,
            termValue_successorIndexTerm_repeatAtRows,
            termValue_shortBinaryNumeralTerm] using hrightData.2.2.1)
  have hleftClosed : leftFormula.freeVariables = ∅ := by
    unfold leftFormula compactFixedWidthEntryAtValuationFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
    · exact hindexClosed
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty left
  have hrightClosed : rightFormula.freeVariables = ∅ := by
    unfold rightFormula compactFixedWidthEntryAtValuationFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
    · exact successorIndexTerm_freeVariables_eq_empty_repeatAtRows indexTerm
        hindexClosed
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty right
  have hlayoutClosed : layoutFormula.freeVariables = ∅ := by
    unfold layoutFormula
      compactSyntaxTaskDirectLayoutAtValuationTermsFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty left
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty right
    · exact hkindClosed
    · exact hbinderClosed
    · exact hrepeatClosed
  have hrightPair :=
    closedPairCertificate_structuralPayloadBound_le_fixed
      atRowsZeroValuation rightFormula layoutFormula rightCertificate
      layoutCertificate rightResource layoutResource hrightClosed
      hlayoutClosed hrightResource hlayoutBound
  let rightPair :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      rightCertificate layoutCertificate
  let rightPairResource :=
    hybridConjunctionGeneralPayloadEnvelope
      (repeatClosedPairSyntaxResource rightResource layoutResource)
      rightResource layoutResource
  have houter :=
    closedPairCertificate_structuralPayloadBound_le_fixed
      atRowsZeroValuation leftFormula (rightFormula ⋏ layoutFormula)
      leftCertificate rightPair leftResource rightPairResource hleftClosed
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hrightClosed,
          hlayoutClosed]
        simp)
      hleftResource (by
        simpa only [rightPair, rightPairResource] using hrightPair)
  unfold repeatAtRowsTerminalCertificateOfGraph
    repeatAtRowsTerminalPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast _
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          leftCertificate rightPair)) <= _
  simpa only [leftFormula, rightFormula, layoutFormula, leftCertificate,
    rightCertificate, layoutCertificate, leftResource, rightResource,
    rightPair, rightPairResource, successorTerm,
    hybridFormulaStructuralPayloadBound] using houter

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreFixedBounds
