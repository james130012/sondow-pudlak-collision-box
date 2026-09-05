import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutParserHeadFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullFixedBounds

/-!
# Fixed task-row certificate for the formula-transform initial parser head

This is the exact native `1` / short-binary binder / native `0` syntax used
inside the original formula-transform endpoint predicate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialParserTaskAtRowsFullyFixedBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutParserHeadFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayoutBinaryInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsBodyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsInstalledWitnessCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsWitnessFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsGuardFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullFixedBounds

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

private theorem fixedNumeralTerm_freeVariables_eq_empty_initialTask
    (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

def formulaTransformInitialParserTaskTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsTerminalPayloadEnvelope (fixedNumeralTerm 0)
    (binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
    numericBound bitBound

def formulaTransformInitialParserTaskWitnessPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsWitnessPayloadEnvelope
    (formulaTransformInitialParserTaskTerminalPayloadEnvelope numericBound
      bitBound)
    numericBound bitBound

def formulaTransformInitialParserTaskFullPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsFullPayloadEnvelope
    (repeatAtRowsGuardPayloadEnvelope numericBound bitBound)
    (formulaTransformInitialParserTaskWitnessPayloadEnvelope numericBound
      bitBound)

theorem
    formulaTransformInitialParserTaskTerminalCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count binderArity numericBound
      bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 1 binderArity 0)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatAtRowsTerminalCertificateOfGraph tokenTable width tokenCount
          boundaryTable count 0 1 binderArity 0 (fixedNumeralTerm 0)
          (fixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0) (by simp)
          (fun valuation => by simp [fixedNumeralTerm, termValue])
          (termValue_shortBinaryNumeralTerm · binderArity)
          (fun valuation => by simp [fixedNumeralTerm, termValue]) hgraph) <=
      formulaTransformInitialParserTaskTerminalPayloadEnvelope numericBound
        bitBound := by
  let left := Classical.choose hgraph.2
  have hleftData := Classical.choose_spec hgraph.2
  let right := Classical.choose hleftData.2
  have hrightData := Classical.choose_spec hleftData.2
  have hleftSize : Nat.size left <= bitBound :=
    (Nat.size_le_size hleftData.1).trans htokenCountSize
  have hrightSize : Nat.size right <= bitBound :=
    (Nat.size_le_size hrightData.1).trans htokenCountSize
  have hlayout :
      hybridFormulaStructuralPayloadBound
          (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
            tokenTable width tokenCount left right 1 binderArity 0
            (fixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
            (fixedNumeralTerm 0)
            (fun valuation => by simp [fixedNumeralTerm, termValue])
            (termValue_shortBinaryNumeralTerm · binderArity)
            (fun valuation => by simp [fixedNumeralTerm, termValue])
            hrightData.2.2.2) <=
        binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
    exact
      parserHeadTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount left right binderArity numericBound bitBound
        hwidthValue htokenCountValue htableSize hwidthSize htokenCountSize
        hleftSize hrightSize hbinderSize hrightData.2.2.2
  unfold formulaTransformInitialParserTaskTerminalPayloadEnvelope
  refine repeatAtRowsTerminalCertificate_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 0)
    (kind := 1) (binderArity := binderArity) (repeatCount := 0)
    (numericBound := numericBound) (bitBound := bitBound)
    (layoutResource :=
      binaryTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
    (indexTerm := fixedNumeralTerm 0) (kindTerm := fixedNumeralTerm 1)
    (binderArityTerm := shortBinaryNumeralTerm binderArity)
    (repeatCountTerm := fixedNumeralTerm 0)
    (hindexClosed :=
      fixedNumeralTerm_freeVariables_eq_empty_initialTask 0)
    (hkindClosed :=
      fixedNumeralTerm_freeVariables_eq_empty_initialTask 1)
    (hbinderClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
    (hrepeatClosed :=
      fixedNumeralTerm_freeVariables_eq_empty_initialTask 0)
    (hindexValue := by simp [fixedNumeralTerm, termValue])
    (hkindValue := fun valuation => by simp [fixedNumeralTerm, termValue])
    (hbinderValue :=
      fun valuation => termValue_shortBinaryNumeralTerm valuation binderArity)
    (hrepeatValue :=
      fun valuation => by simp [fixedNumeralTerm, termValue])
    (hgraph := hgraph) (hwidthValue := hwidthValue)
    (htokenCountValue := htokenCountValue) (hcountValue := hcountValue)
    (hboundarySize := hboundarySize) (htokenCountSize := htokenCountSize)
    (hcountSize := hcountSize) ?_
  simpa only [left, hleftData, right, hrightData] using hlayout

theorem
    formulaTransformInitialParserTaskInstalledWitness_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count binderArity numericBound
      bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 1 binderArity 0)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatAtRowsInstalledWitnessCertificateOfGraph tokenTable width
          tokenCount boundaryTable count 0 1 binderArity 0
          (fixedNumeralTerm 0) (fixedNumeralTerm 1)
          (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0) (by simp)
          (fun valuation => by simp [fixedNumeralTerm, termValue])
          (termValue_shortBinaryNumeralTerm · binderArity)
          (fun valuation => by simp [fixedNumeralTerm, termValue]) hgraph) <=
      formulaTransformInitialParserTaskWitnessPayloadEnvelope numericBound
        bitBound := by
  unfold formulaTransformInitialParserTaskWitnessPayloadEnvelope
  refine repeatAtRowsInstalledWitness_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 0)
    (kind := 1) (binderArity := binderArity) (repeatCount := 0)
    (terminalResource :=
      formulaTransformInitialParserTaskTerminalPayloadEnvelope numericBound
        bitBound)
    (numericBound := numericBound) (bitBound := bitBound)
    (indexTerm := fixedNumeralTerm 0) (kindTerm := fixedNumeralTerm 1)
    (binderArityTerm := shortBinaryNumeralTerm binderArity)
    (repeatCountTerm := fixedNumeralTerm 0)
    (hindexClosed :=
      fixedNumeralTerm_freeVariables_eq_empty_initialTask 0)
    (hkindClosed :=
      fixedNumeralTerm_freeVariables_eq_empty_initialTask 1)
    (hbinderClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
    (hrepeatClosed :=
      fixedNumeralTerm_freeVariables_eq_empty_initialTask 0)
    (hindexValue := by simp [fixedNumeralTerm, termValue])
    (hkindValue := fun valuation => by simp [fixedNumeralTerm, termValue])
    (hbinderValue :=
      fun valuation => termValue_shortBinaryNumeralTerm valuation binderArity)
    (hrepeatValue :=
      fun valuation => by simp [fixedNumeralTerm, termValue])
    (hgraph := hgraph) (htokenCountValue := htokenCountValue)
    (htableSize := htableSize) (hwidthSize := hwidthSize)
    (htokenCountSize := htokenCountSize) (hboundarySize := hboundarySize)
    (hcountSize := hcountSize)
    (hindexCode := fixedZero_code_le_repeatAtRowsTermEnvelope bitBound)
    (hkindCode := fixedOne_code_le_repeatAtRowsTermEnvelope bitBound)
    (hbinderCode :=
      shortBinary_code_le_repeatAtRowsTermEnvelope binderArity bitBound
        hbinderSize)
    (hrepeatCode := fixedZero_code_le_repeatAtRowsTermEnvelope bitBound) ?_
  exact
    formulaTransformInitialParserTaskTerminalCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount boundaryTable count binderArity numericBound
      bitBound hgraph hwidthValue htokenCountValue hcountValue htableSize
      hwidthSize htokenCountSize hboundarySize hcountSize hbinderSize

theorem
    formulaTransformInitialParserTaskFullCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count binderArity numericBound
      bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 1 binderArity 0)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
          boundaryTable count 0 1 binderArity 0 (fixedNumeralTerm 0)
          (fixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0) (by simp)
          (fun valuation => by simp [fixedNumeralTerm, termValue])
          (termValue_shortBinaryNumeralTerm · binderArity)
          (fun valuation => by simp [fixedNumeralTerm, termValue]) hgraph) <=
      formulaTransformInitialParserTaskFullPayloadEnvelope numericBound
        bitBound := by
  unfold formulaTransformInitialParserTaskFullPayloadEnvelope
  refine repeatAtRowsFullCertificate_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 0)
    (kind := 1) (binderArity := binderArity) (repeatCount := 0)
    (guardResource := repeatAtRowsGuardPayloadEnvelope numericBound bitBound)
    (witnessResource :=
      formulaTransformInitialParserTaskWitnessPayloadEnvelope numericBound
        bitBound)
    (indexTerm := fixedNumeralTerm 0) (kindTerm := fixedNumeralTerm 1)
    (binderArityTerm := shortBinaryNumeralTerm binderArity)
    (repeatCountTerm := fixedNumeralTerm 0)
    (hindexClosed :=
      fixedNumeralTerm_freeVariables_eq_empty_initialTask 0)
    (hkindClosed :=
      fixedNumeralTerm_freeVariables_eq_empty_initialTask 1)
    (hbinderClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
    (hrepeatClosed :=
      fixedNumeralTerm_freeVariables_eq_empty_initialTask 0)
    (hindexValue := by simp [fixedNumeralTerm, termValue])
    (hkindValue := fun valuation => by simp [fixedNumeralTerm, termValue])
    (hbinderValue :=
      fun valuation => termValue_shortBinaryNumeralTerm valuation binderArity)
    (hrepeatValue :=
      fun valuation => by simp [fixedNumeralTerm, termValue])
    (hgraph := hgraph) (hguard := ?_) (hwitness := ?_)
  · exact repeatTaskZeroGuard_structuralPayloadBound_le_fixed count numericBound
      bitBound hgraph.1 hcountSize
  · exact
      formulaTransformInitialParserTaskInstalledWitness_structuralPayloadBound_le_fixed
        tokenTable width tokenCount boundaryTable count binderArity numericBound
        bitBound hgraph hwidthValue htokenCountValue hcountValue htableSize
        hwidthSize htokenCountSize hboundarySize hcountSize hbinderSize

noncomputable def formulaTransformInitialParserTaskCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 1 binderArity 0) :
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount boundaryTable count (‘0’ : ValuationTerm)
        (‘1’ : ValuationTerm) (shortBinaryNumeralTerm binderArity)
        (‘0’ : ValuationTerm)) := by
  simpa [fixedNumeralTerm] using
    repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
      boundaryTable count 0 1 binderArity 0 (fixedNumeralTerm 0)
      (fixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0) (by simp)
      (fun valuation => by simp [fixedNumeralTerm, termValue])
      (termValue_shortBinaryNumeralTerm · binderArity)
      (fun valuation => by simp [fixedNumeralTerm, termValue]) hgraph

theorem
    formulaTransformInitialParserTaskCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count binderArity numericBound
      bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 1 binderArity 0)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (formulaTransformInitialParserTaskCertificateOfGraph tokenTable width
          tokenCount boundaryTable count binderArity hgraph) <=
      formulaTransformInitialParserTaskFullPayloadEnvelope numericBound
        bitBound := by
  unfold formulaTransformInitialParserTaskCertificateOfGraph
  exact
    formulaTransformInitialParserTaskFullCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount boundaryTable count binderArity numericBound
      bitBound hgraph hwidthValue htokenCountValue hcountValue htableSize
      hwidthSize htokenCountSize hboundarySize hcountSize hbinderSize

end FoundationCompactNumericListedDirectFormulaTransformInitialParserTaskAtRowsFullyFixedBounds
