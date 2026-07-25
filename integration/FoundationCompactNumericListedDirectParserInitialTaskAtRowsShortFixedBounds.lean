import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericInstalledFullyFixedBounds

/-!
# Fixed exact certificate for the parser's initial syntax task

The original initial-state formula uses short binary terms for the public task
kind, binder arity, and repeat count.  This module instantiates the generic
task-row compiler with those exact terms; no native-numeral formula transport
is used.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserInitialTaskAtRowsShortFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutGenericInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsBodyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsInstalledWitnessCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsWitnessFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsGuardFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullFixedBounds

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

def parserInitialTaskAtRowsTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsTerminalPayloadEnvelope (fixedNumeralTerm 0)
    (genericTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
    numericBound bitBound

def parserInitialTaskAtRowsWitnessPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsWitnessPayloadEnvelope
    (parserInitialTaskAtRowsTerminalPayloadEnvelope numericBound bitBound)
    numericBound bitBound

def parserInitialTaskAtRowsFullPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsFullPayloadEnvelope
    (repeatAtRowsGuardPayloadEnvelope numericBound bitBound)
    (parserInitialTaskAtRowsWitnessPayloadEnvelope numericBound bitBound)

theorem
    parserInitialTaskAtRowsTerminalCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count kind binderArity
      repeatCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 kind binderArity repeatCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hkindSize : Nat.size kind <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatAtRowsTerminalCertificateOfGraph tokenTable width tokenCount
          boundaryTable count 0 kind binderArity repeatCount
          (fixedNumeralTerm 0)
          (shortBinaryNumeralTerm kind)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm repeatCount) (by simp)
          (termValue_shortBinaryNumeralTerm · kind)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_shortBinaryNumeralTerm · repeatCount) hgraph) <=
      parserInitialTaskAtRowsTerminalPayloadEnvelope numericBound bitBound := by
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
            tokenTable width tokenCount left right kind binderArity repeatCount
            (shortBinaryNumeralTerm kind)
            (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm repeatCount)
            (termValue_shortBinaryNumeralTerm · kind)
            (termValue_shortBinaryNumeralTerm · binderArity)
            (termValue_shortBinaryNumeralTerm · repeatCount)
            hrightData.2.2.2) <=
        genericTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
    exact
      genericTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount left right kind binderArity repeatCount
        numericBound bitBound hwidthValue htokenCountValue htableSize hwidthSize
        htokenCountSize hleftSize hrightSize hkindSize hbinderSize
        hrepeatSize hrightData.2.2.2
  unfold parserInitialTaskAtRowsTerminalPayloadEnvelope
  refine repeatAtRowsTerminalCertificate_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 0)
    (kind := kind) (binderArity := binderArity)
    (repeatCount := repeatCount)
    (numericBound := numericBound) (bitBound := bitBound)
    (layoutResource :=
      genericTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
    (indexTerm := fixedNumeralTerm 0)
    (kindTerm := shortBinaryNumeralTerm kind)
    (binderArityTerm := shortBinaryNumeralTerm binderArity)
    (repeatCountTerm := shortBinaryNumeralTerm repeatCount)
    (hindexClosed := by simp)
    (hkindClosed := shortBinaryNumeralTerm_freeVariables_eq_empty kind)
    (hbinderClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
    (hrepeatClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty repeatCount)
    (hindexValue := by simp)
    (hkindValue := (termValue_shortBinaryNumeralTerm · kind))
    (hbinderValue := (termValue_shortBinaryNumeralTerm · binderArity))
    (hrepeatValue := (termValue_shortBinaryNumeralTerm · repeatCount))
    (hgraph := hgraph) (hwidthValue := hwidthValue)
    (htokenCountValue := htokenCountValue) (hcountValue := hcountValue)
    (hboundarySize := hboundarySize)
    (htokenCountSize := htokenCountSize) (hcountSize := hcountSize) ?_
  simpa only [left, hleftData, right, hrightData] using hlayout

theorem
    parserInitialTaskAtRowsInstalledWitness_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count kind binderArity
      repeatCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 kind binderArity repeatCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hkindSize : Nat.size kind <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatAtRowsInstalledWitnessCertificateOfGraph tokenTable width
          tokenCount boundaryTable count 0 kind binderArity repeatCount
          (fixedNumeralTerm 0) (shortBinaryNumeralTerm kind)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm repeatCount)
          (by simp) (termValue_shortBinaryNumeralTerm · kind)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_shortBinaryNumeralTerm · repeatCount) hgraph) <=
      parserInitialTaskAtRowsWitnessPayloadEnvelope numericBound bitBound := by
  unfold parserInitialTaskAtRowsWitnessPayloadEnvelope
  refine repeatAtRowsInstalledWitness_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 0)
    (kind := kind) (binderArity := binderArity)
    (repeatCount := repeatCount)
    (terminalResource :=
      parserInitialTaskAtRowsTerminalPayloadEnvelope numericBound bitBound)
    (numericBound := numericBound) (bitBound := bitBound)
    (indexTerm := fixedNumeralTerm 0)
    (kindTerm := shortBinaryNumeralTerm kind)
    (binderArityTerm := shortBinaryNumeralTerm binderArity)
    (repeatCountTerm := shortBinaryNumeralTerm repeatCount)
    (hindexClosed := by simp)
    (hkindClosed := shortBinaryNumeralTerm_freeVariables_eq_empty kind)
    (hbinderClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
    (hrepeatClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty repeatCount)
    (hindexValue := by simp)
    (hkindValue := (termValue_shortBinaryNumeralTerm · kind))
    (hbinderValue := (termValue_shortBinaryNumeralTerm · binderArity))
    (hrepeatValue := (termValue_shortBinaryNumeralTerm · repeatCount))
    (hgraph := hgraph) (htokenCountValue := htokenCountValue)
    (htableSize := htableSize) (hwidthSize := hwidthSize)
    (htokenCountSize := htokenCountSize) (hboundarySize := hboundarySize)
    (hcountSize := hcountSize)
    (hindexCode := fixedZero_code_le_repeatAtRowsTermEnvelope bitBound)
    (hkindCode :=
      shortBinary_code_le_repeatAtRowsTermEnvelope kind bitBound hkindSize)
    (hbinderCode :=
      shortBinary_code_le_repeatAtRowsTermEnvelope binderArity bitBound
        hbinderSize)
    (hrepeatCode :=
      shortBinary_code_le_repeatAtRowsTermEnvelope repeatCount bitBound
        hrepeatSize) ?_
  exact
    parserInitialTaskAtRowsTerminalCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount boundaryTable count kind binderArity
      repeatCount numericBound bitBound hgraph hwidthValue htokenCountValue
      hcountValue htableSize hwidthSize htokenCountSize hboundarySize hcountSize
      hkindSize hbinderSize hrepeatSize

theorem parserInitialTaskAtRowsFullCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count kind binderArity
      repeatCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 kind binderArity repeatCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hkindSize : Nat.size kind <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
          boundaryTable count 0 kind binderArity repeatCount
          (fixedNumeralTerm 0)
          (shortBinaryNumeralTerm kind)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm repeatCount) (by simp)
          (termValue_shortBinaryNumeralTerm · kind)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_shortBinaryNumeralTerm · repeatCount) hgraph) <=
      parserInitialTaskAtRowsFullPayloadEnvelope numericBound bitBound := by
  unfold parserInitialTaskAtRowsFullPayloadEnvelope
  refine repeatAtRowsFullCertificate_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 0)
    (kind := kind) (binderArity := binderArity)
    (repeatCount := repeatCount)
    (guardResource := repeatAtRowsGuardPayloadEnvelope numericBound bitBound)
    (witnessResource :=
      parserInitialTaskAtRowsWitnessPayloadEnvelope numericBound bitBound)
    (indexTerm := fixedNumeralTerm 0)
    (kindTerm := shortBinaryNumeralTerm kind)
    (binderArityTerm := shortBinaryNumeralTerm binderArity)
    (repeatCountTerm := shortBinaryNumeralTerm repeatCount)
    (hindexClosed := by simp)
    (hkindClosed := shortBinaryNumeralTerm_freeVariables_eq_empty kind)
    (hbinderClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
    (hrepeatClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty repeatCount)
    (hindexValue := by simp)
    (hkindValue := (termValue_shortBinaryNumeralTerm · kind))
    (hbinderValue := (termValue_shortBinaryNumeralTerm · binderArity))
    (hrepeatValue := (termValue_shortBinaryNumeralTerm · repeatCount))
    (hgraph := hgraph) (hguard := ?_) (hwitness := ?_)
  · exact repeatTaskZeroGuard_structuralPayloadBound_le_fixed count numericBound
      bitBound hgraph.1 hcountSize
  · exact
      parserInitialTaskAtRowsInstalledWitness_structuralPayloadBound_le_fixed
        tokenTable width tokenCount boundaryTable count kind binderArity
        repeatCount numericBound bitBound hgraph hwidthValue htokenCountValue
        hcountValue htableSize hwidthSize htokenCountSize hboundarySize
        hcountSize hkindSize hbinderSize hrepeatSize

theorem parserInitialTaskAtRowsTermsFormula_eq_exact
    (tokenTable width tokenCount boundaryTable count kind binderArity
      repeatCount : Nat) :
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount boundaryTable count (fixedNumeralTerm 0)
        (shortBinaryNumeralTerm kind)
        (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm repeatCount) =
      compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula tokenTable
        width tokenCount boundaryTable count kind binderArity repeatCount
        (‘0’ : ValuationTerm) := by
  simp [compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula,
    fixedNumeralTerm]

noncomputable def parserInitialTaskAtRowsExactCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count kind binderArity
      repeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 kind binderArity repeatCount) :
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (compactAdditiveSyntaxTaskListAtRowsAtValuationIndexFormula tokenTable
        width tokenCount boundaryTable count kind binderArity repeatCount
        (‘0’ : ValuationTerm)) := by
  exact .cast
    (parserInitialTaskAtRowsTermsFormula_eq_exact tokenTable width tokenCount
      boundaryTable count kind binderArity repeatCount)
    (repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
      boundaryTable count 0 kind binderArity repeatCount
      (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm kind)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm repeatCount) (by simp)
      (termValue_shortBinaryNumeralTerm · kind)
      (termValue_shortBinaryNumeralTerm · binderArity)
      (termValue_shortBinaryNumeralTerm · repeatCount) hgraph)

theorem
    parserInitialTaskAtRowsExactCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count kind binderArity
      repeatCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 kind binderArity repeatCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hkindSize : Nat.size kind <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (parserInitialTaskAtRowsExactCertificateOfGraph tokenTable width
          tokenCount boundaryTable count kind binderArity repeatCount
          hgraph) <=
      parserInitialTaskAtRowsFullPayloadEnvelope numericBound bitBound := by
  simpa only [parserInitialTaskAtRowsExactCertificateOfGraph,
    hybridFormulaStructuralPayloadBound] using
    (parserInitialTaskAtRowsFullCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount boundaryTable count kind binderArity
      repeatCount numericBound bitBound hgraph hwidthValue htokenCountValue
      hcountValue htableSize hwidthSize htokenCountSize hboundarySize hcountSize
      hkindSize hbinderSize hrepeatSize)

#print axioms
  parserInitialTaskAtRowsTermsFormula_eq_exact
#print axioms
  parserInitialTaskAtRowsExactCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserInitialTaskAtRowsShortFixedBounds
