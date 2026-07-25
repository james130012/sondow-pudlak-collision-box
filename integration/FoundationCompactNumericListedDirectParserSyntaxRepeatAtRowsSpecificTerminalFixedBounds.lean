import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutZeroInstalledFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutFunctionInstalledFullyFixedBounds

/-! # Exact fixed terminal bounds for the two Repeat task rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsSpecificTerminalFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutZeroInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskLayoutFunctionInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreFixedBounds

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

def repeatTaskZeroTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsTerminalPayloadEnvelope (fixedNumeralTerm 0)
    (zeroTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
    numericBound bitBound

def repeatTaskOneTerminalPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsTerminalPayloadEnvelope (fixedNumeralTerm 1)
    (functionTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
    numericBound bitBound

theorem repeatTaskZeroTerminalCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count binderArity
      numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 0 0 binderArity 0)
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
          boundaryTable count 0 0 binderArity 0 (fixedNumeralTerm 0)
          (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0) (by simp) (fun valuation => by simp)
          (fun valuation =>
            termValue_shortBinaryNumeralTerm valuation binderArity)
          (fun valuation => by simp) hgraph) <=
      repeatTaskZeroTerminalPayloadEnvelope numericBound bitBound := by
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
            tokenTable width tokenCount left right 0 binderArity 0
            (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
            (fixedNumeralTerm 0) (fun valuation => by simp)
            (fun valuation =>
              termValue_shortBinaryNumeralTerm valuation binderArity)
            (fun valuation => by simp) hrightData.2.2.2) <=
        zeroTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
    simpa using
      (zeroTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount left right binderArity numericBound
        bitBound hwidthValue htokenCountValue htableSize hwidthSize
        htokenCountSize hleftSize hrightSize hbinderSize hrightData.2.2.2)
  unfold repeatTaskZeroTerminalPayloadEnvelope
  refine repeatAtRowsTerminalCertificate_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 0)
    (kind := 0) (binderArity := binderArity) (repeatCount := 0)
    (numericBound := numericBound) (bitBound := bitBound)
    (layoutResource :=
      zeroTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
    (indexTerm := fixedNumeralTerm 0) (kindTerm := fixedNumeralTerm 0)
    (binderArityTerm := shortBinaryNumeralTerm binderArity)
    (repeatCountTerm := fixedNumeralTerm 0)
    (hindexClosed := by simp) (hkindClosed := by simp)
    (hbinderClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
    (hrepeatClosed := by simp) (hindexValue := by simp)
    (hkindValue := fun valuation => by simp)
    (hbinderValue :=
      fun valuation => termValue_shortBinaryNumeralTerm valuation binderArity)
    (hrepeatValue := fun valuation => by simp) (hgraph := hgraph)
    (hwidthValue := hwidthValue) (htokenCountValue := htokenCountValue)
    (hcountValue := hcountValue) (hboundarySize := hboundarySize)
    (htokenCountSize := htokenCountSize) (hcountSize := hcountSize) ?_
  simpa only [left, hleftData, right, hrightData] using hlayout

theorem repeatTaskOneTerminalCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count binderArity
      decrementedCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count 1 2 binderArity decrementedCount)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hdecrementedSize : Nat.size decrementedCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (repeatAtRowsTerminalCertificateOfGraph tokenTable width tokenCount
          boundaryTable count 1 2 binderArity decrementedCount
          (fixedNumeralTerm 1) (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm decrementedCount) (by simp)
          (fun valuation => by simp)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_shortBinaryNumeralTerm · decrementedCount) hgraph) <=
      repeatTaskOneTerminalPayloadEnvelope numericBound bitBound := by
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
            tokenTable width tokenCount left right 2 binderArity
            decrementedCount (fixedNumeralTerm 2)
            (shortBinaryNumeralTerm binderArity)
            (shortBinaryNumeralTerm decrementedCount)
            (fun valuation => by simp)
            (termValue_shortBinaryNumeralTerm · binderArity)
            (termValue_shortBinaryNumeralTerm · decrementedCount)
            hrightData.2.2.2) <=
        functionTaskLayoutInstalledPayloadEnvelope numericBound bitBound := by
    simpa using
      (functionTaskLayoutExplicitHybridCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount left right binderArity decrementedCount
        numericBound bitBound hwidthValue htokenCountValue htableSize hwidthSize
        htokenCountSize hleftSize hrightSize hbinderSize hdecrementedSize
        hrightData.2.2.2)
  unfold repeatTaskOneTerminalPayloadEnvelope
  refine repeatAtRowsTerminalCertificate_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 1)
    (kind := 2) (binderArity := binderArity)
    (repeatCount := decrementedCount) (numericBound := numericBound)
    (bitBound := bitBound)
    (layoutResource :=
      functionTaskLayoutInstalledPayloadEnvelope numericBound bitBound)
    (indexTerm := fixedNumeralTerm 1) (kindTerm := fixedNumeralTerm 2)
    (binderArityTerm := shortBinaryNumeralTerm binderArity)
    (repeatCountTerm := shortBinaryNumeralTerm decrementedCount)
    (hindexClosed := by simp) (hkindClosed := by simp)
    (hbinderClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
    (hrepeatClosed :=
      shortBinaryNumeralTerm_freeVariables_eq_empty decrementedCount)
    (hindexValue := by simp) (hkindValue := fun valuation => by simp)
    (hbinderValue :=
      fun valuation => termValue_shortBinaryNumeralTerm valuation binderArity)
    (hrepeatValue :=
      fun valuation =>
        termValue_shortBinaryNumeralTerm valuation decrementedCount)
    (hgraph := hgraph) (hwidthValue := hwidthValue)
    (htokenCountValue := htokenCountValue) (hcountValue := hcountValue)
    (hboundarySize := hboundarySize)
    (htokenCountSize := htokenCountSize) (hcountSize := hcountSize) ?_
  simpa only [left, hleftData, right, hrightData] using hlayout

#print axioms repeatTaskZeroTerminalCertificate_structuralPayloadBound_le_fixed
#print axioms repeatTaskOneTerminalCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsSpecificTerminalFixedBounds
