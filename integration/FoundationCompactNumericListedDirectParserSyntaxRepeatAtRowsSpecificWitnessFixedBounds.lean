import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsWitnessFixedBounds

/-! # Fully fixed installed witnesses for the two exact Repeat task rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsSpecificWitnessFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsInstalledWitnessCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsSpecificTerminalFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsBodyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsWitnessFixedBounds

def repeatTaskZeroWitnessPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsWitnessPayloadEnvelope
    (repeatTaskZeroTerminalPayloadEnvelope numericBound bitBound)
    numericBound bitBound

def repeatTaskOneWitnessPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsWitnessPayloadEnvelope
    (repeatTaskOneTerminalPayloadEnvelope numericBound bitBound)
    numericBound bitBound

theorem repeatTaskZeroInstalledWitness_structuralPayloadBound_le_fixed
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
        (repeatAtRowsInstalledWitnessCertificateOfGraph tokenTable width
          tokenCount boundaryTable count 0 0 binderArity 0
          (fixedNumeralTerm 0) (fixedNumeralTerm 0)
          (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
          (by simp) (fun valuation => by simp)
          (fun valuation =>
            termValue_shortBinaryNumeralTerm valuation binderArity)
          (fun valuation => by simp) hgraph) <=
      repeatTaskZeroWitnessPayloadEnvelope numericBound bitBound := by
  unfold repeatTaskZeroWitnessPayloadEnvelope
  refine repeatAtRowsInstalledWitness_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 0)
    (kind := 0) (binderArity := binderArity) (repeatCount := 0)
    (terminalResource :=
      repeatTaskZeroTerminalPayloadEnvelope numericBound bitBound)
    (numericBound := numericBound) (bitBound := bitBound)
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
    (htokenCountValue := htokenCountValue) (htableSize := htableSize)
    (hwidthSize := hwidthSize) (htokenCountSize := htokenCountSize)
    (hboundarySize := hboundarySize) (hcountSize := hcountSize)
    (hindexCode := fixedZero_code_le_repeatAtRowsTermEnvelope bitBound)
    (hkindCode := fixedZero_code_le_repeatAtRowsTermEnvelope bitBound)
    (hbinderCode :=
      shortBinary_code_le_repeatAtRowsTermEnvelope binderArity bitBound
        hbinderSize)
    (hrepeatCode := fixedZero_code_le_repeatAtRowsTermEnvelope bitBound) ?_
  exact repeatTaskZeroTerminalCertificate_structuralPayloadBound_le_fixed
    tokenTable width tokenCount boundaryTable count binderArity numericBound
    bitBound hgraph hwidthValue htokenCountValue hcountValue htableSize
    hwidthSize htokenCountSize hboundarySize hcountSize hbinderSize

theorem repeatTaskOneInstalledWitness_structuralPayloadBound_le_fixed
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
        (repeatAtRowsInstalledWitnessCertificateOfGraph tokenTable width
          tokenCount boundaryTable count 1 2 binderArity decrementedCount
          (fixedNumeralTerm 1) (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm decrementedCount) (by simp)
          (fun valuation => by simp)
          (fun valuation =>
            termValue_shortBinaryNumeralTerm valuation binderArity)
          (fun valuation =>
            termValue_shortBinaryNumeralTerm valuation decrementedCount)
          hgraph) <=
      repeatTaskOneWitnessPayloadEnvelope numericBound bitBound := by
  unfold repeatTaskOneWitnessPayloadEnvelope
  refine repeatAtRowsInstalledWitness_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 1)
    (kind := 2) (binderArity := binderArity)
    (repeatCount := decrementedCount)
    (terminalResource :=
      repeatTaskOneTerminalPayloadEnvelope numericBound bitBound)
    (numericBound := numericBound) (bitBound := bitBound)
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
    (hgraph := hgraph) (htokenCountValue := htokenCountValue)
    (htableSize := htableSize) (hwidthSize := hwidthSize)
    (htokenCountSize := htokenCountSize) (hboundarySize := hboundarySize)
    (hcountSize := hcountSize)
    (hindexCode := fixedOne_code_le_repeatAtRowsTermEnvelope bitBound)
    (hkindCode := fixedTwo_code_le_repeatAtRowsTermEnvelope bitBound)
    (hbinderCode :=
      shortBinary_code_le_repeatAtRowsTermEnvelope binderArity bitBound
        hbinderSize)
    (hrepeatCode :=
      shortBinary_code_le_repeatAtRowsTermEnvelope decrementedCount bitBound
        hdecrementedSize) ?_
  exact repeatTaskOneTerminalCertificate_structuralPayloadBound_le_fixed
    tokenTable width tokenCount boundaryTable count binderArity decrementedCount
    numericBound bitBound hgraph hwidthValue htokenCountValue hcountValue
    htableSize hwidthSize htokenCountSize hboundarySize hcountSize hbinderSize
    hdecrementedSize

#print axioms repeatTaskZeroInstalledWitness_structuralPayloadBound_le_fixed
#print axioms repeatTaskOneInstalledWitness_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsSpecificWitnessFixedBounds
