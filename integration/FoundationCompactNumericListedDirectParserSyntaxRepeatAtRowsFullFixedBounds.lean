import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsGuardFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds

/-! # Fully fixed complete certificates for the two exact Repeat task rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsInstalledWitnessCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsBodyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsSpecificWitnessFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsGuardFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

def repeatAtRowsFullPayloadEnvelope
    (guardResource witnessResource : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (repeatClosedPairSyntaxResource guardResource witnessResource)
    guardResource witnessResource

theorem repeatAtRowsFullCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count index kind binderArity
      repeatCount guardResource witnessResource : Nat)
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
    (hguard :
      hybridFormulaStructuralPayloadBound
          (strictCertificate indexTerm (shortBinaryNumeralTerm count) (by
            simpa only [hindexValue, termValue_shortBinaryNumeralTerm] using
              hgraph.1)) <= guardResource)
    (hwitness :
      hybridFormulaStructuralPayloadBound
          (repeatAtRowsInstalledWitnessCertificateOfGraph tokenTable width
            tokenCount boundaryTable count index kind binderArity repeatCount
            indexTerm kindTerm binderArityTerm repeatCountTerm hindexValue
            hkindValue hbinderValue hrepeatValue hgraph) <= witnessResource) :
    hybridFormulaStructuralPayloadBound
        (repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
          boundaryTable count index kind binderArity repeatCount indexTerm
          kindTerm binderArityTerm repeatCountTerm hindexValue hkindValue
          hbinderValue hrepeatValue hgraph) <=
      repeatAtRowsFullPayloadEnvelope guardResource witnessResource := by
  let guardFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm count)”
  let witnessFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable
      width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
      repeatCountTerm
  let guardCertificate :=
    strictCertificate indexTerm (shortBinaryNumeralTerm count) (by
      simpa only [hindexValue, termValue_shortBinaryNumeralTerm] using hgraph.1)
  let installed :=
    repeatAtRowsInstalledWitnessCertificateOfGraph tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount indexTerm kindTerm
      binderArityTerm repeatCountTerm hindexValue hkindValue hbinderValue
      hrepeatValue hgraph
  let witnessCertificate :
      CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
        witnessFormula :=
    .cast (by
      unfold witnessFormula
        compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
      rw [explicitBoundedWitnessFormula_two_eq]) installed
  have hfullClosed :=
    repeatAtRowsFullFormula_freeVariables_eq_empty tokenTable width tokenCount
      boundaryTable count indexTerm kindTerm binderArityTerm repeatCountTerm
      hindexClosed hkindClosed hbinderClosed hrepeatClosed
  rw [compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment]
    at hfullClosed
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitFormula
    at hfullClosed
  have hguardClosed : guardFormula.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hfullClosed
    exact (Finset.union_eq_empty.mp hfullClosed).1
  have hwitnessClosed : witnessFormula.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hfullClosed
    exact (Finset.union_eq_empty.mp hfullClosed).2
  have hpair :=
    closedPairCertificate_structuralPayloadBound_le_fixed atRowsZeroValuation
      guardFormula witnessFormula guardCertificate witnessCertificate
      guardResource witnessResource hguardClosed hwitnessClosed
      (by simpa only [guardCertificate] using hguard)
      (by simpa only [witnessCertificate, installed,
        hybridFormulaStructuralPayloadBound] using hwitness)
  unfold repeatAtRowsFullCertificateOfGraph
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast _
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          guardCertificate witnessCertificate)) <= _
  simpa only [repeatAtRowsFullPayloadEnvelope, guardFormula, witnessFormula,
    guardCertificate, installed, witnessCertificate,
    hybridFormulaStructuralPayloadBound] using hpair

def repeatTaskZeroFullPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsFullPayloadEnvelope
    (repeatAtRowsGuardPayloadEnvelope numericBound bitBound)
    (repeatTaskZeroWitnessPayloadEnvelope numericBound bitBound)

def repeatTaskOneFullPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  repeatAtRowsFullPayloadEnvelope
    (repeatAtRowsGuardPayloadEnvelope numericBound bitBound)
    (repeatTaskOneWitnessPayloadEnvelope numericBound bitBound)

theorem repeatTaskZeroFullCertificate_structuralPayloadBound_le_fixed
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
        (repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
          boundaryTable count 0 0 binderArity 0 (fixedNumeralTerm 0)
          (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
          (fixedNumeralTerm 0) (by simp) (fun valuation => by simp)
          (fun valuation =>
            termValue_shortBinaryNumeralTerm valuation binderArity)
          (fun valuation => by simp) hgraph) <=
      repeatTaskZeroFullPayloadEnvelope numericBound bitBound := by
  unfold repeatTaskZeroFullPayloadEnvelope
  refine repeatAtRowsFullCertificate_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 0)
    (kind := 0) (binderArity := binderArity) (repeatCount := 0)
    (guardResource := repeatAtRowsGuardPayloadEnvelope numericBound bitBound)
    (witnessResource :=
      repeatTaskZeroWitnessPayloadEnvelope numericBound bitBound)
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
    (hguard := ?_) (hwitness := ?_)
  · exact repeatTaskZeroGuard_structuralPayloadBound_le_fixed count numericBound
      bitBound hgraph.1 hcountSize
  · exact repeatTaskZeroInstalledWitness_structuralPayloadBound_le_fixed
      tokenTable width tokenCount boundaryTable count binderArity numericBound
      bitBound hgraph hwidthValue htokenCountValue hcountValue htableSize
      hwidthSize htokenCountSize hboundarySize hcountSize hbinderSize

theorem repeatTaskOneFullCertificate_structuralPayloadBound_le_fixed
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
        (repeatAtRowsFullCertificateOfGraph tokenTable width tokenCount
          boundaryTable count 1 2 binderArity decrementedCount
          (fixedNumeralTerm 1) (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm decrementedCount) (by simp)
          (fun valuation => by simp)
          (fun valuation =>
            termValue_shortBinaryNumeralTerm valuation binderArity)
          (fun valuation =>
            termValue_shortBinaryNumeralTerm valuation decrementedCount)
          hgraph) <=
      repeatTaskOneFullPayloadEnvelope numericBound bitBound := by
  unfold repeatTaskOneFullPayloadEnvelope
  refine repeatAtRowsFullCertificate_structuralPayloadBound_le_fixed
    (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
    (boundaryTable := boundaryTable) (count := count) (index := 1)
    (kind := 2) (binderArity := binderArity)
    (repeatCount := decrementedCount)
    (guardResource := repeatAtRowsGuardPayloadEnvelope numericBound bitBound)
    (witnessResource :=
      repeatTaskOneWitnessPayloadEnvelope numericBound bitBound)
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
    (hgraph := hgraph) (hguard := ?_) (hwitness := ?_)
  · exact repeatTaskOneGuard_structuralPayloadBound_le_fixed count numericBound
      bitBound hgraph.1 hcountSize
  · exact repeatTaskOneInstalledWitness_structuralPayloadBound_le_fixed
      tokenTable width tokenCount boundaryTable count binderArity
      decrementedCount numericBound bitBound hgraph hwidthValue
      htokenCountValue hcountValue htableSize hwidthSize htokenCountSize
      hboundarySize hcountSize hbinderSize hdecrementedSize

#print axioms repeatTaskZeroFullCertificate_structuralPayloadBound_le_fixed
#print axioms repeatTaskOneFullCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsFullFixedBounds
