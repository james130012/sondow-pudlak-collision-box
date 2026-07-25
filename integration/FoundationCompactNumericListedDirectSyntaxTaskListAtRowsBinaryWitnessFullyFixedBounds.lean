import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedTerminalFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryInstalledWitnessCertificate
import integration.FoundationCompactNumericListedDirectBinaryWitnessInstallationCoreBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fully fixed two-witness installation for a binary syntax-task row

The two cursor values supplied by the genuine `AtRows` graph are installed
below the real terminal certificate.  The open body code and valuation context
are discharged by the fully fixed binary body bounds.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryWitnessFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryBodyFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryInstalledWitnessCertificate
open FoundationCompactNumericListedDirectBinaryWitnessInstallationCoreBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

def syntaxTaskAtRowsBinaryWitnessPayloadAt
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope bitBound)
    (syntaxTaskAtRowsBinaryTerminalFullyFixedPayloadEnvelope
      indexTerm numericBound bitBound)

def syntaxTaskAtRowsBinaryWitnessPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  max
    (syntaxTaskAtRowsBinaryWitnessPayloadAt
      (nativeNumeralTerm 0) numericBound bitBound)
    (syntaxTaskAtRowsBinaryWitnessPayloadAt
      (nativeNumeralTerm 1) numericBound bitBound)

theorem
    syntaxTaskAtRowsBinaryInstalledWitness_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index binderArity
      numericBound bitBound : Nat)
    (hindexSelected : index < 2)
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
    hybridFormulaStructuralPayloadBound
        (syntaxTaskAtRowsBinaryInstalledWitnessCertificateOfGraph tokenTable
          width tokenCount boundaryTable count index binderArity hgraph) <=
      syntaxTaskAtRowsBinaryWitnessPayloadEnvelope numericBound bitBound := by
  let left := Classical.choose hgraph.2
  have hleftData := Classical.choose_spec hgraph.2
  let right := Classical.choose hleftData.2
  have hrightData := Classical.choose_spec hleftData.2
  let indexTerm : ValuationTerm := nativeNumeralTerm index
  let values : Fin 2 -> Nat := ![right, left]
  let body :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
      width tokenCount boundaryTable indexTerm (nativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact hrightData.1
    · exact hleftData.1
  let terminal :=
    syntaxTaskAtRowsBinaryTerminalCertificateOfGraph tokenTable width tokenCount
      boundaryTable count index binderArity hgraph
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        syntaxTaskAtRowsBinaryTerminalFullyFixedPayloadEnvelope indexTerm
          numericBound bitBound := by
    simpa only [terminal, indexTerm] using
      (syntaxTaskAtRowsBinaryTerminalCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount boundaryTable count index binderArity
        numericBound bitBound hgraph hwidthValue htokenCountValue hcountValue
        htableSize hwidthSize htokenCountSize hboundarySize hcountSize
        hbinderSize)
  have hbody :
      (binaryFormulaCode body).length <=
        syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope bitBound := by
    simpa only [body, indexTerm] using
      syntaxTaskAtRowsBinaryTerminalBody_code_length_le_fullyFixed tokenTable
        width tokenCount boundaryTable count index binderArity bitBound
        hindexSelected htableSize hwidthSize htokenCountSize hboundarySize
        hcountSize hbinderSize
  have hbodyClosed : body.freeVariables = ∅ := by
    simpa only [body, indexTerm] using
      syntaxTaskAtRowsBinaryTerminalBody_freeVariables_eq_empty tokenTable width
        tokenCount boundaryTable index binderArity
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables atRowsZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hinstalled :=
    installBinaryWitness_structuralPayloadBound_le_fullyFixed
      atRowsZeroValuation tokenCount numericBound
      (syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope bitBound)
      (syntaxTaskAtRowsBinaryTerminalFullyFixedPayloadEnvelope indexTerm
        numericBound bitBound)
      body values hvalues htokenCountValue hbody hcontext terminal hterminal
  have hnamed :
      hybridFormulaStructuralPayloadBound
          (syntaxTaskAtRowsBinaryInstalledWitnessCertificateOfGraph tokenTable
            width tokenCount boundaryTable count index binderArity hgraph) <=
        syntaxTaskAtRowsBinaryWitnessPayloadAt indexTerm numericBound
          bitBound := by
    change hybridFormulaStructuralPayloadBound
        (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
          hvalues terminal) <= _
    simpa only [syntaxTaskAtRowsBinaryWitnessPayloadAt] using hinstalled
  have hindexCases : index = 0 ∨ index = 1 := by omega
  rcases hindexCases with rfl | rfl
  · apply hnamed.trans
    unfold syntaxTaskAtRowsBinaryWitnessPayloadEnvelope
    exact Nat.le_max_left _ _
  · apply hnamed.trans
    unfold syntaxTaskAtRowsBinaryWitnessPayloadEnvelope
    exact Nat.le_max_right _ _

#print axioms
  syntaxTaskAtRowsBinaryInstalledWitness_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryWitnessFullyFixedBounds
