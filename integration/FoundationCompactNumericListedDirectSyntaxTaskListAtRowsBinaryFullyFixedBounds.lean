import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedComponentsFullyFixedBounds
import integration.FoundationCompactNumericListedDirectClosedHybridConjunctionCoreBounds

/-!
# Fully fixed binary syntax-task row

The named guard and installed two-witness certificate are combined through the
compiled closed-conjunction core.  Every component code, closedness, and
certificate-resource obligation is discharged by a fixed endpoint.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryBodyFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryWitnessFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryGuardFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFormulaNames
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedFullCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedComponentsFullyFixedBounds
open FoundationCompactNumericListedDirectClosedHybridConjunctionCoreBounds

def syntaxTaskAtRowsBinaryFullSyntaxEnvelope (bitBound : Nat) : Nat :=
  syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope bitBound + 1

def syntaxTaskAtRowsBinaryFullPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxTaskAtRowsBinaryFullSyntaxEnvelope bitBound)
    (syntaxTaskAtRowsBinaryGuardPayloadEnvelope numericBound bitBound)
    (syntaxTaskAtRowsBinaryWitnessPayloadEnvelope numericBound bitBound)

theorem
    syntaxTaskAtRowsBinaryNamedFullCertificate_structuralPayloadBound_le_fullyFixed
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
    syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph tokenTable width
        tokenCount boundaryTable count index binderArity hgraph <=
      syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound := by
  rw [syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph_eq_conjunction]
  let guard :=
    syntaxTaskAtRowsBinaryNamedGuardCertificateOfGraph tokenTable width
      tokenCount boundaryTable count index binderArity hgraph
  let witness :=
    syntaxTaskAtRowsBinaryNamedWitnessCertificateOfGraph tokenTable width
      tokenCount boundaryTable count index binderArity hgraph
  let guardFormula := syntaxTaskAtRowsBinaryGuardFormula count index
  let witnessFormula :=
    syntaxTaskAtRowsBinaryWitnessFormula tokenTable width tokenCount
      boundaryTable index binderArity
  let guardResource :=
    syntaxTaskAtRowsBinaryGuardPayloadEnvelope numericBound bitBound
  let witnessResource :=
    syntaxTaskAtRowsBinaryWitnessPayloadEnvelope numericBound bitBound
  let syntaxResource := syntaxTaskAtRowsBinaryFullSyntaxEnvelope bitBound
  have hguard :
      hybridFormulaStructuralPayloadBound guard <= guardResource := by
    simpa only [guard, guardResource] using
      namedGuardCertificate_structuralPayloadBound_le_fullyFixed tokenTable
        width tokenCount boundaryTable count index binderArity numericBound
        bitBound hindexSelected hgraph hcountSize
  have hwitness :
      hybridFormulaStructuralPayloadBound witness <= witnessResource := by
    simpa only [witness, witnessResource] using
      namedWitnessCertificate_structuralPayloadBound_le_fullyFixed tokenTable
        width tokenCount boundaryTable count index binderArity numericBound
        bitBound hindexSelected hgraph hwidthValue htokenCountValue hcountValue
        htableSize hwidthSize htokenCountSize hboundarySize hcountSize
        hbinderSize
  have hconjunctionCode :
      (binaryFormulaCode (guardFormula ⋏ witnessFormula)).length <=
        syntaxResource := by
    apply
      (namedFormulaConjunction_code_length_le_fullyFixed tokenTable width
        tokenCount boundaryTable count index binderArity bitBound
        hindexSelected htableSize hwidthSize htokenCountSize hboundarySize
        hcountSize hbinderSize).trans
    unfold syntaxResource syntaxTaskAtRowsBinaryFullSyntaxEnvelope
    omega
  have hguardCode :
      (binaryFormulaCode guardFormula).length <= syntaxResource := by
    simpa only [guardFormula, syntaxResource,
      syntaxTaskAtRowsBinaryFullSyntaxEnvelope] using
      namedGuardFormula_code_length_le_fullSyntax tokenTable width tokenCount
        boundaryTable count index binderArity bitBound hindexSelected
        htableSize hwidthSize htokenCountSize hboundarySize hcountSize
        hbinderSize
  have hwitnessCode :
      (binaryFormulaCode witnessFormula).length <= syntaxResource := by
    simpa only [witnessFormula, syntaxResource,
      syntaxTaskAtRowsBinaryFullSyntaxEnvelope] using
      namedWitnessFormula_code_length_le_fullSyntax tokenTable width tokenCount
        boundaryTable count index binderArity bitBound hindexSelected
        htableSize hwidthSize htokenCountSize hboundarySize hcountSize
        hbinderSize
  have hguardClosed : guardFormula.freeVariables = ∅ := by
    simpa only [guardFormula] using
      namedGuardFormula_freeVariables_eq_empty tokenTable width tokenCount
        boundaryTable count index binderArity
  have hwitnessClosed : witnessFormula.freeVariables = ∅ := by
    simpa only [witnessFormula] using
      namedWitnessFormula_freeVariables_eq_empty tokenTable width tokenCount
        boundaryTable count index binderArity
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource syntaxTaskAtRowsBinaryFullSyntaxEnvelope
    omega
  have hbound :=
    closedHybridConjunction_structuralPayloadBound_le_general guard witness
      guardResource witnessResource syntaxResource hguard hwitness hpositive
      hguardClosed hwitnessClosed hguardCode hwitnessCode hconjunctionCode
  simpa only [guard, witness, guardFormula, witnessFormula, guardResource,
    witnessResource, syntaxResource, syntaxTaskAtRowsBinaryFullPayloadEnvelope]
    using hbound

#print axioms
  syntaxTaskAtRowsBinaryNamedFullCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFullyFixedBounds
