import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedFullCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryWitnessFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryGuardFullyFixedBounds

/-!
# Fully fixed named components of a binary syntax-task row

This module closes the guard certificate, witness certificate, conjunction
code, component codes, and closedness against the irreducible formula names.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 65536
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedComponentsFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryBodyFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryWitnessFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryGuardFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFormulaNames
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedFullCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryInstalledWitnessCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

private theorem binaryFormulaCode_left_length_le_namedComponents
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_namedComponents
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem namedGuardCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index binderArity
      numericBound bitBound : Nat)
    (hindexSelected : index < 2)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0)
    (hcountSize : Nat.size count <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTaskAtRowsBinaryNamedGuardCertificateOfGraph tokenTable width
          tokenCount boundaryTable count index binderArity hgraph) <=
      syntaxTaskAtRowsBinaryGuardPayloadEnvelope numericBound bitBound := by
  unfold syntaxTaskAtRowsBinaryNamedGuardCertificateOfGraph
  change hybridFormulaStructuralPayloadBound
      (strictCertificate (nativeNumeralTerm index)
        (shortBinaryNumeralTerm count) _) <= _
  simpa only using
    strictCertificate_binaryIndex_structuralPayloadBound_le_fullyFixed count
      index numericBound bitBound hindexSelected hgraph.1 hcountSize

theorem namedWitnessCertificate_structuralPayloadBound_le_fullyFixed
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
        (syntaxTaskAtRowsBinaryNamedWitnessCertificateOfGraph tokenTable width
          tokenCount boundaryTable count index binderArity hgraph) <=
      syntaxTaskAtRowsBinaryWitnessPayloadEnvelope numericBound bitBound := by
  unfold syntaxTaskAtRowsBinaryNamedWitnessCertificateOfGraph
  change hybridFormulaStructuralPayloadBound
      (syntaxTaskAtRowsBinaryInstalledWitnessCertificateOfGraph tokenTable
        width tokenCount boundaryTable count index binderArity hgraph) <= _
  exact
    syntaxTaskAtRowsBinaryInstalledWitness_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount boundaryTable count index binderArity
      numericBound bitBound hindexSelected hgraph hwidthValue htokenCountValue
      hcountValue htableSize hwidthSize htokenCountSize hboundarySize
      hcountSize hbinderSize

theorem namedFormulaConjunction_code_length_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index binderArity
      bitBound : Nat)
    (hindexSelected : index < 2)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryFormulaCode
      (syntaxTaskAtRowsBinaryGuardFormula count index ⋏
        syntaxTaskAtRowsBinaryWitnessFormula tokenTable width tokenCount
          boundaryTable index binderArity)).length <=
      syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope bitBound := by
  rw [syntaxTaskAtRowsBinaryGuardFormula_eq,
    syntaxTaskAtRowsBinaryWitnessFormula_eq]
  have hfull :=
    syntaxTaskAtRowsBinaryFullFormula_code_length_le_fullyFixed tokenTable width
      tokenCount boundaryTable count index binderArity bitBound hindexSelected
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hbinderSize
  rw [compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment] at hfull
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitFormula at hfull
  exact hfull

theorem namedGuardFormula_code_length_le_fullSyntax
    (tokenTable width tokenCount boundaryTable count index binderArity
      bitBound : Nat)
    (hindexSelected : index < 2)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryFormulaCode
      (syntaxTaskAtRowsBinaryGuardFormula count index)).length <=
      syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope bitBound + 1 := by
  apply (binaryFormulaCode_left_length_le_namedComponents _ _).trans
  apply (namedFormulaConjunction_code_length_le_fullyFixed tokenTable width
    tokenCount boundaryTable count index binderArity bitBound hindexSelected
    htableSize hwidthSize htokenCountSize hboundarySize hcountSize
    hbinderSize).trans
  omega

theorem namedWitnessFormula_code_length_le_fullSyntax
    (tokenTable width tokenCount boundaryTable count index binderArity
      bitBound : Nat)
    (hindexSelected : index < 2)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryFormulaCode
      (syntaxTaskAtRowsBinaryWitnessFormula tokenTable width tokenCount
        boundaryTable index binderArity)).length <=
      syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope bitBound + 1 := by
  apply (binaryFormulaCode_right_length_le_namedComponents _ _).trans
  apply (namedFormulaConjunction_code_length_le_fullyFixed tokenTable width
    tokenCount boundaryTable count index binderArity bitBound hindexSelected
    htableSize hwidthSize htokenCountSize hboundarySize hcountSize
    hbinderSize).trans
  omega

theorem namedFormulaConjunction_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat) :
    (syntaxTaskAtRowsBinaryGuardFormula count index ⋏
      syntaxTaskAtRowsBinaryWitnessFormula tokenTable width tokenCount
        boundaryTable index binderArity).freeVariables = ∅ := by
  rw [syntaxTaskAtRowsBinaryGuardFormula_eq,
    syntaxTaskAtRowsBinaryWitnessFormula_eq]
  have hfull :=
    syntaxTaskAtRowsBinaryFullFormula_freeVariables_eq_empty tokenTable width
      tokenCount boundaryTable count index binderArity
  rw [compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment] at hfull
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitFormula at hfull
  exact hfull

theorem namedGuardFormula_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat) :
    (syntaxTaskAtRowsBinaryGuardFormula count index).freeVariables = ∅ := by
  have h := namedFormulaConjunction_freeVariables_eq_empty tokenTable width
    tokenCount boundaryTable count index binderArity
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at h
  exact (Finset.union_eq_empty.mp h).1

theorem namedWitnessFormula_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat) :
    (syntaxTaskAtRowsBinaryWitnessFormula tokenTable width tokenCount
      boundaryTable index binderArity).freeVariables = ∅ := by
  have h := namedFormulaConjunction_freeVariables_eq_empty tokenTable width
    tokenCount boundaryTable count index binderArity
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at h
  exact (Finset.union_eq_empty.mp h).2

#print axioms namedGuardCertificate_structuralPayloadBound_le_fullyFixed
#print axioms namedWitnessCertificate_structuralPayloadBound_le_fullyFixed
#print axioms namedFormulaConjunction_code_length_le_fullyFixed
#print axioms namedFormulaConjunction_freeVariables_eq_empty

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedComponentsFullyFixedBounds
