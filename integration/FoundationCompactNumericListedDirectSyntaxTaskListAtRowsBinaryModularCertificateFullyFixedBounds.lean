import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFullyFixedBounds

/-!
# Modular certificate for the original binary syntax-task row formula

This module installs the already bounded named guard-and-witness certificate
at the original project formula.  It does not normalize the older monolithic
certificate implementation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryModularCertificateFullyFixedBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFormulaNames
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedFullCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

theorem syntaxTaskAtRowsBinaryNamedFormula_eq_original
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat) :
    syntaxTaskAtRowsBinaryGuardFormula count index ⋏
        syntaxTaskAtRowsBinaryWitnessFormula tokenTable width tokenCount
          boundaryTable index binderArity =
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount boundaryTable count (nativeNumeralTerm index)
        (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
        (nativeNumeralTerm 0) := by
  rw [syntaxTaskAtRowsBinaryGuardFormula_eq,
    syntaxTaskAtRowsBinaryWitnessFormula_eq]
  rw [compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment]
  rfl

noncomputable def syntaxTaskAtRowsBinaryModularCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) :
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount boundaryTable count (nativeNumeralTerm index)
        (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
        (nativeNumeralTerm 0)) :=
  .cast
    (syntaxTaskAtRowsBinaryNamedFormula_eq_original tokenTable width tokenCount
      boundaryTable count index binderArity)
    (syntaxTaskAtRowsBinaryNamedFullCertificateOfGraph tokenTable width
      tokenCount boundaryTable count index binderArity hgraph)

theorem
    syntaxTaskAtRowsBinaryModularCertificate_structuralPayloadBound_le_fullyFixed
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
        (syntaxTaskAtRowsBinaryModularCertificateOfGraph tokenTable width
          tokenCount boundaryTable count index binderArity hgraph) <=
      syntaxTaskAtRowsBinaryFullPayloadEnvelope numericBound bitBound := by
  have h :=
    syntaxTaskAtRowsBinaryNamedFullCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount boundaryTable count index binderArity
      numericBound bitBound hindexSelected hgraph hwidthValue htokenCountValue
      hcountValue htableSize hwidthSize htokenCountSize hboundarySize hcountSize
      hbinderSize
  unfold syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph at h
  simpa only [syntaxTaskAtRowsBinaryModularCertificateOfGraph,
    hybridFormulaStructuralPayloadBound] using h

#print axioms syntaxTaskAtRowsBinaryNamedFormula_eq_original
#print axioms
  syntaxTaskAtRowsBinaryModularCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryModularCertificateFullyFixedBounds
