import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFormulaNames
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryInstalledWitnessCertificate

/-!
# Named complete binary syntax-task row certificate

The guard and installed witness are cast to the irreducible formula names and
combined once.  Quantitative proofs can import this compiled dependent object.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedFullCertificate

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryInstalledWitnessCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryFormulaNames
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

noncomputable def syntaxTaskAtRowsBinaryNamedWitnessCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) :
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (syntaxTaskAtRowsBinaryWitnessFormula tokenTable width tokenCount
        boundaryTable index binderArity) := by
  let installed :=
    syntaxTaskAtRowsBinaryInstalledWitnessCertificateOfGraph tokenTable width
      tokenCount boundaryTable count index binderArity hgraph
  exact .cast (by
    rw [syntaxTaskAtRowsBinaryWitnessFormula_eq]
    unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
    rw [explicitBoundedWitnessFormula_two_eq]) installed

noncomputable def syntaxTaskAtRowsBinaryNamedGuardCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) :
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (syntaxTaskAtRowsBinaryGuardFormula count index) := by
  let indexTerm : ValuationTerm := nativeNumeralTerm index
  let guardRaw :=
    strictCertificate indexTerm (shortBinaryNumeralTerm count) (by
      simpa only [indexTerm, termValue_nativeNumeralTerm,
        termValue_shortBinaryNumeralTerm] using hgraph.1)
  exact .cast (by
    simpa only [indexTerm] using
      (syntaxTaskAtRowsBinaryGuardFormula_eq count index).symm) guardRaw

noncomputable def syntaxTaskAtRowsBinaryNamedFullCertificateRawOfGraph
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) :
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (syntaxTaskAtRowsBinaryGuardFormula count index ⋏
        syntaxTaskAtRowsBinaryWitnessFormula tokenTable width tokenCount
          boundaryTable index binderArity) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (syntaxTaskAtRowsBinaryNamedGuardCertificateOfGraph tokenTable width
      tokenCount boundaryTable count index binderArity hgraph)
    (syntaxTaskAtRowsBinaryNamedWitnessCertificateOfGraph tokenTable width
      tokenCount boundaryTable count index binderArity hgraph)

@[irreducible] noncomputable def
    syntaxTaskAtRowsBinaryNamedFullCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) :
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (syntaxTaskAtRowsBinaryGuardFormula count index ⋏
        syntaxTaskAtRowsBinaryWitnessFormula tokenTable width tokenCount
          boundaryTable index binderArity) :=
  syntaxTaskAtRowsBinaryNamedFullCertificateRawOfGraph tokenTable width
    tokenCount boundaryTable count index binderArity hgraph

theorem syntaxTaskAtRowsBinaryNamedFullCertificateOfGraph_eq_raw
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) :
    syntaxTaskAtRowsBinaryNamedFullCertificateOfGraph tokenTable width
        tokenCount boundaryTable count index binderArity hgraph =
      syntaxTaskAtRowsBinaryNamedFullCertificateRawOfGraph tokenTable width
        tokenCount boundaryTable count index binderArity hgraph := by
  unfold syntaxTaskAtRowsBinaryNamedFullCertificateOfGraph
  rfl

@[irreducible] noncomputable def
    syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) : Nat :=
  hybridFormulaStructuralPayloadBound
    (syntaxTaskAtRowsBinaryNamedFullCertificateOfGraph tokenTable width
      tokenCount boundaryTable count index binderArity hgraph)

theorem syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph_eq_raw
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) :
    syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph tokenTable width
        tokenCount boundaryTable count index binderArity hgraph =
      hybridFormulaStructuralPayloadBound
        (syntaxTaskAtRowsBinaryNamedFullCertificateRawOfGraph tokenTable width
          tokenCount boundaryTable count index binderArity hgraph) := by
  unfold syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph
  rw [syntaxTaskAtRowsBinaryNamedFullCertificateOfGraph_eq_raw]

theorem syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph_eq_conjunction
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) :
    syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph tokenTable width
        tokenCount boundaryTable count index binderArity hgraph =
      hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (syntaxTaskAtRowsBinaryNamedGuardCertificateOfGraph tokenTable width
            tokenCount boundaryTable count index binderArity hgraph)
          (syntaxTaskAtRowsBinaryNamedWitnessCertificateOfGraph tokenTable width
            tokenCount boundaryTable count index binderArity hgraph)) := by
  rw [syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph_eq_raw]
  rfl

#print axioms syntaxTaskAtRowsBinaryNamedFullCertificateOfGraph_eq_raw
#print axioms syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph_eq_raw
#print axioms
  syntaxTaskAtRowsBinaryNamedFullStructuralPayloadOfGraph_eq_conjunction

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedFullCertificate
