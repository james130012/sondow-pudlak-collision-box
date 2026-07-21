import integration.FoundationCompactNumericListedDirectVerifierStateCoreStructuredLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierChildResultListRowsExplicitHybridCertificate

/-!
# Direct explicit certificate from a verifier state-core graph

The public endpoint consumes the concrete twelve-part state-core graph.  All
closed component certificates, including both arbitrary-count row graphs, are
constructed internally at the same 24-coordinate environment.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierStateCoreGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierStateCoreLeafExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierStateCoreStructuredLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveOptionBoolExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

def compactNumericVerifierStateCoordinatesAtValues
    (values : Fin 24 -> Nat) : CompactNumericVerifierStateRowCoordinates :=
  compactNumericVerifierStateRowCoordinatesOf
    (values 3) (values 4) (values 5) (values 6)
    (values 7) (values 8) (values 9) (values 10)
    (values 11) (values 12) (values 13) (values 14)
    (values 15) (values 16) (values 17)

def compactNumericVerifierStateSizeWitnessAtValues
    (values : Fin 24 -> Nat) : CompactNumericVerifierStateSizeWitness where
  taskBoundarySize := values 18
  valueBoundarySize := values 19
  taskTableWidth := values 20
  taskValueBound := values 21
  valueTableWidth := values 22
  valueValueBound := values 23

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

theorem compactNumericVerifierStateTaskRowsAtEnvironmentFormula_eq_closed
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateTaskRowsAtEnvironmentFormula values =
      compactNumericVerifierTaskListRowsClosedFormula
        (values 0) (values 1) (values 2) (values 11)
        (values 10) (values 20) (values 21) := by
  unfold compactNumericVerifierStateTaskRowsAtEnvironmentFormula
  unfold compactNumericVerifierTaskListRowsClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStateEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

theorem compactNumericVerifierStateValueRowsAtEnvironmentFormula_eq_closed
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateValueRowsAtEnvironmentFormula values =
      compactNumericChildResultListRowsClosedFormula
        (values 0) (values 1) (values 2) (values 14)
        (values 13) (values 22) (values 23) := by
  unfold compactNumericVerifierStateValueRowsAtEnvironmentFormula
  unfold compactNumericChildResultListRowsClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStateEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

/-- Close the exact state-core formula directly from its semantic graph. -/
noncomputable def compactNumericVerifierStateCoreExplicitHybridCertificateOfGraph
    (values : Fin 24 -> Nat)
    (hgraph : CompactNumericVerifierStateCoreGraph
      (values 0) (values 1) (values 2)
      (compactNumericVerifierStateCoordinatesAtValues values)
      (compactNumericVerifierStateSizeWitnessAtValues values)) :
    HybridCertificate
      (compactNumericVerifierStateCoreAtEnvironmentFormula values) := by
  rcases hgraph with
    ⟨hproofSlice, hcertificateSlice, htaskLayout, htaskRows,
      htaskBoundarySize, htaskBoundaryBound,
      hvalueLayout, hvalueRows, hvalueBoundarySize, hvalueBoundaryBound,
      hoptionLayout, hstatus⟩
  have hproofSlice' : CompactAdditiveNatListSlice
      (values 0) (values 1) (values 2)
      (values 3) (values 6) (values 5) := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf] using hproofSlice
  have hcertificateSlice' : CompactAdditiveNatListSlice
      (values 0) (values 1) (values 2)
      (values 5) (values 8) (values 7) := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf] using
      hcertificateSlice
  have htaskLayout' : CompactAdditiveStructuredListLayout
      (values 0) (values 1) (values 2)
      (values 7) (values 10) (values 9) (values 11) := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf] using htaskLayout
  have htaskRows' : CompactNumericVerifierTaskListRowsGraph
      (values 0) (values 1) (values 2) (values 11)
      (values 10) (values 20) (values 21) := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf,
      compactNumericVerifierStateSizeWitnessAtValues] using htaskRows
  have htaskBoundarySize' : values 18 = Nat.size (values 11) := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf,
      compactNumericVerifierStateSizeWitnessAtValues] using
        htaskBoundarySize
  have htaskBoundaryBound' : values 18 ≤ (values 10 + 1) * values 2 := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf,
      compactNumericVerifierStateSizeWitnessAtValues] using
        htaskBoundaryBound
  have hvalueLayout' : CompactAdditiveStructuredListLayout
      (values 0) (values 1) (values 2)
      (values 9) (values 13) (values 12) (values 14) := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf] using hvalueLayout
  have hvalueRows' : CompactNumericChildResultListRowsGraph
      (values 0) (values 1) (values 2) (values 14)
      (values 13) (values 22) (values 23) := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf,
      compactNumericVerifierStateSizeWitnessAtValues] using hvalueRows
  have hvalueBoundarySize' : values 19 = Nat.size (values 14) := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf,
      compactNumericVerifierStateSizeWitnessAtValues] using
        hvalueBoundarySize
  have hvalueBoundaryBound' : values 19 ≤ (values 13 + 1) * values 2 := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf,
      compactNumericVerifierStateSizeWitnessAtValues] using
        hvalueBoundaryBound
  have hoptionLayout' : CompactAdditiveOptionLayout
      (values 0) (values 1) (values 2)
      (values 12) (values 15) (values 16) (values 4) := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf] using hoptionLayout
  have hstatus' :
      ((values 15 = 0 ∧ values 4 = values 16) ∨
        (values 15 = 1 ∧
          CompactAdditiveBoolSlice
            (values 0) (values 1) (values 2)
            (values 16) (values 17) (values 4))) := by
    simpa [compactNumericVerifierStateCoordinatesAtValues,
      compactNumericVerifierStateRowCoordinatesOf] using hstatus
  let parts : CompactNumericVerifierStateCoreImmediateCertificates
      zeroValuation values :=
    { proofSlice := by
        rw [
          compactNumericVerifierStateProofSliceAtEnvironmentFormula_eq_closed]
        exact compactAdditiveNatListSliceExplicitHybridCertificateOfSlice
          (values 0) (values 1) (values 2)
          (values 3) (values 6) (values 5) hproofSlice'
      certificateSlice := by
        rw [
          compactNumericVerifierStateCertificateSliceAtEnvironmentFormula_eq_closed]
        exact compactAdditiveNatListSliceExplicitHybridCertificateOfSlice
          (values 0) (values 1) (values 2)
          (values 5) (values 8) (values 7) hcertificateSlice'
      taskLayout :=
        compactNumericVerifierStateTaskLayoutExplicitHybridCertificate
          values htaskLayout'
      taskRows := by
        rw [compactNumericVerifierStateTaskRowsAtEnvironmentFormula_eq_closed]
        exact compactNumericVerifierTaskListRowsExplicitHybridCertificateOfGraph
          (values 0) (values 1) (values 2) (values 11)
          (values 10) (values 20) (values 21) htaskRows'
      taskBoundarySize :=
        compactNumericVerifierStateTaskBoundarySizeExplicitHybridCertificate
          values htaskBoundarySize'
      taskBoundaryBound :=
        compactNumericVerifierStateTaskBoundaryBoundExplicitHybridCertificate
          values htaskBoundaryBound'
      valueLayout :=
        compactNumericVerifierStateValueLayoutExplicitHybridCertificate
          values hvalueLayout'
      valueRows := by
        rw [compactNumericVerifierStateValueRowsAtEnvironmentFormula_eq_closed]
        exact compactNumericChildResultListRowsExplicitHybridCertificateOfGraph
          (values 0) (values 1) (values 2) (values 14)
          (values 13) (values 22) (values 23) hvalueRows'
      valueBoundarySize :=
        compactNumericVerifierStateValueBoundarySizeExplicitHybridCertificate
          values hvalueBoundarySize'
      valueBoundaryBound :=
        compactNumericVerifierStateValueBoundaryBoundExplicitHybridCertificate
          values hvalueBoundaryBound'
      optionLayout := by
        rw [
          compactNumericVerifierStateOptionLayoutAtEnvironmentFormula_eq_closed]
        exact compactAdditiveOptionLayoutExplicitHybridCertificateOfLayout
          (values 0) (values 1) (values 2) (values 12)
          (values 15) (values 16) (values 4) hoptionLayout' }
  if hzero : values 15 = 0 then
    have hfinish : values 4 = values 16 := by
      rcases hstatus' with hnone | hsome
      · exact hnone.2
      · exact False.elim (by omega)
    exact compactNumericVerifierStateCoreExplicitHybridCertificateOfNone parts
      (compactNumericVerifierStateStatusTagZeroExplicitHybridCertificate
        values hzero)
      (compactNumericVerifierStateStatusFinishEqExplicitHybridCertificate
        values hfinish)
  else
    have hsome : values 15 = 1 ∧
        CompactAdditiveBoolSlice
          (values 0) (values 1) (values 2)
          (values 16) (values 17) (values 4) := by
      rcases hstatus' with hnone | hsome
      · exact False.elim (hzero hnone.1)
      · exact hsome
    let boolSlice : HybridCertificate
        (compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula
          values) := by
      rw [
        compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula_eq_closed]
      exact compactAdditiveBoolSliceExplicitHybridCertificateOfSlice
        (values 0) (values 1) (values 2)
        (values 16) (values 17) (values 4) hsome.2
    exact compactNumericVerifierStateCoreExplicitHybridCertificateOfSome parts
      (compactNumericVerifierStateStatusTagOneExplicitHybridCertificate
        values hsome.1)
      boolSlice

#print axioms
  compactNumericVerifierStateTaskRowsAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierStateValueRowsAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierStateCoreExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectVerifierStateCoreGraphExplicitHybridCertificate
