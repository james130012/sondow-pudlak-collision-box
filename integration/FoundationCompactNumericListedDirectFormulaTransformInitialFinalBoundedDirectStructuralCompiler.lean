import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectCompilation
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectClosedFreeVariables
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-! # Closed direct proof for bounded formula-transform endpoints -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectStructuralCompiler

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectOriginalSplitAlignment
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFreeVariables
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectCompilation

structure CompactFormulaTransformInitialFinalBoundedClosedDirectBound
    (formula : ValuationFormula) (resource : Nat) where
  proof : CertifiedPAContextProof ∅ formula
  payloadLength_le : proof.payloadLength <= resource

noncomputable def
    compactFormulaTransformInitialFinalBoundedClosedDirectBoundOfBounded
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound : Nat)
    (hbounded : CompactFormulaTransformInitialFinalBounded tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound) :
    CompactFormulaTransformInitialFinalBoundedClosedDirectBound
      (compactFormulaTransformInitialFinalBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound)
      (compactFormulaTransformInitialFinalBoundedDirectStructuralPayloadEnvelope
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound) := by
  let compiled :=
    formulaTransformInitialFinalBoundedDirectCompilationOfBounded tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound hbounded
  let sourceFormula :=
    compactFormulaTransformInitialFinalBoundedDirectSourceFormula tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound
  let rawProof := castDirectCompilationProof compiled.direct sourceFormula
    compiled.formula_eq
  have hformula : sourceFormula =
      compactFormulaTransformInitialFinalBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound := by
    exact
      (compactFormulaTransformInitialFinalBoundedClosedFormula_alignment_split
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound).symm
  let contextualProof := castValuationContextProof hformula rawProof
  have hclosed :=
    compactFormulaTransformInitialFinalBoundedClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity valueBound
  let proof : CertifiedPAContextProof ∅
      (compactFormulaTransformInitialFinalBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity valueBound) :=
    CertifiedPAContextProof.castContext (by
      rw [hclosed]
      simp [valuationContext]) contextualProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (CertifiedPAContextProof.castContext _
    contextualProof).payloadLength <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  exact castDirectCompilationProof_payloadLength_le compiled.direct
    sourceFormula compiled.formula_eq _ compiled.resource_eq

#print axioms
  compactFormulaTransformInitialFinalBoundedClosedDirectBoundOfBounded

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectStructuralCompiler
