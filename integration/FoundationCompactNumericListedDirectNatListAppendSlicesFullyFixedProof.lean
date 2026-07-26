import integration.FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedCertificate

/-! # Fully fixed empty-context PA proof for the append-slices leaf -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 250000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedProof

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedCertificate

theorem exists_compactAdditiveNatListAppendSlicesFullyFixedPAProof
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hrightCountBound : rightCount <= numericBound)
    (htargetCountBound : targetCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ∃ proof : CertifiedPAContextProof ∅
        (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
          tokenCount leftStart leftFinish leftCount rightStart rightFinish
          rightCount targetStart targetFinish targetCount),
      proof.payloadLength <=
        appendSlicesFullyFixedPayloadPolynomial numericBound bitBound := by
  let certificate :=
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount leftStart leftFinish leftCount rightStart
      rightFinish rightCount targetStart targetFinish targetCount hgraph
  have hclosed :
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount).freeVariables = ∅ := by
    rw [compactAdditiveNatListAppendSlicesClosedFormula_alignment]
    exact compactAdditiveNatListAppendSlicesExplicitFormula_closed tokenTable
      width tokenCount leftStart leftFinish leftCount rightStart rightFinish
      rightCount targetStart targetFinish targetCount
  have hcontext :
      valuationContext
          (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
            tokenCount leftStart leftFinish leftCount rightStart rightFinish
            rightCount targetStart targetFinish targetCount).freeVariables
          FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate.zeroValuation =
        ∅ := by
    rw [hclosed]
    simp [valuationContext]
  let proof : CertifiedPAContextProof ∅
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount) :=
    CertifiedPAContextProof.castContext hcontext certificate.compile
  refine ⟨proof, ?_⟩
  have hcompile := compile_payloadLength_le_structuralPayloadBound certificate
  have hfixed :=
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fixed
      tokenTable width tokenCount leftStart leftFinish leftCount rightStart
      rightFinish rightCount targetStart targetFinish targetCount numericBound
      bitBound hgraph htableSize hwidthBound htokenCountBound hrightCountBound
      htargetCountBound hnumericSize
  dsimp only [proof]
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact hcompile.trans hfixed

#print axioms exists_compactAdditiveNatListAppendSlicesFullyFixedPAProof

end FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedProof
