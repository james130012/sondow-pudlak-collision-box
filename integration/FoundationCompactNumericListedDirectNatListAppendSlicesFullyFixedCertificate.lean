import integration.FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedBound

/-! # Fully fixed structural payload of the append-slices certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 250000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedCertificate

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedBound

theorem
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fixed
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
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
          tokenTable width tokenCount leftStart leftFinish leftCount rightStart
          rightFinish rightCount targetStart targetFinish targetCount hgraph) <=
      appendSlicesFullyFixedPayloadPolynomial numericBound bitBound :=
  (compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount leftStart leftFinish leftCount rightStart
      rightFinish rightCount targetStart targetFinish targetCount hgraph).trans
    (compactAdditiveNatListAppendSlicesGraphPayloadEnvelope_le_fixed tokenTable
      width tokenCount leftStart leftFinish leftCount rightStart rightFinish
      rightCount targetStart targetFinish targetCount numericBound bitBound
      hgraph htableSize hwidthBound htokenCountBound hrightCountBound
      htargetCountBound hnumericSize)

#print axioms
  compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedCertificate
