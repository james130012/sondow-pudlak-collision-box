import integration.FoundationCompactNumericListedDirectNegationFormulaTagBranchAssemblyFixedBounds

/-! # Fully fixed endpoint for the checked negation-tag graph certificate -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 50000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNegationFormulaTagFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagBranchAssemblyFixedBounds

theorem
    compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tag mapped bitBound : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactNegationFormulaTagExplicitHybridCertificateOfGraph
          tag mapped hgraph) <=
      negationFormulaTagFullyFixedPayloadPolynomial bitBound := by
  let data := compactNegationFormulaTagCheckedBranchDataOfGraph
    tag mapped hgraph
  have hbound :=
    compactNegationFormulaTagExplicitHybridCertificateFromData_structuralPayloadBound_le_fullyFixed
      tag mapped bitBound htagSize hmappedSize data
  simpa only [compactNegationFormulaTagExplicitHybridCertificateOfGraph,
    hybridFormulaStructuralPayloadBound, data] using hbound

#print axioms
  compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNegationFormulaTagFullyFixedBounds
