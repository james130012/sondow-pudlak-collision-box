import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGraphPublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicFiniteBounds

/-!
# Graph-level public-finite bounds for term output rows

This module transfers the already checked graph-certificate bound to the
graph-independent finite envelope assembled from the fourteen semantic
branches.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate

theorem compactFormulaTransformTermOutputRowsGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) :
    compactFormulaTransformTermOutputRowsGraphPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount hgraph <=
      compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount := by
  unfold compactFormulaTransformTermOutputRowsGraphPayloadEnvelope
  exact
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData_le_publicFinite
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount
      (compactFormulaTransformTermOutputRowsCheckedBranchDataOfGraph tokenTable
        width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount hgraph)

theorem
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hgraph) <=
      compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount := by
  exact
    (compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount hgraph).trans
    (compactFormulaTransformTermOutputRowsGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount hgraph)

#print axioms
  compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
