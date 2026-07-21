import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

/-!
# Graph-level public structural resources for term output rows

This small module combines the fourteen independently checked branch bounds.
Keeping the dependent branch eliminator above the leaf module avoids repeating
the large branch proofs during graph-level elaboration.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate

theorem
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (data : CompactFormulaTransformTermOutputRowsCheckedBranchData tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount data) <=
      compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount data := by
  cases data with
  | zero hcount hconsumed hsame =>
      exact
        compactFormulaTransformTermOutputRowsZeroBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hsame
  | modeZeroLower hcount hconsumed hmode hguard hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeZeroLowerBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode hguard hrows
  | modeZeroShifted hcount hconsumed hmode failure hguard hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeZeroShiftedBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode failure hguard hrows
  | modeZeroRaw hcount hconsumed hmode lowerFailure shiftFailure hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeZeroRawBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode lowerFailure shiftFailure hrows
  | modeOneShifted hcount hconsumed hmode hguard hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeOneShiftedBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode hguard hrows
  | modeOneRaw hcount hconsumed hmode failure hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeOneRawBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode failure hrows
  | modeTwoLower hcount hconsumed hmode hguard hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeTwoLowerBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode hguard hrows
  | modeTwoRaw hcount hconsumed hmode failure hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeTwoRawBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode failure hrows
  | modeFourOne hcount hconsumed hmode hguard hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeFourOneBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode hguard hrows
  | modeFourSame hcount hconsumed hmode failure hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeFourSameBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode failure hrows
  | modeFiveCaptured hcount hconsumed hmode hguard hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeFiveCapturedBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode hguard hrows
  | modeFiveResidual hcount hconsumed hmode hguard residual hresidual hequality
      hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeFiveResidualBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount residual hcount
          hconsumed hmode hguard hresidual hequality hrows
  | modeFiveRaw hcount hconsumed hmode failure hrows =>
      exact
        compactFormulaTransformTermOutputRowsModeFiveRawBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hmode failure hrows
  | other hcount hconsumed hzero hone htwo hfour hfive hrows =>
      exact
        compactFormulaTransformTermOutputRowsOtherBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hcount
          hconsumed hzero hone htwo hfour hfive hrows

noncomputable def compactFormulaTransformTermOutputRowsGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount) : Nat :=
  compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData tokenTable
    width tokenCount current next mode binderArity tag argument consumedCount
    witnessStart witnessFinish witnessCount
    (compactFormulaTransformTermOutputRowsCheckedBranchDataOfGraph tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount hgraph)

theorem
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
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
      compactFormulaTransformTermOutputRowsGraphPayloadEnvelope tokenTable width
        tokenCount current next mode binderArity tag argument consumedCount
        witnessStart witnessFinish witnessCount hgraph := by
  let data := compactFormulaTransformTermOutputRowsCheckedBranchDataOfGraph
    tokenTable width tokenCount current next mode binderArity tag argument
    consumedCount witnessStart witnessFinish witnessCount hgraph
  have hbranch :=
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount data
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  unfold compactFormulaTransformTermOutputRowsGraphPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
      (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
        tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount data) <=
    compactFormulaTransformTermOutputRowsBranchPayloadEnvelopeFromData
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount data
  exact hbranch

#print axioms
  compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_transparent
#print axioms
  compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
