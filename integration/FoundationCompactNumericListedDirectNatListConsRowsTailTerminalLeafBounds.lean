import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSourceLeafBounds
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalTargetLeafBounds
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalAtomicLeafBounds

/-! # Aggregated leaf bounds for one natural-list cons tail terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailAtomicRowFixedBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalAtomicLeafBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafTypes
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSemanticBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalSourceLeafBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalTargetLeafBounds

theorem buildNatListConsRowsTailLeafBounds
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (numericBound bitBound : Nat)
    (facts : NatListConsRowsTailFixedFacts data numericBound bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    NatListConsRowsTailLeafBounds data numericBound bitBound := by
  have source := buildNatListConsRowsTailSourceLeafBounds data numericBound
    bitBound facts hsourceBoundarySize
  have target := buildNatListConsRowsTailTargetLeafBounds data numericBound
    bitBound facts htargetBoundarySize
  have atomic := buildNatListConsRowsTailAtomicLeafBounds data numericBound
    bitBound facts htokenTableSize hnumericSize
  exact {
    sourceLeftPayload := source.leftPayload
    sourceLeftCode := source.leftCode
    sourceRightPayload := source.rightPayload
    sourceRightCode := source.rightCode
    targetLeftPayload := target.leftPayload
    targetLeftCode := target.leftCode
    targetRightPayload := target.rightPayload
    targetRightCode := target.rightCode
    atomicRowPayload := atomic.payload
    atomicRowCode := atomic.code }

theorem consRowsTailPartsFormula_freeVariables_subset_singleton
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    (consRowsTailPartsFormula tokenTable width tokenCount sourceBoundary
      targetBoundary index data).freeVariables ⊆ {0} := by
  have hsourceLeft :
      (consRowsTailSourceLeftFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data).freeVariables ⊆ {0} := by
    unfold consRowsTailSourceLeftFormula
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      consRowsTailIndexTerm_freeVariables_subset
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hsourceRight :
      (consRowsTailSourceRightFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data).freeVariables ⊆ {0} := by
    unfold consRowsTailSourceRightFormula
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      consRowsTailSuccessorTerm_freeVariables_subset
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have htargetLeft :
      (consRowsTailTargetLeftFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data).freeVariables ⊆ {0} := by
    unfold consRowsTailTargetLeftFormula
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      consRowsTailSuccessorTerm_freeVariables_subset
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have htargetRight :
      (consRowsTailTargetRightFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data).freeVariables ⊆ {0} := by
    unfold consRowsTailTargetRightFormula
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      consRowsTailSecondSuccessorTerm_freeVariables_subset
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hatomic :
      (consRowsTailAtomicRowFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data).freeVariables ⊆ {0} := by
    rw [show
      (consRowsTailAtomicRowFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data).freeVariables = ∅ by
      unfold consRowsTailAtomicRowFormula
      exact natListConsRowsTailAtomicRowFormula_freeVariables_eq_empty _ _ _ _
        _ _ _]
    simp
  unfold consRowsTailPartsFormula
  simp only [LO.FirstOrder.Semiformula.freeVariables_and]
  exact Finset.union_subset hsourceLeft
    (Finset.union_subset hsourceRight
      (Finset.union_subset htargetLeft
        (Finset.union_subset htargetRight hatomic)))

#print axioms buildNatListConsRowsTailLeafBounds
#print axioms consRowsTailPartsFormula_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectNatListConsRowsTailTerminalLeafBounds
