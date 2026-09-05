import integration.FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds

/-! # Exact four-witness certificate for one natural-list cons tail branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBranchCertificate

open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate

noncomputable def compactAdditiveNatListConsRowsTailBranchCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (consRowsTailValuation index)
      (Rewriting.free
        (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
          sourceBoundary targetBoundary)) := by
  let body := compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
    tokenCount sourceBoundary targetBoundary
  let values := compactAdditiveNatListConsTailValues data
  let terminal :=
    compactAdditiveNatListConsRowsTailTerminalCertificate tokenTable width
      tokenCount sourceBoundary targetBoundary index data
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount body
    values (compactAdditiveNatListConsTailValues_le data) terminal
  exact CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactAdditiveNatListConsRowsTailBody_free_alignment tokenTable width
      tokenCount sourceBoundary targetBoundary).symm installed

#print axioms compactAdditiveNatListConsRowsTailBranchCertificate

end FoundationCompactNumericListedDirectNatListConsRowsTailBranchCertificate
