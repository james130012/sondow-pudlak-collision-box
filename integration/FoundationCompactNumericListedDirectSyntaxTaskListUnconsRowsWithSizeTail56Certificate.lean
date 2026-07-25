import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions

/-!
# Innermost checked certificate of syntax-task-list uncons

This module exposes only the original `NatSize ∧ area` certificate layer.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate

noncomputable def unconsRowsWithSizeTail56Certificate
    (tailBoundarySize tailBoundary tailCount tokenCount : Nat)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (compactNatSizeClosedFormula tailBoundarySize tailBoundary ⋏
        (“!!(shortBinaryNumeralTerm tailBoundarySize) ≤
          (!!(shortBinaryNumeralTerm tailCount) + 1) *
            !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactNatSizeExplicitHybridCertificateOfEq tailBoundarySize tailBoundary
      hsize)
    (closedTailAreaLeCertificate tailBoundarySize tailCount tokenCount harea)

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeTail56Certificate
