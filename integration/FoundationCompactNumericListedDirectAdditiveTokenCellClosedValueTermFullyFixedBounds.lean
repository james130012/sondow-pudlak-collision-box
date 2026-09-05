import integration.FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsPublicBounds

/-!
# Fully uniform token-cell certificate for an arbitrary closed value term

This module adapts the zero-valuation token-cell theorem to the local
certificate constructor used by the exact index-and-value-term NatList route.
The value expression remains in the checked formula; it is not replaced by a
numeral or by a finite enumeration.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 60000

namespace FoundationCompactNumericListedDirectAdditiveTokenCellClosedValueTermFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds

theorem
    compactAdditiveNatListAtRowsValueTokenCellCertificate_structuralPayloadBound_le_closedValueFixed
    (tokenTable width tokenCount cursor next numericBound bitBound : Nat)
    (valueTerm : ValuationTerm)
    (hwidthValue : width <= numericBound)
    (hcursorValue : cursor <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size (termValue natListAtZeroValuation valueTerm) <=
      bitBound)
    (hnextSize : Nat.size next <= bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound)
    (hvalueClosed : valueTerm.freeVariables = ∅)
    (hcell : CompactAdditiveTokenCell
      (termValue natListAtZeroValuation (shortBinaryNumeralTerm tokenTable))
      (termValue natListAtZeroValuation (shortBinaryNumeralTerm width))
      (termValue natListAtZeroValuation (shortBinaryNumeralTerm tokenCount))
      (termValue natListAtZeroValuation (shortBinaryNumeralTerm cursor))
      (termValue natListAtZeroValuation valueTerm)
      (termValue natListAtZeroValuation (shortBinaryNumeralTerm next))) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificateLocal
          natListAtZeroValuation (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm cursor) valueTerm
          (shortBinaryNumeralTerm next) hcell) <=
      additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound := by
  exact
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount cursor next numericBound bitBound valueTerm
      hwidthValue hcursorValue htableSize hwidthSize htokenCountSize hcursorSize
      hvalueSize hnextSize hvalueCode hvalueClosed hcell

#print axioms
  compactAdditiveNatListAtRowsValueTokenCellCertificate_structuralPayloadBound_le_closedValueFixed

end FoundationCompactNumericListedDirectAdditiveTokenCellClosedValueTermFullyFixedBounds
