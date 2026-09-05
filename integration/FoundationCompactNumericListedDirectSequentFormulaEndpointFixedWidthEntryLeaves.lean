import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointDirectSyntax
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroBound
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingBounds

/-! # The four fixed-width entry leaves of the sequent endpoint -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryLeaves

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryCertificateBound
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryZeroBound
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingCertificates
open FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryRemainingBounds
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

structure CompactSequentFormulaEndpointFixedWidthEntryLeaves
    (tokenCount finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) where
  firstStart : FixedResourceEmptyContextProof
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm coordinates.suffixBoundary)
      (shortBinaryNumeralTerm tokenCount) (‘0’ : ValuationTerm)
      (shortBinaryNumeralTerm coordinates.firstStart))
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial
      coordinates.suffixBoundary tokenCount coordinates.firstStart
      (‘0’ : ValuationTerm))
  firstFinish : FixedResourceEmptyContextProof
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm coordinates.suffixBoundary)
      (shortBinaryNumeralTerm tokenCount) (‘1’ : ValuationTerm)
      (shortBinaryNumeralTerm coordinates.firstFinish))
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial
      coordinates.suffixBoundary tokenCount coordinates.firstFinish
      (‘1’ : ValuationTerm))
  finalStart : FixedResourceEmptyContextProof
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm coordinates.suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm coordinates.valueCount)
      (shortBinaryNumeralTerm finalStart))
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial
      coordinates.suffixBoundary tokenCount finalStart
      (shortBinaryNumeralTerm coordinates.valueCount))
  finalFinish : FixedResourceEmptyContextProof
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm coordinates.suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (endpointSuccessorIndexTerm coordinates.valueCount)
      (shortBinaryNumeralTerm finalFinish))
    (sequentFormulaEndpointFixedWidthEntryPayloadPolynomial
      coordinates.suffixBoundary tokenCount finalFinish
      (endpointSuccessorIndexTerm coordinates.valueCount))

noncomputable def compactSequentFormulaEndpointFixedWidthEntryLeavesOfGraph
    (tokenTable width tokenCount inputStart inputFinish valueStart valueFinish
      finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates)
    (hgraph : CompactSequentFormulaEndpointGraph tokenTable width tokenCount
      inputStart inputFinish valueStart valueFinish finalStart finalFinish
      coordinates) :
    CompactSequentFormulaEndpointFixedWidthEntryLeaves tokenCount finalStart
      finalFinish coordinates := by
  rcases hgraph with
    ⟨_, _, _, _, hfirstStart, hfirstFinish, hfinalStart, hfinalFinish,
      _, _, _, _⟩
  exact
    { firstStart :=
        sequentFormulaEndpointFixedWidthEntryZeroBound
          coordinates.suffixBoundary tokenCount coordinates.firstStart
          hfirstStart
      firstFinish :=
        sequentFormulaEndpointFixedWidthEntryOneBound
          coordinates.suffixBoundary tokenCount coordinates.firstFinish
          hfirstFinish
      finalStart :=
        sequentFormulaEndpointFixedWidthEntryNumeralBound
          coordinates.suffixBoundary tokenCount coordinates.valueCount
          finalStart hfinalStart
      finalFinish :=
        sequentFormulaEndpointFixedWidthEntrySuccessorBound
          coordinates.suffixBoundary tokenCount coordinates.valueCount
          finalFinish hfinalFinish }

#print axioms compactSequentFormulaEndpointFixedWidthEntryLeavesOfGraph

end FoundationCompactNumericListedDirectSequentFormulaEndpointFixedWidthEntryLeaves
