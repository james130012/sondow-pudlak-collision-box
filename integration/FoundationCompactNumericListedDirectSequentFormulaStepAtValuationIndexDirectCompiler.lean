import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectTableTailCompiler
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-!
# Direct PA compiler for one original sequent step at an open row index

The lower two compiler modules close conjuncts 10--21.  This module prepends
the nine numerical bounds and casts the resulting exact-context proof back to
the original twenty-six-coordinate formula.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalAlignment
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax

/-- Compile all twenty-one original conjuncts without replacing the open row
index `&0` by a closed numeral. -/
noncomputable def
    compactSequentFormulaStepAtValuationIndexDirectBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ExactContextBoundedProof
      (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepDirectFormulaAtValuationIndex tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        (&0 : ValuationTerm) row) := by
  let tail10 :=
    compactSequentFormulaStepDirectTail10AtValuationIndexBoundOfGraph
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex row hgraph
  rcases hgraph with
    ⟨hcurrentStart, hcurrentFinish, hcurrentCount,
      hnextStart, hnextFinish, hnextCount,
      hvalueStart, hvalueFinish, hvalueCount,
      _, _, _, _, _, _, _, _, _, _, _, _⟩
  let valuation := extendValuation rowIndex zeroValuation
  let proof01 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepClosedLePublicBound
      row.current.start tokenCount hcurrentStart)
  let proof02 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepClosedLePublicBound
      row.current.finish tokenCount hcurrentFinish)
  let proof03 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepClosedLePublicBound
      row.current.count tokenCount hcurrentCount)
  let proof04 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepClosedLePublicBound
      row.next.start tokenCount hnextStart)
  let proof05 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepClosedLePublicBound
      row.next.finish tokenCount hnextFinish)
  let proof06 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepClosedLePublicBound
      row.next.count tokenCount hnextCount)
  let proof07 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepClosedLePublicBound
      row.value.start tokenCount hvalueStart)
  let proof08 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepClosedLePublicBound
      row.value.finish tokenCount hvalueFinish)
  let proof09 := ExactContextBoundedProof.ofEmpty (valuation := valuation)
    (compactSequentFormulaStepClosedLePublicBound
      row.value.count tokenCount hvalueCount)
  let tail09 := ExactContextBoundedProof.conjunction proof09 tail10
  let tail08 := ExactContextBoundedProof.conjunction proof08 tail09
  let tail07 := ExactContextBoundedProof.conjunction proof07 tail08
  let tail06 := ExactContextBoundedProof.conjunction proof06 tail07
  let tail05 := ExactContextBoundedProof.conjunction proof05 tail06
  let tail04 := ExactContextBoundedProof.conjunction proof04 tail05
  let tail03 := ExactContextBoundedProof.conjunction proof03 tail04
  let tail02 := ExactContextBoundedProof.conjunction proof02 tail03
  let assembled := ExactContextBoundedProof.conjunction proof01 tail02
  let partsFormula :=
    compactSequentFormulaStepDirectPartsFormulaAtValuationIndex tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      (&0 : ValuationTerm) row
  let partsBound : ExactContextBoundedProof valuation partsFormula := by
    simpa only [partsFormula,
      compactSequentFormulaStepDirectPartsFormulaAtValuationIndex,
      compactSequentFormulaStepDirectTail10AtValuationIndex,
      compactSequentFormulaStepDirectTail16AtValuationIndex] using assembled
  let directFormula :=
    compactSequentFormulaStepDirectFormulaAtValuationIndex tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      (&0 : ValuationTerm) row
  have hformula : partsFormula = directFormula := by
    simpa only [partsFormula, directFormula] using
      (compactSequentFormulaStepDirectFormulaAtValuationIndex_alignment
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount (&0 : ValuationTerm) row).symm
  let proof := castValuationContextProof hformula partsBound.proof
  refine
    { resource := partsBound.resource
      proof := proof
      payloadLength_le := ?_ }
  change proof.payloadLength <= partsBound.resource
  rw [show proof.payloadLength = partsBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula partsBound.proof]
  exact partsBound.payloadLength_le

#print axioms
  compactSequentFormulaStepAtValuationIndexDirectBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
