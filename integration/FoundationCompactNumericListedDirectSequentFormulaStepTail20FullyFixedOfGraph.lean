import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail20FullyFixedBound

/-! # Install the fully fixed final two leaves from a checked graph -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 250000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail20FullyFixedOfGraph

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedAppendLeaf
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedCountLeaf
open FoundationCompactNumericListedDirectSequentFormulaStepTail20FullyFixedBound

noncomputable def compactSequentFormulaStepTail20FullyFixedBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ClosedDirectFormulaBound
      ((compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
          tokenCount row.value.start row.value.finish row.value.count
          row.next.start row.next.finish row.next.count row.current.start
          row.current.finish row.current.count) ⋏
        (“!!(shortBinaryNumeralTerm suffixCount) =
          !!(shortBinaryNumeralTerm valueCount) + 1” : ValuationFormula))
      (compactSequentFormulaStepTail20FullyFixedPayloadPolynomial tokenTable
        width tokenCount suffixCount valueCount row) := by
  let append := compactSequentFormulaStepTail16FixedAppendLeafOfGraph
    tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
    valueCount rowIndex row hgraph
  rcases hgraph with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hcount⟩
  let countExists := exists_compactSequentFormulaStepTail16FixedCountLeaf
    suffixCount valueCount hcount
  exact compactSequentFormulaStepTail20FullyFixedBoundOfLeaves tokenTable width
    tokenCount suffixCount valueCount row append (Classical.choose countExists)
    (Classical.choose_spec countExists)

#print axioms compactSequentFormulaStepTail20FullyFixedBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepTail20FullyFixedOfGraph
