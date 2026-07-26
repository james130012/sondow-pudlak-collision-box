import integration.FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds

/-! # One fully fixed natural-list witness-row leaf -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowFullyFixedBound

open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListWitnessRowsFullyFixedProof
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowsFullyFixedBounds

noncomputable def compactSequentFormulaStepNatListRowFullyFixedBound
    (tokenTable width tokenCount start count finish boundaryTable boundarySize :
      Nat)
    (hcount : count <= tokenCount)
    (hrows : CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      start count finish boundaryTable boundarySize) :
    ClosedDirectFormulaBound
      (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
        tokenCount start count finish boundaryTable boundarySize)
      (compactSequentFormulaStepNatListRowsPayloadPolynomial tokenTable width
        tokenCount) := by
  let numericBound :=
    compactSequentFormulaStepNatListRowsNumericBound width tokenCount
  let bitBound :=
    compactSequentFormulaStepNatListRowsBitBound tokenTable width tokenCount
  have hwidthBound : width <= numericBound := by
    exact compactSequentFormulaStepNatListRows_width_le_numericBound width
      tokenCount
  have htokenCountBound : tokenCount <= numericBound := by
    exact compactSequentFormulaStepNatListRows_tokenCount_le_numericBound width
      tokenCount
  have htokenTableSize : Nat.size tokenTable <= bitBound := by
    exact compactSequentFormulaStepNatListRows_tokenTableSize_le_bitBound
      tokenTable width tokenCount
  have hnumericSize : Nat.size numericBound <= bitBound := by
    exact compactSequentFormulaStepNatListRows_numericBoundSize_le_bitBound
      tokenTable width tokenCount
  have hboundaryTableSize : Nat.size boundaryTable <= bitBound := by
    exact compactSequentFormulaStepNatListRows_boundaryTableSize_le_bitBound
      tokenTable width tokenCount count boundaryTable boundarySize hcount
      hrows.2.2.1 hrows.2.2.2
  simpa only [compactSequentFormulaStepNatListRowsPayloadPolynomial] using
    compactNatListWitnessRowsFullyFixedBound tokenTable width tokenCount start
      count finish boundaryTable boundarySize numericBound bitBound hrows
      hwidthBound htokenCountBound (hcount.trans htokenCountBound)
      htokenTableSize hboundaryTableSize hnumericSize

#print axioms compactSequentFormulaStepNatListRowFullyFixedBound

end FoundationCompactNumericListedDirectSequentFormulaStepNatListWitnessRowFullyFixedBound
