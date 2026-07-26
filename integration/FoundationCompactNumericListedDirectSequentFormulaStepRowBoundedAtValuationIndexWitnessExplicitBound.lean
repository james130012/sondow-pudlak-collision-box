import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessExplicitPayload
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Explicit eighteen-witness bound at an open row index -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData

noncomputable def
    compactSequentFormulaStepRowBoundedAtValuationIndexExplicitWitnessBoundOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    ExplicitDirectFormulaBound
      (extendValuation rowIndex
        FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation)
      (explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 18
        (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount))
      (compactSequentFormulaStepRowBoundedAtValuationIndexWitnessPayloadEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound data) :=
  { proof :=
      compactSequentFormulaStepRowBoundedAtValuationIndexExplicitWitnessProofOfData
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound data
    payloadLength_le :=
      compactSequentFormulaStepRowBoundedAtValuationIndexExplicitWitnessProof_payloadLength_le
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound data }

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexExplicitWitnessBoundOfData

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler
