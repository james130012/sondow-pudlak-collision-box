import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraph
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversalUniformResource

/-!
# Proof-independent resource bound for the complete bounded sequent-row graph
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraphUniformResource

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraph
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversal
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversalUniformResource

def compactSequentFormulaStepRowsBoundedDirectClosedUniformResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound : Nat) : Nat :=
  let exponentialFormula :=
    compactSequentFormulaStepRowsBoundedExponentialClosedFormula tableWidth
      valueBound
  let universalFormula :=
    (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound).ballLT (shortBinaryNumeralTerm rowCount)
  compactSequentFormulaStepRowsBoundedExponentialDirectResource tableWidth
      valueBound +
    compactSequentFormulaStepRowsBoundedDirectUniversalUniformResource tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowCount valueBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ exponentialFormula
      universalFormula

theorem
    compileCompactSequentFormulaStepRowsBoundedDirectClosedContext_payloadLength_le_uniform
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound : Nat)
    (hgraph : CompactSequentFormulaStepRowsBoundedGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
      tableWidth valueBound) :
    (compileCompactSequentFormulaStepRowsBoundedDirectClosedContext tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowCount tableWidth valueBound hgraph).payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectClosedUniformResource tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowCount tableWidth valueBound := by
  let exponentialProof :=
    compileCompactSequentFormulaStepRowsBoundedExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hgraph.2
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  have hexponential : exponentialProof.payloadLength <=
      compactSequentFormulaStepRowsBoundedExponentialDirectResource tableWidth
        valueBound :=
    compileCompactSequentFormulaStepRowsBoundedExponentialDirectContext_payloadLength_le
      tableWidth valueBound hgraph.1
  have huniversal : universalProof.payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectUniversalUniformResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound :=
    compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext_payloadLength_le_uniform
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hgraph.2
  have hraw := CertifiedPAContextProof.conjunction_payloadLength_le
    exponentialProof universalProof
  unfold
    compileCompactSequentFormulaStepRowsBoundedDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change raw.payloadLength <= _
  exact hraw.trans (by
    unfold
      compactSequentFormulaStepRowsBoundedDirectClosedUniformResource
    dsimp only
    omega)

#print axioms
  compileCompactSequentFormulaStepRowsBoundedDirectClosedContext_payloadLength_le_uniform

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraphUniformResource
