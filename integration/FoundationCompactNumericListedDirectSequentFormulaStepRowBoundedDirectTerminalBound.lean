import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectFreeVariables

/-! # Empty-context terminal bound for one bounded sequent-step row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectTerminalBound

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectFreeVariables

def compactSequentFormulaStepRowBoundedDirectZeroValuation : Nat -> Nat :=
  fun _ => 0

opaque
    compactSequentFormulaStepRowBoundedInstalledTerminalBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ExplicitDirectFormulaBound
      compactSequentFormulaStepRowBoundedDirectZeroValuation
      (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          rowIndex ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (compactSequentFormulaStepRowBoundedDirectWitnessValues row
            coordinate)))
      (compactSequentFormulaStepDirectPublicPayloadEnvelope tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        row) := by
  let installedFormula :=
    compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (compactSequentFormulaStepRowBoundedDirectWitnessValues row
            coordinate))
  let directBound :=
    compactSequentFormulaStepDirectStructuralBoundOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      row hgraph
  let directFormula :=
    compactSequentFormulaStepDirectClosedFormula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row
  have hdirectClosed : directFormula.freeVariables = ∅ := by
    simpa only [directFormula] using
      (compactSequentFormulaStepDirectClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex row)
  let directContextual : CertifiedPAContextProof
      (valuationContext directFormula.freeVariables
        compactSequentFormulaStepRowBoundedDirectZeroValuation)
      directFormula :=
    CertifiedPAContextProof.castContext (by
      rw [hdirectClosed]
      simp [valuationContext])
      directBound.proof
  have hterminalFormula :
      directFormula = installedFormula := by
    simpa only [directFormula, installedFormula] using
      (compactSequentFormulaStepRowBoundedDirectRawTerminal_alignment
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex row).symm
  let terminal :=
    castValuationContextProof hterminalFormula directContextual
  refine ⟨terminal, ?_⟩
  rw [show terminal.payloadLength = directContextual.payloadLength by
    exact castValuationContextProof_payloadLength_eq
      hterminalFormula directContextual]
  change (CertifiedPAContextProof.castContext _
    directBound.proof).payloadLength <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  have hbound := directBound.payloadLength_le
  rw [
    compactSequentFormulaStepDirectStructuralBoundOfGraph_resource_eq_public
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex row hgraph] at hbound
  exact hbound

#print axioms
  compactSequentFormulaStepRowBoundedInstalledTerminalBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectTerminalBound
