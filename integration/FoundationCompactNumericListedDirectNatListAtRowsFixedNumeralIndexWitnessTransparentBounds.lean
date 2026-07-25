import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexWitnessCertificate

/-!
# Transparent resource bridge for the native-numeral row witness

This theorem identifies the named two-witness certificate with the generic
transparent witness envelope.  The fixed-polynomial arithmetic is deliberately
kept in the downstream module.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

theorem
    fixedNumeralAtRowsWitnessCertificate_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount boundaryTable index value terminalResource : Nat)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
    (hterminal :
      hybridFormulaStructuralPayloadBound
          (FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexTerminalFullyFixedBounds.fixedNumeralAtRowsTerminalCertificate
            tokenTable width tokenCount boundaryTable index value data) <=
        terminalResource) :
    hybridFormulaStructuralPayloadBound
        (fixedNumeralAtRowsWitnessCertificate tokenTable width tokenCount
          boundaryTable index value data) <=
      explicitBoundedWitnessHybridStructuralPayloadEnvelope atRowsZeroValuation
        tokenCount
        (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
          tokenCount boundaryTable value (fixedNumeralTerm index))
        ![data.right, data.left] terminalResource := by
  let terminal :=
    FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexTerminalFullyFixedBounds.fixedNumeralAtRowsTerminalCertificate
      tokenTable width tokenCount boundaryTable index value data
  let values : Fin 2 -> Nat := ![data.right, data.left]
  have htransparent :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value (fixedNumeralTerm index))
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.right_le
        · exact data.left_le)
      terminal terminalResource (by
        simpa only [terminal] using hterminal)
  unfold fixedNumeralAtRowsWitnessCertificate
  simpa only [hybridFormulaStructuralPayloadBound, terminal, values] using
    htransparent

#print axioms
  fixedNumeralAtRowsWitnessCertificate_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
