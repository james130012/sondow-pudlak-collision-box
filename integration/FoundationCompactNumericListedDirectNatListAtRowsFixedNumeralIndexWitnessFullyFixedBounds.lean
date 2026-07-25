import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexWitnessTransparentBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexWitnessEnvelopeFixedBounds

/-!
# Fully fixed two-witness row lookup at native numeral indices

This module isolates the expensive two-witness installation from the outer
row-lookup guard and conjunction.  Downstream files consume the compiled
resource theorem without re-elaborating its dependent certificate proof.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

theorem
    fixedNumeralAtRowsWitnessCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound : Nat)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (hindex : index < count)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexFixed : index <= 2) :
    hybridFormulaStructuralPayloadBound
        (fixedNumeralAtRowsWitnessCertificate tokenTable width tokenCount
          boundaryTable index value data) <=
      compactAdditiveNatListAtRowsFixedNumeralWitnessFullyFixedPayloadPolynomial
        index numericBound bitBound := by
  let terminal :=
    FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexTerminalFullyFixedBounds.fixedNumeralAtRowsTerminalCertificate
      tokenTable width tokenCount boundaryTable index value data
  have hterminal :
      hybridFormulaStructuralPayloadBound terminal <=
        compactAdditiveNatListAtRowsFixedNumeralTerminalFullyFixedPayloadPolynomial
          index numericBound bitBound := by
    simpa only [terminal] using
      compactAdditiveNatListAtRowsFixedNumeralTerminalCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount boundaryTable count index value numericBound
        bitBound data hwidthValue htokenCountValue hcountValue hindex htableSize
        hwidthSize htokenCountSize hboundarySize hcountSize hvalueSize hindexFixed
  have htransparent :=
    fixedNumeralAtRowsWitnessCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount boundaryTable index value
      (compactAdditiveNatListAtRowsFixedNumeralTerminalFullyFixedPayloadPolynomial
        index numericBound bitBound)
      data hterminal
  exact htransparent.trans
    (fixedNumeralAtRowsWitnessEnvelope_le_fullyFixed tokenTable width tokenCount
      boundaryTable count index value numericBound bitBound data
      htokenCountValue htableSize hwidthSize htokenCountSize hboundarySize
      hcountSize hvalueSize hindexFixed)

#print axioms
  fixedNumeralAtRowsWitnessCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
