import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexWitnessCertificate
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# Fixed envelope for the native-numeral row-lookup witnesses

This module specializes the generic arity-two witness envelope to the exact
row-lookup terminal formula.  It contains no certificate construction.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

theorem fixedNumeralAtRowsWitnessEnvelope_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index value numericBound
      bitBound : Nat)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexFixed : index <= 2) :
    explicitBoundedWitnessHybridStructuralPayloadEnvelope atRowsZeroValuation
        tokenCount
        (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
          tokenCount boundaryTable value (fixedNumeralTerm index))
        ![data.right, data.left]
        (compactAdditiveNatListAtRowsFixedNumeralTerminalFullyFixedPayloadPolynomial
          index numericBound bitBound) <=
      compactAdditiveNatListAtRowsFixedNumeralWitnessFullyFixedPayloadPolynomial
        index numericBound bitBound := by
  have hterminalCode :=
    compactAdditiveNatListAtRowsTerminalAtFixedNumeralIndex_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count value index bitBound
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hvalueSize
      hindexFixed
  have hterminalClosed :=
    compactAdditiveNatListAtRowsTerminalAtFixedNumeralIndex_freeVariables_eq_empty
      tokenTable width tokenCount boundaryTable value index
  have hcontextCode :
      formulaCodeSum
        (valuationContext
          (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
            tokenCount boundaryTable value
            (fixedNumeralTerm index)).freeVariables atRowsZeroValuation) <= 0 := by
    rw [hterminalClosed]
    simp [valuationContext, formulaCodeSum]
  unfold
    compactAdditiveNatListAtRowsFixedNumeralWitnessFullyFixedPayloadPolynomial
  apply
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity02
      atRowsZeroValuation 0 tokenCount numericBound
      (natListAtRowsFixedIndexFormulaCodePolynomial bitBound)
      (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value (fixedNumeralTerm index))
      ![data.right, data.left]
      (terminalSmall :=
        compactAdditiveNatListAtRowsFixedNumeralTerminalFullyFixedPayloadPolynomial
          index numericBound bitBound)
      (terminalLarge :=
        compactAdditiveNatListAtRowsFixedNumeralTerminalFullyFixedPayloadPolynomial
          index numericBound bitBound)
  · intro coordinate
    fin_cases coordinate
    · exact data.right_le
    · exact data.left_le
  · exact htokenCountValue
  · exact hterminalCode
  · exact hcontextCode
  · exact le_rfl

#print axioms fixedNumeralAtRowsWitnessEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
