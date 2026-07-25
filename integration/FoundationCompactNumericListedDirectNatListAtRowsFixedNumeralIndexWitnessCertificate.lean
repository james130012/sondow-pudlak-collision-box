import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexTerminalFullyFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-!
# The native-numeral row-lookup witness certificate

The certificate object is isolated from its quantitative resource theorem so
that downstream elaboration can reuse one compiled dependent proof term.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 50000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
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

def compactAdditiveNatListAtRowsFixedNumeralWitnessFullyFixedPayloadPolynomial
    (index numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (natListAtRowsFixedIndexFormulaCodePolynomial bitBound)
    (compactAdditiveNatListAtRowsFixedNumeralTerminalFullyFixedPayloadPolynomial
      index numericBound bitBound)

noncomputable def fixedNumeralAtRowsWitnessCertificate
    (tokenTable width tokenCount boundaryTable index value : Nat)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value) :
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
        tokenCount boundaryTable value (fixedNumeralTerm index)) := by
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value (fixedNumeralTerm index))
    ![data.right, data.left] (by
      intro coordinate
      fin_cases coordinate
      · exact data.right_le
      · exact data.left_le)
    (FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexTerminalFullyFixedBounds.fixedNumeralAtRowsTerminalCertificate
      tokenTable width tokenCount boundaryTable index value data)
  exact CheckedHybridValuationBoundedFormulaCertificate.cast (by
    rw [explicitBoundedWitnessFormula_two_eq]
    rfl) installed

end FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
