import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadSyntaxUniformBound
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds

/-! # Public syntax and context inputs for the fixed cons-head envelope -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsHeadFixedInputs

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadSyntaxUniformBound

private abbrev consHeadZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

theorem natListConsHeadBodyCode_le_public
    (tokenTable width tokenCount targetBoundary head bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hheadSize : Nat.size head <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListConsRowsHeadTerminal tokenTable width tokenCount
        targetBoundary head)).length <=
      natListConsHeadTerminalBodyCodeEnvelope bitBound := by
  exact compactAdditiveNatListConsRowsHeadTerminal_code_length_le_uniform
    tokenTable width tokenCount targetBoundary head bitBound htableSize
    hwidthSize htokenCountSize htargetBoundarySize hheadSize

theorem natListConsHeadBodyContextCode_le_zero
    (tokenTable width tokenCount targetBoundary head : Nat) :
    formulaCodeSum
      (valuationContext
        (compactAdditiveNatListConsRowsHeadTerminal tokenTable width tokenCount
          targetBoundary head).freeVariables consHeadZeroValuation) <= 0 := by
  rw [compactAdditiveNatListConsRowsHeadTerminal_freeVariables_eq_empty]
  simp [valuationContext, formulaCodeSum]

#print axioms natListConsHeadBodyCode_le_public
#print axioms natListConsHeadBodyContextCode_le_zero

end FoundationCompactNumericListedDirectNatListConsRowsHeadFixedInputs
