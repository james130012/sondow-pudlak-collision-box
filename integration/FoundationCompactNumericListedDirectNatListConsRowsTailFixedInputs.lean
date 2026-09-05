import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBranchFreeVariables
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSyntaxUniformBound
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailTerminalResources
import integration.FoundationCompactPAValuationContextSingletonCodeBound

/-! # Public syntax and context inputs for the fixed cons-tail envelope -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailFixedInputs

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAValuationContextSingletonCodeBound
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailBranchFreeVariables
open FoundationCompactNumericListedDirectNatListConsRowsTailSyntaxUniformBound
open FoundationCompactNumericListedDirectNatListConsRowsTailTerminalResources

theorem natListConsTailBodyCode_le_public
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary)).length <=
      natListConsRowsTailBranchFormulaCodePolynomial bitBound := by
  exact compactAdditiveNatListConsRowsTailBranchTerminal_code_length_le_uniform
    tokenTable width tokenCount sourceBoundary targetBoundary bitBound
    htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
    htargetBoundarySize

theorem natListConsTailBodyContextCode_le_public
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound : Nat)
    (hindex : index <= numericBound) :
    formulaCodeSum
        (valuationContext
          (compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
            tokenCount sourceBoundary targetBoundary).freeVariables
          (consRowsTailValuation index)) <=
      natListConsRowsTailTerminalContextCodePolynomial numericBound := by
  have hvaluation : consRowsTailValuation index 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  exact valuationContext_formulaCodeSum_le_singleton _ _ numericBound
    (compactAdditiveNatListConsRowsTailBranchTerminal_freeVariables_subset_singleton
      tokenTable width tokenCount sourceBoundary targetBoundary)
    hvaluation

#print axioms natListConsTailBodyCode_le_public
#print axioms natListConsTailBodyContextCode_le_public

end FoundationCompactNumericListedDirectNatListConsRowsTailFixedInputs
