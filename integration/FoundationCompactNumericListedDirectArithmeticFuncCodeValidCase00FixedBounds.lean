import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore

/-! # Fixed selected path for the valid function-code pair `(0, 0)` -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase00FixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore

theorem funcCodeValidCase00Certificate_structuralPayloadBound_le_fixed
    (arity code bitBound : Nat)
    (hpair : arity = 0 ∧ code = 0)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (funcCodeValidCase00Certificate arity code hpair) <=
      funcCodeValidCase00FixedPayloadEnvelope bitBound := by
  let pair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeFixedEqCertificate arity 0 hpair.1)
    (funcCodeFixedEqCertificate code 0 hpair.2)
  have hpairResource :=
    funcCodeValidPairCertificate_structuralPayloadBound_le_fixed arity 0 code
      0 bitBound hpair.1 hpair.2 haritySize hcodeSize (by omega) (by omega)
  let branch00 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 0
  let tail :=
    (funcCodeFixedEqFormula arity 0 ⋏ funcCodeFixedEqFormula code 1) ⋎
      (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 0) ⋎
      (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 1)
  have hfull :=
    compactAdditiveArithmeticFuncCodeValidExplicitFormula_code_length_le_fixed
      arity code bitBound haritySize hcodeSize
  have hbranchCode :
      (binaryFormulaCode branch00).length <=
        funcCodeFormulaSyntaxFixedPolynomial bitBound :=
    funcCodeValidBranchCode_le_full arity code bitBound haritySize hcodeSize
      branch00 (binaryFormulaCode_left_le_or _ _)
  have htailCode :
      (binaryFormulaCode tail).length <=
        funcCodeFormulaSyntaxFixedPolynomial bitBound :=
    funcCodeValidBranchCode_le_full arity code bitBound haritySize hcodeSize
      tail (binaryFormulaCode_right_le_or _ _)
  have hselected :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral pair
      (funcCodeValidPairFixedPayloadEnvelope bitBound)
      (funcCodeFormulaSyntaxFixedPolynomial bitBound) hpairResource (by
        unfold funcCodeFormulaSyntaxFixedPolynomial
        omega)
      (by simp [branch00]) (by simp [tail])
      hbranchCode htailCode (by
        simpa only [compactAdditiveArithmeticFuncCodeValidExplicitFormula,
          branch00, tail] using hfull)
  unfold funcCodeValidCase00Certificate
    funcCodeValidCase00FixedPayloadEnvelope
  dsimp only [pair, branch00, tail] at hselected
  convert hselected using 1
  congr 1

#print axioms funcCodeValidCase00Certificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase00FixedBounds
