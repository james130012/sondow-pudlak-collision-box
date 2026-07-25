import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore

/-! # Fixed selected path for the valid function-code pair `(0, 1)` -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase01FixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore

theorem funcCodeValidCase01Certificate_structuralPayloadBound_le_fixed
    (arity code bitBound : Nat)
    (hpair : arity = 0 ∧ code = 1)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (funcCodeValidCase01Certificate arity code hpair) <=
      funcCodeValidCase01FixedPayloadEnvelope bitBound := by
  let pair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeFixedEqCertificate arity 0 hpair.1)
    (funcCodeFixedEqCertificate code 1 hpair.2)
  have hpairResource :=
    funcCodeValidPairCertificate_structuralPayloadBound_le_fixed arity 0 code
      1 bitBound hpair.1 hpair.2 haritySize hcodeSize (by omega) (by omega)
  let branch00 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 0
  let branch01 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 1
  let tail20 :=
    (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 0) ⋎
      (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 1)
  let inner := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := tail20) pair
  have hfull :=
    compactAdditiveArithmeticFuncCodeValidExplicitFormula_code_length_le_fixed
      arity code bitBound haritySize hcodeSize
  have hbranch00Code :
      (binaryFormulaCode branch00).length <=
        funcCodeFormulaSyntaxFixedPolynomial bitBound :=
    funcCodeValidBranchCode_le_full arity code bitBound haritySize hcodeSize
      branch00 (binaryFormulaCode_left_le_or _ _)
  have htailCode :
      (binaryFormulaCode (branch01 ⋎ tail20)).length <=
        funcCodeFormulaSyntaxFixedPolynomial bitBound :=
    funcCodeValidBranchCode_le_full arity code bitBound haritySize hcodeSize
      (branch01 ⋎ tail20) (binaryFormulaCode_right_le_or _ _)
  have hbranch01Code :=
    (binaryFormulaCode_left_le_or branch01 tail20).trans htailCode
  have htail20Code :=
    (binaryFormulaCode_right_le_or branch01 tail20).trans htailCode
  have hinner :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral pair
      (funcCodeValidPairFixedPayloadEnvelope bitBound)
      (funcCodeFormulaSyntaxFixedPolynomial bitBound) hpairResource (by
        unfold funcCodeFormulaSyntaxFixedPolynomial
        omega)
      (by simp [branch01]) (by simp [tail20])
      hbranch01Code htail20Code htailCode
  have houter :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral inner
      (hybridDisjunctionGeneralPayloadEnvelope
        (funcCodeFormulaSyntaxFixedPolynomial bitBound)
        (funcCodeValidPairFixedPayloadEnvelope bitBound))
      (funcCodeFormulaSyntaxFixedPolynomial bitBound) hinner (by
        unfold funcCodeFormulaSyntaxFixedPolynomial
        omega)
      (by simp [branch00]) (by simp [branch01, tail20])
      hbranch00Code htailCode (by
        simpa only [compactAdditiveArithmeticFuncCodeValidExplicitFormula,
          branch00, branch01, tail20] using hfull)
  unfold funcCodeValidCase01Certificate
    funcCodeValidCase01FixedPayloadEnvelope
  dsimp only [pair, inner, branch00, branch01, tail20] at houter
  convert houter using 1
  congr 1

#print axioms funcCodeValidCase01Certificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase01FixedBounds
