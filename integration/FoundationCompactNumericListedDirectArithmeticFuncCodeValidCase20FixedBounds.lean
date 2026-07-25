import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore

/-! # Fixed selected path for the valid function-code pair `(2, 0)` -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase20FixedBounds

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

theorem funcCodeValidCase20Certificate_structuralPayloadBound_le_fixed
    (arity code bitBound : Nat)
    (hpair : arity = 2 ∧ code = 0)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (funcCodeValidCase20Certificate arity code hpair) <=
      funcCodeValidCase20FixedPayloadEnvelope bitBound := by
  let pair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeFixedEqCertificate arity 2 hpair.1)
    (funcCodeFixedEqCertificate code 0 hpair.2)
  have hpairResource :=
    funcCodeValidPairCertificate_structuralPayloadBound_le_fixed arity 2 code
      0 bitBound hpair.1 hpair.2 haritySize hcodeSize (by omega) (by omega)
  let branch00 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 0
  let branch01 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 1
  let branch20 := funcCodeFixedEqFormula arity 2 ⋏
    funcCodeFixedEqFormula code 0
  let branch21 := funcCodeFixedEqFormula arity 2 ⋏
    funcCodeFixedEqFormula code 1
  let inner20 := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := branch21) pair
  let inner01 := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := branch01) inner20
  have hfull :=
    compactAdditiveArithmeticFuncCodeValidExplicitFormula_code_length_le_fixed
      arity code bitBound haritySize hcodeSize
  have htail01 :
      (binaryFormulaCode (branch01 ⋎ branch20 ⋎ branch21)).length <=
        funcCodeFormulaSyntaxFixedPolynomial bitBound :=
    funcCodeValidBranchCode_le_full arity code bitBound haritySize hcodeSize _
      (binaryFormulaCode_right_le_or _ _)
  have htail20 :=
    (binaryFormulaCode_right_le_or branch01 (branch20 ⋎ branch21)).trans
      htail01
  have hbranch20 :=
    (binaryFormulaCode_left_le_or branch20 branch21).trans htail20
  have hbranch21 :=
    (binaryFormulaCode_right_le_or branch20 branch21).trans htail20
  have hinner20 :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral pair
      (funcCodeValidPairFixedPayloadEnvelope bitBound)
      (funcCodeFormulaSyntaxFixedPolynomial bitBound) hpairResource (by
        unfold funcCodeFormulaSyntaxFixedPolynomial
        omega)
      (by simp [branch20]) (by simp [branch21])
      hbranch20 hbranch21 htail20
  have hbranch01 :=
    (binaryFormulaCode_left_le_or branch01 (branch20 ⋎ branch21)).trans
      htail01
  have hinner01 :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral inner20
      (hybridDisjunctionGeneralPayloadEnvelope
        (funcCodeFormulaSyntaxFixedPolynomial bitBound)
        (funcCodeValidPairFixedPayloadEnvelope bitBound))
      (funcCodeFormulaSyntaxFixedPolynomial bitBound) hinner20 (by
        unfold funcCodeFormulaSyntaxFixedPolynomial
        omega)
      (by simp [branch01]) (by simp [branch20, branch21])
      hbranch01 htail20 htail01
  have hbranch00 :=
    (binaryFormulaCode_left_le_or branch00
      (branch01 ⋎ branch20 ⋎ branch21)).trans hfull
  have houter :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral inner01
      (hybridDisjunctionGeneralPayloadEnvelope
        (funcCodeFormulaSyntaxFixedPolynomial bitBound)
        (hybridDisjunctionGeneralPayloadEnvelope
          (funcCodeFormulaSyntaxFixedPolynomial bitBound)
          (funcCodeValidPairFixedPayloadEnvelope bitBound)))
      (funcCodeFormulaSyntaxFixedPolynomial bitBound) hinner01 (by
        unfold funcCodeFormulaSyntaxFixedPolynomial
        omega)
      (by simp [branch00]) (by simp [branch01, branch20, branch21])
      hbranch00 htail01 (by
        simpa only [compactAdditiveArithmeticFuncCodeValidExplicitFormula,
          branch00, branch01, branch20, branch21] using hfull)
  unfold funcCodeValidCase20Certificate
    funcCodeValidCase20FixedPayloadEnvelope
  dsimp only [pair, inner20, inner01, branch00, branch01, branch20,
    branch21] at houter
  convert houter using 1
  congr 1

#print axioms funcCodeValidCase20Certificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase20FixedBounds
