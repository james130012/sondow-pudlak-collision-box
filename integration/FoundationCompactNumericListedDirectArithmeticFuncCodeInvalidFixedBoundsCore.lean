import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidPairFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-! # Shared formulas and fixed envelopes for invalid function codes -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBoundsCore

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidPairFixedBounds

def funcCodeInvalidPair00Formula (arity code : Nat) : ValuationFormula :=
  funcCodeFixedNeFormula arity 0 ⋎ funcCodeFixedNeFormula code 0

def funcCodeInvalidPair01Formula (arity code : Nat) : ValuationFormula :=
  funcCodeFixedNeFormula arity 0 ⋎ funcCodeFixedNeFormula code 1

def funcCodeInvalidPair20Formula (arity code : Nat) : ValuationFormula :=
  funcCodeFixedNeFormula arity 2 ⋎ funcCodeFixedNeFormula code 0

def funcCodeInvalidPair21Formula (arity code : Nat) : ValuationFormula :=
  funcCodeFixedNeFormula arity 2 ⋎ funcCodeFixedNeFormula code 1

def funcCodeInvalidTail20Formula (arity code : Nat) : ValuationFormula :=
  funcCodeInvalidPair20Formula arity code ⋏
    funcCodeInvalidPair21Formula arity code

def funcCodeInvalidTail01Formula (arity code : Nat) : ValuationFormula :=
  funcCodeInvalidPair01Formula arity code ⋏
    funcCodeInvalidTail20Formula arity code

theorem compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_eq_fixedTree
    (arity code : Nat) :
    compactAdditiveArithmeticFuncCodeInvalidExplicitFormula arity code =
      funcCodeInvalidPair00Formula arity code ⋏
        funcCodeInvalidTail01Formula arity code := by
  rfl

def funcCodeInvalidTail20FixedPayloadEnvelope (bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (funcCodeFormulaSyntaxFixedPolynomial bitBound)
    (funcCodeInvalidPairFixedPayloadEnvelope bitBound)
    (funcCodeInvalidPairFixedPayloadEnvelope bitBound)

def funcCodeInvalidTail01FixedPayloadEnvelope (bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (funcCodeFormulaSyntaxFixedPolynomial bitBound)
    (funcCodeInvalidPairFixedPayloadEnvelope bitBound)
    (funcCodeInvalidTail20FixedPayloadEnvelope bitBound)

def compactAdditiveArithmeticFuncCodeInvalidFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (funcCodeFormulaSyntaxFixedPolynomial bitBound)
    (funcCodeInvalidPairFixedPayloadEnvelope bitBound)
    (funcCodeInvalidTail01FixedPayloadEnvelope bitBound)

@[simp] theorem funcCodeInvalidPair00Formula_freeVariables_eq_empty
    (arity code : Nat) :
    (funcCodeInvalidPair00Formula arity code).freeVariables = ∅ := by
  simp [funcCodeInvalidPair00Formula]

@[simp] theorem funcCodeInvalidPair01Formula_freeVariables_eq_empty
    (arity code : Nat) :
    (funcCodeInvalidPair01Formula arity code).freeVariables = ∅ := by
  simp [funcCodeInvalidPair01Formula]

@[simp] theorem funcCodeInvalidPair20Formula_freeVariables_eq_empty
    (arity code : Nat) :
    (funcCodeInvalidPair20Formula arity code).freeVariables = ∅ := by
  simp [funcCodeInvalidPair20Formula]

@[simp] theorem funcCodeInvalidPair21Formula_freeVariables_eq_empty
    (arity code : Nat) :
    (funcCodeInvalidPair21Formula arity code).freeVariables = ∅ := by
  simp [funcCodeInvalidPair21Formula]

@[simp] theorem funcCodeInvalidTail20Formula_freeVariables_eq_empty
    (arity code : Nat) :
    (funcCodeInvalidTail20Formula arity code).freeVariables = ∅ := by
  simp [funcCodeInvalidTail20Formula]

@[simp] theorem funcCodeInvalidTail01Formula_freeVariables_eq_empty
    (arity code : Nat) :
    (funcCodeInvalidTail01Formula arity code).freeVariables = ∅ := by
  simp [funcCodeInvalidTail01Formula]

theorem funcCodeInvalidPair00Formula_code_length_le_fixed
    (arity code bitBound : Nat)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    (binaryFormulaCode
      (funcCodeInvalidPair00Formula arity code)).length <=
      funcCodeFormulaSyntaxFixedPolynomial bitBound := by
  exact funcCodeInvalidPairFormula_code_length_le_fixed arity 0 code 0
    bitBound haritySize hcodeSize (by omega) (by omega)

theorem funcCodeInvalidPair01Formula_code_length_le_fixed
    (arity code bitBound : Nat)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    (binaryFormulaCode
      (funcCodeInvalidPair01Formula arity code)).length <=
      funcCodeFormulaSyntaxFixedPolynomial bitBound := by
  exact funcCodeInvalidPairFormula_code_length_le_fixed arity 0 code 1
    bitBound haritySize hcodeSize (by omega) (by omega)

theorem funcCodeInvalidPair20Formula_code_length_le_fixed
    (arity code bitBound : Nat)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    (binaryFormulaCode
      (funcCodeInvalidPair20Formula arity code)).length <=
      funcCodeFormulaSyntaxFixedPolynomial bitBound := by
  exact funcCodeInvalidPairFormula_code_length_le_fixed arity 2 code 0
    bitBound haritySize hcodeSize (by omega) (by omega)

theorem funcCodeInvalidPair21Formula_code_length_le_fixed
    (arity code bitBound : Nat)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    (binaryFormulaCode
      (funcCodeInvalidPair21Formula arity code)).length <=
      funcCodeFormulaSyntaxFixedPolynomial bitBound := by
  exact funcCodeInvalidPairFormula_code_length_le_fixed arity 2 code 1
    bitBound haritySize hcodeSize (by omega) (by omega)

theorem funcCodeInvalidTail20Formula_code_length_le_fixed
    (arity code bitBound : Nat)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    (binaryFormulaCode
      (funcCodeInvalidTail20Formula arity code)).length <=
      funcCodeFormulaSyntaxFixedPolynomial bitBound := by
  have hfull := compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_code_length_le_fixed
    arity code bitBound haritySize hcodeSize
  unfold compactAdditiveArithmeticFuncCodeInvalidExplicitFormula at hfull
  unfold funcCodeInvalidTail20Formula funcCodeInvalidPair20Formula
    funcCodeInvalidPair21Formula
  simp only [binaryFormulaCode, List.length_append] at hfull ⊢
  omega

theorem funcCodeInvalidTail01Formula_code_length_le_fixed
    (arity code bitBound : Nat)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    (binaryFormulaCode
      (funcCodeInvalidTail01Formula arity code)).length <=
      funcCodeFormulaSyntaxFixedPolynomial bitBound := by
  have hfull := compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_code_length_le_fixed
    arity code bitBound haritySize hcodeSize
  unfold compactAdditiveArithmeticFuncCodeInvalidExplicitFormula at hfull
  unfold funcCodeInvalidTail01Formula funcCodeInvalidTail20Formula
    funcCodeInvalidPair01Formula funcCodeInvalidPair20Formula
    funcCodeInvalidPair21Formula
  simp only [binaryFormulaCode, List.length_append] at hfull ⊢
  omega

end FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBoundsCore
