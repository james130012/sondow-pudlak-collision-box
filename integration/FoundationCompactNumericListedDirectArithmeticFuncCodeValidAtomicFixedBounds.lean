import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

/-! # Fixed atomic resources for arithmetic function-code validity -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

private abbrev funcCodeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate.zeroValuation

def funcCodeFixedEqFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (parserFormulaAtomicTermCodePolynomial bitBound)

def funcCodeFixedNeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compileNegativeRelationFixedPayloadPolynomial 0
    (parserFormulaAtomicTermCodePolynomial bitBound)

def funcCodeFormulaSyntaxFixedPolynomial (bitBound : Nat) : Nat :=
  16 * (parserFormulaAtomicLeafFormulaCodePolynomial bitBound +
    parserFormulaAtomicFormulaCodePolynomial bitBound) +
    16 * (binaryNatCode 4).length + 16 * (binaryNatCode 5).length + 1024

theorem funcCodeFixedEqFormula_code_length_le_fixed
    (value expected bitBound : Nat)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 2) :
    (binaryFormulaCode
      (funcCodeFixedEqFormula value expected)).length <=
      parserFormulaAtomicLeafFormulaCodePolynomial bitBound := by
  have hleft :=
    parserFormulaShortNumeralCode_le value bitBound hvalueSize
  have hright :
      (binaryTermCode (funcCodeFixedNumeralTerm expected)).length <=
        parserFormulaAtomicTermCodePolynomial bitBound := by
    change
      (binaryTermCode
        (FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          expected)).length <=
        parserFormulaAtomicTermCodePolynomial bitBound
    exact parserFormulaFixedTagCode_le expected bitBound
      (hexpected.trans (by omega))
  unfold funcCodeFixedEqFormula funcCodeFixedNumeralTerm
  exact parserFormulaBinaryRelationCode_le_fixed Language.Eq.eq
    (shortBinaryNumeralTerm value)
    (Semiterm.Operator.numeral ℒₒᵣ expected : Semiterm.Const ℒₒᵣ)
    bitBound hleft (by
      simpa [funcCodeFixedNumeralTerm] using hright)

theorem funcCodeFixedNeFormula_code_length_le_fixed
    (value expected bitBound : Nat)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 2) :
    (binaryFormulaCode
      (funcCodeFixedNeFormula value expected)).length <=
      parserFormulaAtomicFormulaCodePolynomial bitBound := by
  have heq := funcCodeFixedEqFormula_code_length_le_fixed value expected
    bitBound hvalueSize hexpected
  have hneg := binaryFormulaCode_neg_length_le
    (funcCodeFixedEqFormula value expected)
  unfold funcCodeFixedNeFormula parserFormulaAtomicFormulaCodePolynomial
  omega

@[simp] theorem funcCodeFixedEqFormula_freeVariables_eq_empty
    (value expected : Nat) :
    (funcCodeFixedEqFormula value expected).freeVariables = ∅ := by
  unfold funcCodeFixedEqFormula
  exact parserFormulaBinaryRelation_freeVariables_eq_empty Language.Eq.eq
    (shortBinaryNumeralTerm value) (funcCodeFixedNumeralTerm expected)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (by
      change
        (FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          expected).freeVariables = ∅
      exact parserFormulaFixedNumeral_freeVariables_eq_empty expected)

@[simp] theorem funcCodeFixedNeFormula_freeVariables_eq_empty
    (value expected : Nat) :
    (funcCodeFixedNeFormula value expected).freeVariables = ∅ := by
  unfold funcCodeFixedNeFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_not,
    funcCodeFixedEqFormula_freeVariables_eq_empty]

theorem compactAdditiveArithmeticFuncCodeValidExplicitFormula_code_length_le_fixed
    (arity code bitBound : Nat)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code)).length <=
      funcCodeFormulaSyntaxFixedPolynomial bitBound := by
  have ha0 := funcCodeFixedEqFormula_code_length_le_fixed arity 0 bitBound
    haritySize (by omega)
  have ha2 := funcCodeFixedEqFormula_code_length_le_fixed arity 2 bitBound
    haritySize (by omega)
  have hc0 := funcCodeFixedEqFormula_code_length_le_fixed code 0 bitBound
    hcodeSize (by omega)
  have hc1 := funcCodeFixedEqFormula_code_length_le_fixed code 1 bitBound
    hcodeSize (by omega)
  unfold compactAdditiveArithmeticFuncCodeValidExplicitFormula
    funcCodeFormulaSyntaxFixedPolynomial
  simp only [binaryFormulaCode, List.length_append] at *
  omega

theorem compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_code_length_le_fixed
    (arity code bitBound : Nat)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveArithmeticFuncCodeInvalidExplicitFormula arity code)).length <=
      funcCodeFormulaSyntaxFixedPolynomial bitBound := by
  have ha0 := funcCodeFixedNeFormula_code_length_le_fixed arity 0 bitBound
    haritySize (by omega)
  have ha2 := funcCodeFixedNeFormula_code_length_le_fixed arity 2 bitBound
    haritySize (by omega)
  have hc0 := funcCodeFixedNeFormula_code_length_le_fixed code 0 bitBound
    hcodeSize (by omega)
  have hc1 := funcCodeFixedNeFormula_code_length_le_fixed code 1 bitBound
    hcodeSize (by omega)
  unfold compactAdditiveArithmeticFuncCodeInvalidExplicitFormula
    funcCodeFormulaSyntaxFixedPolynomial
  simp only [binaryFormulaCode, List.length_append] at *
  omega

@[simp] theorem
    compactAdditiveArithmeticFuncCodeValidExplicitFormula_freeVariables_eq_empty
    (arity code : Nat) :
    (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code).freeVariables =
      ∅ := by
  unfold compactAdditiveArithmeticFuncCodeValidExplicitFormula
  simp

@[simp] theorem
    compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_freeVariables_eq_empty
    (arity code : Nat) :
    (compactAdditiveArithmeticFuncCodeInvalidExplicitFormula arity code).freeVariables =
      ∅ := by
  unfold compactAdditiveArithmeticFuncCodeInvalidExplicitFormula
  simp

theorem funcCodeFixedEqCertificate_structuralPayloadBound_le_fixed
    (value expected bitBound : Nat)
    (heq : value = expected)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 2) :
    hybridFormulaStructuralPayloadBound
        (funcCodeFixedEqCertificate value expected heq) <=
      funcCodeFixedEqFixedPayloadPolynomial bitBound := by
  change compilePositiveRelationPayloadResource funcCodeZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, funcCodeFixedNumeralTerm expected] <= _
  unfold funcCodeFixedEqFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    funcCodeZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm value) (funcCodeFixedNumeralTerm expected)
    0 (parserFormulaAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (by
      simp [funcCodeFixedNumeralTerm,
        LO.FirstOrder.Semiterm.Operator.operator])
    (parserFormulaShortNumeralCode_le value bitBound hvalueSize)
    (by
      change
        (binaryTermCode
          (FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
            expected)).length <=
          parserFormulaAtomicTermCodePolynomial bitBound
      exact parserFormulaFixedTagCode_le expected bitBound
        (hexpected.trans (by omega)))

theorem funcCodeFixedNeCertificate_structuralPayloadBound_le_fixed
    (value expected bitBound : Nat)
    (hne : value ≠ expected)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 2) :
    hybridFormulaStructuralPayloadBound
        (funcCodeFixedNeCertificate value expected hne) <=
      funcCodeFixedNeFixedPayloadPolynomial bitBound := by
  change compileNegativeRelationPayloadResource funcCodeZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, funcCodeFixedNumeralTerm expected] <= _
  unfold funcCodeFixedNeFixedPayloadPolynomial
  exact compileNegativeRelationPayloadResource_le_fixed_of_closed
    funcCodeZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm value) (funcCodeFixedNumeralTerm expected)
    0 (parserFormulaAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (by
      simp [funcCodeFixedNumeralTerm,
        LO.FirstOrder.Semiterm.Operator.operator])
    (parserFormulaShortNumeralCode_le value bitBound hvalueSize)
    (by
      change
        (binaryTermCode
          (FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
            expected)).length <=
          parserFormulaAtomicTermCodePolynomial bitBound
      exact parserFormulaFixedTagCode_le expected bitBound
        (hexpected.trans (by omega)))

#print axioms funcCodeFixedEqCertificate_structuralPayloadBound_le_fixed
#print axioms funcCodeFixedNeCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
