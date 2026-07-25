import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Shared fixed-resource core for valid arithmetic function codes -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds

def funcCodeValidPairFixedPayloadEnvelope (bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (funcCodeFormulaSyntaxFixedPolynomial bitBound)
    (funcCodeFixedEqFixedPayloadPolynomial bitBound)
    (funcCodeFixedEqFixedPayloadPolynomial bitBound)

def funcCodeValidCase00FixedPayloadEnvelope (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (funcCodeFormulaSyntaxFixedPolynomial bitBound)
    (funcCodeValidPairFixedPayloadEnvelope bitBound)

def funcCodeValidCase01FixedPayloadEnvelope (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (funcCodeFormulaSyntaxFixedPolynomial bitBound)
    (hybridDisjunctionGeneralPayloadEnvelope
      (funcCodeFormulaSyntaxFixedPolynomial bitBound)
      (funcCodeValidPairFixedPayloadEnvelope bitBound))

def funcCodeValidCase20FixedPayloadEnvelope (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (funcCodeFormulaSyntaxFixedPolynomial bitBound)
    (hybridDisjunctionGeneralPayloadEnvelope
      (funcCodeFormulaSyntaxFixedPolynomial bitBound)
      (hybridDisjunctionGeneralPayloadEnvelope
        (funcCodeFormulaSyntaxFixedPolynomial bitBound)
        (funcCodeValidPairFixedPayloadEnvelope bitBound)))

def funcCodeValidCase21FixedPayloadEnvelope (bitBound : Nat) : Nat :=
  funcCodeValidCase20FixedPayloadEnvelope bitBound

def compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  max (funcCodeValidCase00FixedPayloadEnvelope bitBound)
    (max (funcCodeValidCase01FixedPayloadEnvelope bitBound)
      (max (funcCodeValidCase20FixedPayloadEnvelope bitBound)
        (funcCodeValidCase21FixedPayloadEnvelope bitBound)))

theorem binaryFormulaCode_left_le_and
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem binaryFormulaCode_right_le_and
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem binaryFormulaCode_left_le_or
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem binaryFormulaCode_right_le_or
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem funcCodeValidPairCertificate_structuralPayloadBound_le_fixed
    (left leftExpected right rightExpected bitBound : Nat)
    (hleft : left = leftExpected)
    (hright : right = rightExpected)
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound)
    (hleftExpected : leftExpected <= 2)
    (hrightExpected : rightExpected <= 2) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (funcCodeFixedEqCertificate left leftExpected hleft)
          (funcCodeFixedEqCertificate right rightExpected hright)) <=
      funcCodeValidPairFixedPayloadEnvelope bitBound := by
  let leftCertificate :=
    funcCodeFixedEqCertificate left leftExpected hleft
  let rightCertificate :=
    funcCodeFixedEqCertificate right rightExpected hright
  have hleftResource :=
    funcCodeFixedEqCertificate_structuralPayloadBound_le_fixed left
      leftExpected bitBound hleft hleftSize hleftExpected
  have hrightResource :=
    funcCodeFixedEqCertificate_structuralPayloadBound_le_fixed right
      rightExpected bitBound hright hrightSize hrightExpected
  have hleftCode :=
    funcCodeFixedEqFormula_code_length_le_fixed left leftExpected bitBound
      hleftSize hleftExpected
  have hrightCode :=
    funcCodeFixedEqFormula_code_length_le_fixed right rightExpected bitBound
      hrightSize hrightExpected
  have hfullRaw := binaryFormulaCode_and_length_le_local
    (funcCodeFixedEqFormula left leftExpected)
    (funcCodeFixedEqFormula right rightExpected)
  have hfullCode :
      (binaryFormulaCode
        (funcCodeFixedEqFormula left leftExpected ⋏
          funcCodeFixedEqFormula right rightExpected)).length <=
        funcCodeFormulaSyntaxFixedPolynomial bitBound := by
    unfold funcCodeFormulaSyntaxFixedPolynomial
    omega
  exact checkedHybridConjunctionPayloadBound_le_closedGeneral
    leftCertificate rightCertificate
    (funcCodeFixedEqFixedPayloadPolynomial bitBound)
    (funcCodeFixedEqFixedPayloadPolynomial bitBound)
    (funcCodeFormulaSyntaxFixedPolynomial bitBound)
    hleftResource hrightResource (by
      unfold funcCodeFormulaSyntaxFixedPolynomial
      omega)
    (funcCodeFixedEqFormula_freeVariables_eq_empty left leftExpected)
    (funcCodeFixedEqFormula_freeVariables_eq_empty right rightExpected)
    (hleftCode.trans (by
      unfold funcCodeFormulaSyntaxFixedPolynomial
      omega))
    (hrightCode.trans (by
      unfold funcCodeFormulaSyntaxFixedPolynomial
      omega))
    hfullCode

theorem funcCodeValidBranchCode_le_full
    (arity code bitBound : Nat)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound)
    (branch : ValuationFormula)
    (hbranch :
      (binaryFormulaCode branch).length <=
        (binaryFormulaCode
          (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity
            code)).length) :
    (binaryFormulaCode branch).length <=
      funcCodeFormulaSyntaxFixedPolynomial bitBound :=
  hbranch.trans
    (compactAdditiveArithmeticFuncCodeValidExplicitFormula_code_length_le_fixed
      arity code bitBound haritySize hcodeSize)

#print axioms funcCodeValidPairCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore
