import integration.FoundationCompactNumericListedDirectNatListConsRowsTailLeafFixedBounds
import integration.FoundationCompactPAHybridFiveConjunctionSingletonGeneralBounds

/-! # Uniform resources for one natural-list cons tail terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailTerminalResources

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListConsRowsTailEntryFixedBounds

def natListConsRowsTailTerminalContextCodePolynomial
    (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length

def natListConsRowsTailTerminalAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  natListConsRowsTailTerminalContextCodePolynomial numericBound +
    32 * (natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound +
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound +
      (binaryNatCode 4).length + 1) + 1

def natListConsRowsTailTerminalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridFiveConjunctionGeneralPayloadEnvelope
    (natListConsRowsTailTerminalAssemblySyntaxPolynomial numericBound bitBound)
    (natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound)
    (natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound)
    (natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound)
    (natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound)
    (compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound)

theorem natListConsRowsTailTerminalAssemblySyntax_positive
    (numericBound bitBound : Nat) :
    1 <= natListConsRowsTailTerminalAssemblySyntaxPolynomial numericBound
      bitBound := by
  unfold natListConsRowsTailTerminalAssemblySyntaxPolynomial
  omega

theorem natListConsRowsTailTerminalContextCode_le_assembly
    (numericBound bitBound : Nat) :
    natListConsRowsTailTerminalContextCodePolynomial numericBound <=
      natListConsRowsTailTerminalAssemblySyntaxPolynomial numericBound
        bitBound := by
  unfold natListConsRowsTailTerminalAssemblySyntaxPolynomial
  omega

theorem fiveFormulaCode_le_natListConsRowsTailTerminalAssembly
    (formula1 formula2 formula3 formula4 formula5 : ValuationFormula)
    (numericBound bitBound : Nat)
    (hformula1 : (binaryFormulaCode formula1).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound)
    (hformula2 : (binaryFormulaCode formula2).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound)
    (hformula3 : (binaryFormulaCode formula3).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound)
    (hformula4 : (binaryFormulaCode formula4).length <=
      natListConsRowsTailEntryFixedPayloadPolynomial numericBound bitBound)
    (hformula5 : (binaryFormulaCode formula5).length <=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound) :
    (binaryFormulaCode
      (formula1 ⋏
        (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5))))).length <=
      natListConsRowsTailTerminalAssemblySyntaxPolynomial numericBound
        bitBound := by
  have htail4 := binaryFormulaCode_and_length_le_local formula4 formula5
  have htail3 := binaryFormulaCode_and_length_le_local formula3
    (formula4 ⋏ formula5)
  have htail2 := binaryFormulaCode_and_length_le_local formula2
    (formula3 ⋏ (formula4 ⋏ formula5))
  have htotal := binaryFormulaCode_and_length_le_local formula1
    (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5)))
  unfold natListConsRowsTailTerminalAssemblySyntaxPolynomial
  omega

#print axioms natListConsRowsTailTerminalAssemblySyntax_positive
#print axioms natListConsRowsTailTerminalContextCode_le_assembly
#print axioms fiveFormulaCode_le_natListConsRowsTailTerminalAssembly

end FoundationCompactNumericListedDirectNatListConsRowsTailTerminalResources
