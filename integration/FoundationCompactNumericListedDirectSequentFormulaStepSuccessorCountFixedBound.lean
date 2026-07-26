import integration.FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds

/-! # Fixed resource for the terminal successor-count equality -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepSuccessorCountFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

def compactSequentFormulaStepSuccessorCountTermCodeEnvelope
    (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def compactSequentFormulaStepSuccessorCountFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (compactSequentFormulaStepSuccessorCountTermCodeEnvelope bitBound)

theorem
    compactSequentFormulaStepSuccessorCountPublicBound_resource_le_fixed
    (suffixCount valueCount bitBound : Nat)
    (hsuffixSize : Nat.size suffixCount <= bitBound)
    (hvalueSize : Nat.size valueCount <= bitBound)
    (hequality : suffixCount = valueCount + 1) :
    (compactSequentFormulaStepSuccessorCountPublicBound suffixCount valueCount
      hequality).resource <=
      compactSequentFormulaStepSuccessorCountFixedPayloadPolynomial
        bitBound := by
  let leftTerm := shortBinaryNumeralTerm suffixCount
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm valueCount) + 1’
  let termCodeBound :=
    compactSequentFormulaStepSuccessorCountTermCodeEnvelope bitBound
  have hleftCode : (binaryTermCode leftTerm).length <= termCodeBound := by
    have hraw :=
      binaryNumeralTerm_code_length_le_envelope suffixCount bitBound
        hsuffixSize
    dsimp only [leftTerm, termCodeBound,
      compactSequentFormulaStepSuccessorCountTermCodeEnvelope]
    omega
  have hrightCode : (binaryTermCode rightTerm).length <= termCodeBound := by
    have hvalueCode :=
      binaryNumeralTerm_code_length_le_envelope valueCount bitBound hvalueSize
    have hadd := paAddTerm_code_length_le
      (shortBinaryNumeralTerm valueCount) (‘1’ : ValuationTerm)
    dsimp only [rightTerm, termCodeBound,
      compactSequentFormulaStepSuccessorCountTermCodeEnvelope]
    exact hadd.trans (by omega)
  have hleftVariables : leftTerm.freeVariables ⊆ {0} := by
    dsimp only [leftTerm]
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hrightVariables : rightTerm.freeVariables ⊆ {0} := by
    dsimp only [rightTerm]
    rw [arithmeticAddTerm_freeVariables_eq_union,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    have hone : (‘1’ : ValuationTerm).freeVariables = ∅ := by
      simp [LO.FirstOrder.Semiterm.Operator.operator]
    rw [hone]
    simp
  change
    compilePositiveRelationPayloadPolynomial _ Language.Eq.eq
        ![leftTerm, rightTerm] <=
      compilePositiveRelationFixedPayloadPolynomial 0 termCodeBound
  apply compilePositiveRelationPayloadPolynomial_le_fixed
  · exact hleftVariables
  · exact hrightVariables
  · exact Nat.zero_le _
  · exact hleftCode
  · exact hrightCode

#print axioms
  compactSequentFormulaStepSuccessorCountPublicBound_resource_le_fixed

end FoundationCompactNumericListedDirectSequentFormulaStepSuccessorCountFixedBound
