import integration.FoundationCompactNumericListedDirectVerifierStepCompleteness

/-!
# Canonical verifier-step witnesses with their exact state layouts

The complete step formula already constructs an independent canonical token
table for each public verifier step.  This module retains the two direct state
layouts together with the 429-column formula witness, so later trace rows can
be connected across their independent tables without a semantic shortcut.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCanonicalStepFormulaLayouts

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierStepCompleteness

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec

theorem CompactNumericVerifierCanonicalStepFormula.exists_witness_with_layouts
    {currentState nextState : CompactNumericVerifierState}
    (hformula : CompactNumericVerifierCanonicalStepFormula
      currentState nextState) :
    ∃ backTokens : List Nat,
      let currentTokens := compactAdditiveEncode currentState
      let nextTokens := compactAdditiveEncode nextState
      let tokens := currentTokens ++ nextTokens ++ backTokens
      let width := (compactBinaryNatPayloadBits tokens).length
      ∃ witness : CompactNumericVerifierStepFormulaWitness
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentTokens.length
          (currentTokens.length + nextTokens.length),
        CompactNumericVerifierStateDirectLayout
            (compactFixedWidthTableCode width tokens) width tokens.length
            0 currentTokens.length currentState ∧
          CompactNumericVerifierStateDirectLayout
            (compactFixedWidthTableCode width tokens) width tokens.length
            currentTokens.length
              (currentTokens.length + nextTokens.length) nextState := by
  rcases hformula with ⟨backTokens, hwitness⟩
  refine ⟨backTokens, ?_⟩
  rcases hwitness with ⟨witness⟩
  refine ⟨witness, ?_⟩
  exact compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState backTokens

theorem exists_compactNumericVerifierStepFormulaWitness_with_layouts_of_public_step
    (currentState : CompactNumericVerifierState) :
    ∃ backTokens : List Nat,
      let nextState := compactNumericVerifierStep currentState
      let currentTokens := compactAdditiveEncode currentState
      let nextTokens := compactAdditiveEncode nextState
      let tokens := currentTokens ++ nextTokens ++ backTokens
      let width := (compactBinaryNatPayloadBits tokens).length
      ∃ witness : CompactNumericVerifierStepFormulaWitness
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentTokens.length
          (currentTokens.length + nextTokens.length),
        CompactNumericVerifierStateDirectLayout
            (compactFixedWidthTableCode width tokens) width tokens.length
            0 currentTokens.length currentState ∧
          CompactNumericVerifierStateDirectLayout
            (compactFixedWidthTableCode width tokens) width tokens.length
            currentTokens.length
              (currentTokens.length + nextTokens.length) nextState := by
  exact
    CompactNumericVerifierCanonicalStepFormula.exists_witness_with_layouts
      (CompactNumericVerifierCanonicalStepFormula.exists_of_public_step
        currentState)

#print axioms
  CompactNumericVerifierCanonicalStepFormula.exists_witness_with_layouts
#print axioms
  exists_compactNumericVerifierStepFormulaWitness_with_layouts_of_public_step

end FoundationCompactNumericListedDirectVerifierCanonicalStepFormulaLayouts
