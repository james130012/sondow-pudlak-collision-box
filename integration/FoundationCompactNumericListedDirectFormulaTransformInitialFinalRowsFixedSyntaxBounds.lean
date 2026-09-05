import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBundleTypes
import integration.FoundationCompactPAHybridSixConjunctionClosedGeneralBounds

/-! # Fixed assembly resources for the seven formula-transform endpoint leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedSyntaxBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridSixConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

def formulaTransformInitialFinalRowsAssemblySyntaxResource
    (stateCount fuel tokenCount numericBound bitBound : Nat) : Nat :=
  parserInitialFinalStateCountPayloadPolynomial stateCount fuel numericBound +
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm 0) numericBound bitBound +
    compactFormulaTransformInitialParserSourceFullyFixedPayloadPolynomial
      numericBound bitBound +
    formulaTransformInitialOutputCountZeroPayloadPolynomial numericBound
      bitBound +
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm fuel) numericBound bitBound +
    parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound +
    sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound +
    6 * (binaryNatCode 4).length + 1

def formulaTransformInitialFinalRowsFullyFixedPayloadPolynomial
    (stateCount fuel tokenCount numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    formulaTransformInitialFinalRowsAssemblySyntaxResource stateCount fuel
      tokenCount numericBound bitBound
  let resource1 :=
    parserInitialFinalStateCountPayloadPolynomial stateCount fuel numericBound
  let resource2 :=
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm 0) numericBound bitBound
  let resource3 :=
    compactFormulaTransformInitialParserSourceFullyFixedPayloadPolynomial
      numericBound bitBound
  let resource4 :=
    formulaTransformInitialOutputCountZeroPayloadPolynomial numericBound
      bitBound
  let resource5 :=
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm fuel) numericBound bitBound
  let resource6 :=
    parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound
  let resource7 :=
    sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound
  let resource67 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    resource6 resource7
  hybridSixConjunctionGeneralPayloadEnvelope syntaxResource resource1 resource2
    resource3 resource4 resource5 resource67

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedSyntaxBounds
