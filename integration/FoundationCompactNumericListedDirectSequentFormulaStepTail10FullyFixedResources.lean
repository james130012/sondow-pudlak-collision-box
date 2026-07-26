import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedLeaves
import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16AtValuationFullyFixedBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectTableTailCompiler
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-! # Fixed resources for open-index tail 10--21 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedResources

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextSingletonCodeBound
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedLeaves
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound

def compactSequentFormulaStepTail15Formula
    (tokenTable width tokenCount _suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTermAtValuation
        (&0 : ValuationTerm))
      (shortBinaryNumeralTerm row.value.finish) ⋏
    compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
      tokenCount suffixCount valueCount row

def compactSequentFormulaStepTail14Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm valueBoundary)
      (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
      (shortBinaryNumeralTerm row.value.start) ⋏
    compactSequentFormulaStepTail15Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail13Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
        (&0 : ValuationTerm))
      (shortBinaryNumeralTerm row.next.finish) ⋏
    compactSequentFormulaStepTail14Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail12Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTermAtValuation
        (&0 : ValuationTerm))
      (shortBinaryNumeralTerm row.next.start) ⋏
    compactSequentFormulaStepTail13Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail11Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (compactSequentFormulaStepIndexSuccessorTermAtValuation
        (&0 : ValuationTerm))
      (shortBinaryNumeralTerm row.current.finish) ⋏
    compactSequentFormulaStepTail12Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail10Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm suffixBoundary)
      (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
      (shortBinaryNumeralTerm row.current.start) ⋏
    compactSequentFormulaStepTail11Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

theorem compactSequentFormulaStepTail10Formula_eq_direct
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    compactSequentFormulaStepTail10Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount row =
      compactSequentFormulaStepDirectTail10AtValuationIndex tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount row := by
  rfl

def compactSequentFormulaStepTail15FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail16FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail14FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail15FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail13FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail14FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail12FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail13FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail11FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail12FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail10FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail11FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  32 *
    (compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
        numericBound +
      compactSequentFormulaStepTail10FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound row +
      1)

def compactSequentFormulaStepTail15FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail16FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount row)

def compactSequentFormulaStepTail14FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail15FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail13FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail14FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail12FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail13FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail11FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail12FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail10FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail11FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

structure CompactSequentFormulaStepAtValuationFixedResult
    (valuation : Nat -> Nat) (formula : ValuationFormula)
    (payloadResource codeResource : Nat) where
  bound : ExplicitDirectFormulaBound valuation formula payloadResource
  codeLength_le : (binaryFormulaCode formula).length <= codeResource
  freeVariables_subset : formula.freeVariables ⊆ {0}

noncomputable def compactSequentFormulaStepAtValuationFixedConjunction
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    {leftResource rightResource : Nat}
    (leftBound : ExplicitDirectFormulaBound valuation left leftResource)
    (rightBound : ExplicitDirectFormulaBound valuation right rightResource)
    (syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext (left ⋏ right).freeVariables valuation) <=
          syntaxResource)
    (hleft : (binaryFormulaCode left).length <= syntaxResource)
    (hright : (binaryFormulaCode right).length <= syntaxResource)
    (hconjunction :
      (binaryFormulaCode (left ⋏ right)).length <= syntaxResource) :
    ExplicitDirectFormulaBound valuation (left ⋏ right)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
        rightResource) := by
  let proof := compileDirectConjunction leftBound.proof rightBound.proof
  have hraw := compileDirectConjunction_payloadLength_le leftBound.proof
    rightBound.proof leftResource rightResource leftBound.payloadLength_le
    rightBound.payloadLength_le
  have henvelope :
      transparentHybridConjunctionPayloadEnvelope valuation left right
          leftResource rightResource <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
          rightResource := by
    change hybridConjunctionStructuralPayloadEnvelope valuation left right
      leftResource rightResource <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation left
      right leftResource rightResource syntaxResource hpositive hcontext hleft
      hright hconjunction
  exact { proof := proof, payloadLength_le := hraw.trans henvelope }

noncomputable def compactSequentFormulaStepAtValuationFixedConjunctionResult
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    {leftPayload rightPayload leftCode rightCode syntaxResource numericBound :
      Nat}
    (leftBound : ExplicitDirectFormulaBound valuation left leftPayload)
    (rightResult : CompactSequentFormulaStepAtValuationFixedResult valuation
      right rightPayload rightCode)
    (hleftCode : (binaryFormulaCode left).length <= leftCode)
    (hleftVariables : left.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound)
    (hpositive : 1 <= syntaxResource)
    (hcontextEnvelope :
      FoundationCompactPAValuationTermCompilerPublicBounds.valuationContextFormulaCodeSumEnvelope
          1 numericBound (binaryTermCode (&0 : ValuationTerm)).length <=
        syntaxResource)
    (hcodeEnvelope :
      leftCode + rightCode + (binaryNatCode 4).length <= syntaxResource) :
    CompactSequentFormulaStepAtValuationFixedResult valuation (left ⋏ right)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource leftPayload
        rightPayload)
      (leftCode + rightCode + (binaryNatCode 4).length) := by
  have hrawCode := binaryFormulaCode_and_length_le_local left right
  have hrightCode := rightResult.codeLength_le
  have hconjunctionCode : (binaryFormulaCode (left ⋏ right)).length <=
      leftCode + rightCode + (binaryNatCode 4).length := by
    omega
  have hvariables : (left ⋏ right).freeVariables ⊆ {0} := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hleftVariables rightResult.freeVariables_subset
  have hcontextBase := valuationContext_formulaCodeSum_le_singleton
    (left ⋏ right).freeVariables valuation numericBound hvariables hvaluation
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (left ⋏ right).freeVariables valuation) <=
        syntaxResource := hcontextBase.trans hcontextEnvelope
  have hleftSyntax : (binaryFormulaCode left).length <= syntaxResource :=
    hleftCode.trans (by omega)
  have hrightSyntax : (binaryFormulaCode right).length <= syntaxResource :=
    rightResult.codeLength_le.trans (by omega)
  have hconjunctionSyntax :
      (binaryFormulaCode (left ⋏ right)).length <= syntaxResource :=
    hconjunctionCode.trans hcodeEnvelope
  let bound := compactSequentFormulaStepAtValuationFixedConjunction leftBound
    rightResult.bound syntaxResource hpositive hcontext hleftSyntax hrightSyntax
    hconjunctionSyntax
  exact ⟨bound, hconjunctionCode, hvariables⟩

end FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedResources
