import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepClosedLeFixedBound

/-! # Fixed resources for all twenty-one open-index sequent-step conjuncts -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedResources

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedResources
open FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepClosedLeFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound

def compactSequentFormulaStepClosedLeFormula
    (left right : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm left) ≤ !!(shortBinaryNumeralTerm right)”

private theorem shortNumeralRelation_freeVariables_eq_empty
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : Nat) :
    (LO.FirstOrder.Semiformula.rel relationSymbol
      ![shortBinaryNumeralTerm left,
        shortBinaryNumeralTerm right]).freeVariables = ∅ := by
  ext candidate
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  simp [shortBinaryNumeralTerm_freeVariables_eq_empty]

theorem compactSequentFormulaStepClosedLeFormula_freeVariables_eq_empty
    (left right : Nat) :
    (compactSequentFormulaStepClosedLeFormula left right).freeVariables = ∅ := by
  unfold compactSequentFormulaStepClosedLeFormula
  rw [LO.FirstOrder.Semiformula.Operator.le_def,
    LO.FirstOrder.Semiformula.freeVariables_or]
  have hequality := shortNumeralRelation_freeVariables_eq_empty
    Language.Eq.eq left right
  have hstrict := shortNumeralRelation_freeVariables_eq_empty
    Language.ORing.Rel.lt left right
  change
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq
        ![shortBinaryNumeralTerm left,
          shortBinaryNumeralTerm right]).freeVariables ∪
      (LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm left,
          shortBinaryNumeralTerm right]).freeVariables = ∅
  rw [hequality, hstrict]
  simp

def compactSequentFormulaStepTail09Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepClosedLeFormula row.value.count tokenCount ⋏
    compactSequentFormulaStepDirectTail10AtValuationIndex tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail08Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepClosedLeFormula row.value.finish tokenCount ⋏
    compactSequentFormulaStepTail09Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail07Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepClosedLeFormula row.value.start tokenCount ⋏
    compactSequentFormulaStepTail08Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail06Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepClosedLeFormula row.next.count tokenCount ⋏
    compactSequentFormulaStepTail07Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail05Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepClosedLeFormula row.next.finish tokenCount ⋏
    compactSequentFormulaStepTail06Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail04Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepClosedLeFormula row.next.start tokenCount ⋏
    compactSequentFormulaStepTail05Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail03Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepClosedLeFormula row.current.count tokenCount ⋏
    compactSequentFormulaStepTail04Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail02Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepClosedLeFormula row.current.finish tokenCount ⋏
    compactSequentFormulaStepTail03Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

def compactSequentFormulaStepTail01Formula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : ValuationFormula :=
  compactSequentFormulaStepClosedLeFormula row.current.start tokenCount ⋏
    compactSequentFormulaStepTail02Formula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount row

theorem compactSequentFormulaStepTail01Formula_eq_directParts
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    compactSequentFormulaStepTail01Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount row =
      compactSequentFormulaStepDirectPartsFormulaAtValuationIndex tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        (&0 : ValuationTerm) row := by
  rfl

def compactSequentFormulaStepClosedLeFullyFixedCodePolynomial
    (bitBound : Nat) : Nat :=
  compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound

def compactSequentFormulaStepTail09FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail10FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail08FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail09FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail07FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail08FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail06FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail07FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail05FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail06FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail04FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail05FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail03FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail04FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail02FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail03FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail01FullyFixedCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail02FullyFixedCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row +
    (binaryNatCode 4).length

def compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  32 *
    (compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
        numericBound +
      compactSequentFormulaStepTail01FullyFixedCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound row +
      1)

def compactSequentFormulaStepTail09FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail10FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail08FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail09FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail07FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail08FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail06FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail07FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail05FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail06FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail04FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail05FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail03FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail04FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail02FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail03FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

def compactSequentFormulaStepTail01FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail02FullyFixedPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound row)

noncomputable def compactSequentFormulaStepClosedLeFullyFixedResult
    (valuation : Nat -> Nat) (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound)
    (hle : left <= right) :
    CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepClosedLeFormula left right)
      (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
      (compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound) := by
  let closed := compactSequentFormulaStepClosedLePublicBound left right hle
  have hresource :=
    compactSequentFormulaStepClosedLePublicBound_resource_le_fixed left right
      bitBound hleft hright hle
  have hclosed :=
    compactSequentFormulaStepClosedLeFormula_freeVariables_eq_empty left right
  have hcontext : (∅ : Finset ValuationFormula) =
      valuationContext
        (compactSequentFormulaStepClosedLeFormula left right).freeVariables
        valuation := by
    rw [hclosed]
    simp [valuationContext]
  let proof := CertifiedPAContextProof.castContext hcontext closed.proof
  have hpayload : proof.payloadLength <=
      compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound := by
    dsimp only [proof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact closed.payloadLength_le.trans hresource
  have hcode :
      (binaryFormulaCode
        (compactSequentFormulaStepClosedLeFormula left right)).length <=
        compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound := by
    exact
      (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        proof).trans hpayload
  exact
    { bound := { proof := proof, payloadLength_le := hpayload }
      codeLength_le := hcode
      freeVariables_subset := by rw [hclosed]; simp }

#print axioms compactSequentFormulaStepTail01Formula_eq_directParts
#print axioms compactSequentFormulaStepClosedLeFullyFixedResult

end FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedResources
