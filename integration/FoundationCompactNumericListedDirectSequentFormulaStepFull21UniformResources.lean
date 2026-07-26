import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail10UniformBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedResources

/-! # Row-independent resources for all twenty-one open-index conjuncts -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformResources

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectSequentFormulaStepTail10UniformBound
open FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedResources
open FoundationCompactNumericListedDirectSequentFormulaStepClosedLeFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound

def compactSequentFormulaStepTail09UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail10UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail08UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail09UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail07UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail08UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail06UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail07UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail05UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail06UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail04UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail05UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail03UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail04UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail02UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail03UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail01UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepClosedLeFullyFixedCodePolynomial bitBound +
    compactSequentFormulaStepTail02UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepFull21UniformSyntaxPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  32 *
    (compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
        numericBound +
      compactSequentFormulaStepTail01UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound + 1)

def compactSequentFormulaStepTail09UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail10UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail08UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail09UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail07UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail08UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail06UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail07UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail05UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail06UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail04UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail05UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail03UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail04UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail02UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail03UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail01UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepFull21UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound)
    (compactSequentFormulaStepTail02UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

end FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformResources
