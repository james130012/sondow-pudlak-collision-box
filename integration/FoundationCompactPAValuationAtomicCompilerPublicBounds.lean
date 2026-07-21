import integration.FoundationCompactPAValuationAtomicCompilerBounds
import integration.FoundationCompactPAValuationTermCompilerPublicBounds

/-!
# Public resources for valuation atomic compilation

The positive binary-relation compiler normalizes both argument terms before
transporting a closed atomic proof.  This file replaces both exact term
normalization resources by the proved public term polynomials.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAValuationAtomicCompilerPublicBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAUnaryAtomicTransport
open FoundationCompactCertifiedContextualModusPonens

def compilePositiveRelationPayloadPolynomial
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) : Nat :=
  let Gamma := valuationContext
    (LO.FirstOrder.Semiformula.rel relationSymbol args).freeVariables
    valuation
  let firstTerm := shortBinaryNumeralTerm (termValue valuation (args 0))
  let secondTerm := shortBinaryNumeralTerm (termValue valuation (args 1))
  let firstFormula :=
    (“!!firstTerm = !!(args 0)” : LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!secondTerm = !!(args 1)” : LO.FirstOrder.ArithmeticProposition)
  let firstBound := compileTermValueEqualityPayloadPolynomial
      valuation (args 0) +
    weakeningFullAssemblyCost (insert firstFormula Gamma)
  let secondBound := compileTermValueEqualityPayloadPolynomial
      valuation (args 1) +
    weakeningFullAssemblyCost (insert secondFormula Gamma)
  let sourceFormula := binaryRelationFormula
    relationSymbol firstTerm secondTerm
  let targetFormula := binaryRelationFormula relationSymbol (args 0) (args 1)
  let contextualSourceBound :=
    positiveRelationSourcePayloadResource valuation relationSymbol args +
      weakeningFullAssemblyCost (insert sourceFormula Gamma)
  let transportBound := relationTransportImplicationStructuralPayloadBound
    Gamma relationSymbol firstTerm secondTerm (args 0) (args 1)
    firstBound secondBound
  transportBound + contextualSourceBound +
    contextualModusPonensFullAssemblyCost Gamma sourceFormula targetFormula

theorem compilePositiveRelationPayloadResource_le_publicPolynomial
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (hfirst : (args 0).freeVariables ⊆ {0})
    (hsecond : (args 1).freeVariables ⊆ {0}) :
    compilePositiveRelationPayloadResource valuation relationSymbol args ≤
      compilePositiveRelationPayloadPolynomial valuation relationSymbol args := by
  have hfirstBound :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial
      valuation (args 0) hfirst
  have hsecondBound :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial
      valuation (args 1) hsecond
  unfold compilePositiveRelationPayloadResource
    compilePositiveRelationPayloadPolynomial
    relationTransportImplicationStructuralPayloadBound
  dsimp only
  omega

def compileNegativeRelationPayloadPolynomial
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm) : Nat :=
  let Gamma := valuationContext
    (LO.FirstOrder.Semiformula.nrel relationSymbol args).freeVariables
    valuation
  let firstTerm := shortBinaryNumeralTerm (termValue valuation (args 0))
  let secondTerm := shortBinaryNumeralTerm (termValue valuation (args 1))
  let firstFormula :=
    (“!!firstTerm = !!(args 0)” : LO.FirstOrder.ArithmeticProposition)
  let secondFormula :=
    (“!!secondTerm = !!(args 1)” : LO.FirstOrder.ArithmeticProposition)
  let firstForwardBound :=
    compileTermValueEqualityPayloadPolynomial valuation (args 0) +
      weakeningFullAssemblyCost (insert firstFormula Gamma)
  let secondForwardBound :=
    compileTermValueEqualityPayloadPolynomial valuation (args 1) +
      weakeningFullAssemblyCost (insert secondFormula Gamma)
  let firstReverseBound := contextualEqualitySymmetryStructuralPayloadBound
    Gamma firstTerm (args 0) firstForwardBound
  let secondReverseBound := contextualEqualitySymmetryStructuralPayloadBound
    Gamma secondTerm (args 1) secondForwardBound
  let sourceFormula := binaryRelationFormula relationSymbol firstTerm secondTerm
  let targetFormula := binaryRelationFormula relationSymbol (args 0) (args 1)
  let reverseTransportBound := relationTransportImplicationStructuralPayloadBound
    Gamma relationSymbol (args 0) (args 1) firstTerm secondTerm
    firstReverseBound secondReverseBound
  let contextualSourceBound :=
    negativeRelationSourcePayloadResource valuation relationSymbol args +
      weakeningFullAssemblyCost (insert (∼sourceFormula) Gamma)
  reverseTransportBound + contextualSourceBound +
    FoundationCompactCertifiedContextProof.CertifiedPAContextProof.modusTollensFullAssemblyCost
      Gamma targetFormula sourceFormula

theorem compileNegativeRelationPayloadResource_le_publicPolynomial
    (valuation : Nat -> Nat)
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (args : Fin 2 -> ValuationTerm)
    (hfirst : (args 0).freeVariables ⊆ {0})
    (hsecond : (args 1).freeVariables ⊆ {0}) :
    compileNegativeRelationPayloadResource valuation relationSymbol args ≤
      compileNegativeRelationPayloadPolynomial valuation relationSymbol args := by
  have hfirstBound :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial
      valuation (args 0) hfirst
  have hsecondBound :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial
      valuation (args 1) hsecond
  unfold compileNegativeRelationPayloadResource
    compileNegativeRelationPayloadPolynomial
    contextualEqualitySymmetryStructuralPayloadBound
    relationTransportImplicationStructuralPayloadBound
  dsimp only
  omega

#print axioms compilePositiveRelationPayloadResource_le_publicPolynomial
#print axioms compileNegativeRelationPayloadResource_le_publicPolynomial

end FoundationCompactPAValuationAtomicCompilerPublicBounds
