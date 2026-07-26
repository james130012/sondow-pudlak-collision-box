import integration.FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
import integration.FoundationCompactNumericListedDirectAdditiveProductSplitFixedPolynomialBounds

/-! # Fixed resource for the nine closed numerical inequalities -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectSequentFormulaStepClosedLeFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectNatListWitnessRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveProductSplitFixedPolynomialBounds
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

private abbrev scalarZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

def compactSequentFormulaStepClosedLeFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  2 * productSplitLeFixedPayloadPolynomial bitBound

private theorem shortNumeralRelation_freeVariables_eq_empty
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : Nat) :
    (LO.FirstOrder.Semiformula.rel relationSymbol
      ![shortBinaryNumeralTerm left,
        shortBinaryNumeralTerm right]).freeVariables = ∅ := by
  ext candidate
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  simp [shortBinaryNumeralTerm_freeVariables_eq_empty]

private theorem shortNumeralRelation_code_length_le_scalar
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel relationSymbol
        ![shortBinaryNumeralTerm left,
          shortBinaryNumeralTerm right])).length <=
      productSplitAtomicFormulaCodePolynomial bitBound := by
  have hleftCode :
      (binaryTermCode (shortBinaryNumeralTerm left)).length <=
        productSplitAtomicTermCodePolynomial bitBound :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hrightCode :
      (binaryTermCode (shortBinaryNumeralTerm right)).length <=
        productSplitAtomicTermCodePolynomial bitBound :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hright
  unfold productSplitAtomicFormulaCodePolynomial
    productSplitAtomicTermCodePolynomial
  exact binaryRelationFormula_code_le_orderAtomic relationSymbol
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
    (binaryNumeralTermCodeEnvelope bitBound) hleftCode hrightCode

theorem witnessRowsValuationLeStructuralPayloadPolynomial_le_fixed
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    witnessRowsValuationLeStructuralPayloadPolynomial
        (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right) <=
      compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound := by
  let args : Fin 2 -> ValuationTerm :=
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right]
  let equalityFormula : ValuationFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula : ValuationFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let termCode := productSplitAtomicTermCodePolynomial bitBound
  let atomicCode := productSplitAtomicFormulaCodePolynomial bitBound
  let atomicResource := productSplitAtomicFixedPayloadPolynomial bitBound
  let syntaxResource := productSplitLeSyntaxPolynomial bitBound
  let equalityResource :=
    compilePositiveRelationPayloadPolynomial scalarZeroValuation
      Language.Eq.eq args
  let strictResource :=
    compilePositiveRelationPayloadPolynomial scalarZeroValuation
      Language.ORing.Rel.lt args
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm left).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm right).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hfirstCode : (binaryTermCode (args 0)).length <= termCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hsecondCode : (binaryTermCode (args 1)).length <= termCode :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hright
  have hequalityResource : equalityResource <= atomicResource := by
    exact compilePositiveRelationPayloadPolynomial_le_fixed
      scalarZeroValuation Language.Eq.eq args 0 termCode hfirst hsecond
      (by rfl) hfirstCode hsecondCode
  have hstrictResource : strictResource <= atomicResource := by
    exact compilePositiveRelationPayloadPolynomial_le_fixed
      scalarZeroValuation Language.ORing.Rel.lt args 0 termCode hfirst hsecond
      (by rfl) hfirstCode hsecondCode
  have hequalityCode :
      (binaryFormulaCode equalityFormula).length <= atomicCode := by
    simpa only [equalityFormula, args] using
      shortNumeralRelation_code_length_le_scalar Language.Eq.eq left right
        bitBound hleft hright
  have hstrictCode :
      (binaryFormulaCode strictFormula).length <= atomicCode := by
    simpa only [strictFormula, args] using
      shortNumeralRelation_code_length_le_scalar Language.ORing.Rel.lt
        left right bitBound hleft hright
  have hequalitySyntax :
      (binaryFormulaCode equalityFormula).length <= syntaxResource :=
    hequalityCode.trans (by
      unfold syntaxResource productSplitLeSyntaxPolynomial
      omega)
  have hstrictSyntax :
      (binaryFormulaCode strictFormula).length <= syntaxResource :=
    hstrictCode.trans (by
      unfold syntaxResource productSplitLeSyntaxPolynomial
      omega)
  have htargetCode :
      (binaryFormulaCode targetFormula).length <= syntaxResource := by
    dsimp only [targetFormula]
    simp only [binaryFormulaCode, List.length_append]
    unfold syntaxResource productSplitLeSyntaxPolynomial
    omega
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    have hequalityClosed : equalityFormula.freeVariables = ∅ := by
      simpa only [equalityFormula, args] using
        shortNumeralRelation_freeVariables_eq_empty Language.Eq.eq left right
    have hstrictClosed : strictFormula.freeVariables = ∅ := by
      simpa only [strictFormula, args] using
        shortNumeralRelation_freeVariables_eq_empty Language.ORing.Rel.lt
          left right
    dsimp only [targetFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hequalityClosed,
      hstrictClosed]
    simp
  have hcontext : formulaCodeSum
      (valuationContext targetFormula.freeVariables scalarZeroValuation) <=
        syntaxResource := by
    rw [htargetClosed]
    simp [valuationContext, formulaCodeSum]
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource productSplitLeSyntaxPolynomial
    omega
  let leftEnvelope :=
    transparentHybridDisjunctionLeftPayloadEnvelope scalarZeroValuation
      equalityFormula strictFormula equalityResource
  let rightEnvelope :=
    transparentHybridDisjunctionRightPayloadEnvelope scalarZeroValuation
      equalityFormula strictFormula strictResource
  have hleftEnvelope :
      leftEnvelope <=
        hybridDisjunctionGeneralPayloadEnvelope syntaxResource
          atomicResource := by
    have hraw :=
      transparentHybridDisjunctionLeftPayloadEnvelope_le_general
        scalarZeroValuation equalityFormula strictFormula equalityResource
        syntaxResource hpositive hcontext hequalitySyntax hstrictSyntax
        htargetCode
    exact hraw.trans (by
      unfold hybridDisjunctionGeneralPayloadEnvelope
      omega)
  have hrightEnvelope :
      rightEnvelope <=
        hybridDisjunctionGeneralPayloadEnvelope syntaxResource
          atomicResource := by
    have hraw :=
      transparentHybridDisjunctionRightPayloadEnvelope_le_general
        scalarZeroValuation equalityFormula strictFormula strictResource
        syntaxResource hpositive hcontext hequalitySyntax hstrictSyntax
        htargetCode
    exact hraw.trans (by
      unfold hybridDisjunctionGeneralPayloadEnvelope
      omega)
  have hpublic :
      witnessRowsValuationLeStructuralPayloadPolynomial
          (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right) <=
        leftEnvelope + rightEnvelope := by
    unfold witnessRowsValuationLeStructuralPayloadPolynomial
    change
      equalityResource + strictResource +
          FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
            (insert equalityFormula
              (valuationContext targetFormula.freeVariables
                scalarZeroValuation)) +
          FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
            (insert strictFormula
              (valuationContext targetFormula.freeVariables
                scalarZeroValuation)) +
          FoundationCompactCertifiedContextProof.CertifiedPAContextProof.disjunctionFullAssemblyCost
            (valuationContext targetFormula.freeVariables scalarZeroValuation)
            equalityFormula strictFormula <=
        leftEnvelope + rightEnvelope
    dsimp only [targetFormula]
    simp only [leftEnvelope, rightEnvelope,
      transparentHybridDisjunctionLeftPayloadEnvelope,
      transparentHybridDisjunctionRightPayloadEnvelope]
    omega
  have hsum :
      leftEnvelope + rightEnvelope <=
        compactSequentFormulaStepClosedLeFixedPayloadPolynomial
          bitBound := by
    calc
      leftEnvelope + rightEnvelope <=
          hybridDisjunctionGeneralPayloadEnvelope syntaxResource
              atomicResource +
            hybridDisjunctionGeneralPayloadEnvelope syntaxResource
              atomicResource :=
        Nat.add_le_add hleftEnvelope hrightEnvelope
      _ = compactSequentFormulaStepClosedLeFixedPayloadPolynomial
          bitBound := by
        simp only [
          compactSequentFormulaStepClosedLeFixedPayloadPolynomial,
          productSplitLeFixedPayloadPolynomial, syntaxResource,
          atomicResource, Nat.two_mul]
  exact hpublic.trans hsum

theorem compactSequentFormulaStepClosedLePublicBound_resource_le_fixed
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound)
    (hle : left <= right) :
    (compactSequentFormulaStepClosedLePublicBound left right hle).resource <=
      compactSequentFormulaStepClosedLeFixedPayloadPolynomial bitBound := by
  change witnessRowsValuationLeStructuralPayloadPolynomial
      (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right) <= _
  exact witnessRowsValuationLeStructuralPayloadPolynomial_le_fixed
    left right bitBound hleft hright

#print axioms
  compactSequentFormulaStepClosedLePublicBound_resource_le_fixed

end FoundationCompactNumericListedDirectSequentFormulaStepClosedLeFixedBound
