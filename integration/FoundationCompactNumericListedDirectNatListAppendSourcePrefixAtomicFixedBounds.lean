import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Fixed arithmetic leaves for source-prefix append

The non-strict order and equality leaves are bounded solely from closedness and
one common term-code coordinate.  No concrete numeral or proof object remains
in the resulting resources.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds

private abbrev appendSourceZeroValuationFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.zeroValuation

def appendSourcePrefixAtomicFormulaCodePolynomial
    (termCodeBound : Nat) : Nat :=
  orderAtomicFormulaCodeEnvelope termCodeBound

def appendSourcePrefixAtomicFixedPayloadPolynomial
    (termCodeBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0 termCodeBound

def appendSourcePrefixLeSyntaxPolynomial
    (termCodeBound : Nat) : Nat :=
  2 * appendSourcePrefixAtomicFormulaCodePolynomial termCodeBound + 9

def appendSourcePrefixLeFixedPayloadPolynomial
    (termCodeBound : Nat) : Nat :=
  2 * appendSourcePrefixAtomicFixedPayloadPolynomial termCodeBound +
    3 * generalContextAssemblyEnvelope
      (appendSourcePrefixLeSyntaxPolynomial termCodeBound)

def appendSourcePrefixValuationLeStructuralEnvelopeAt
    (valuation : Nat -> Nat) (left right : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![left, right]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables valuation
  compilePositiveRelationPayloadResource valuation Language.Eq.eq args +
    compilePositiveRelationPayloadResource valuation Language.ORing.Rel.lt
      args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

private theorem closedBinaryRelation_freeVariables_eq_empty
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right]).freeVariables =
      ∅ := by
  ext candidate
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  simp [hleft, hright]

private theorem closedBinaryRelation_code_le_fixed
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) (termCodeBound : Nat)
    (hleft : (binaryTermCode left).length <= termCodeBound)
    (hright : (binaryTermCode right).length <= termCodeBound) :
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right])).length <=
        appendSourcePrefixAtomicFormulaCodePolynomial termCodeBound := by
  unfold appendSourcePrefixAtomicFormulaCodePolynomial
  exact binaryRelationFormula_code_le_orderAtomic relationSymbol left right
    termCodeBound hleft hright

theorem appendSourcePrefixValuationEqStructuralEnvelope_le_fixed
    (left right : ValuationTerm) (termCodeBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <= termCodeBound)
    (hrightCode : (binaryTermCode right).length <= termCodeBound) :
    appendSourcePrefixValuationEqStructuralEnvelope left right <=
      appendSourcePrefixAtomicFixedPayloadPolynomial termCodeBound := by
  unfold appendSourcePrefixValuationEqStructuralEnvelope
    appendSourcePrefixAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    appendSourceZeroValuationFixed Language.Eq.eq left right 0 termCodeBound
    hleftClosed hrightClosed hleftCode hrightCode

theorem appendSourcePrefixValuationLeStructuralEnvelopeAt_le_fixed
    (valuation : Nat -> Nat) (left right : ValuationTerm)
    (termCodeBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <= termCodeBound)
    (hrightCode : (binaryTermCode right).length <= termCodeBound) :
    appendSourcePrefixValuationLeStructuralEnvelopeAt valuation left right <=
      appendSourcePrefixLeFixedPayloadPolynomial termCodeBound := by
  let args : Fin 2 -> ValuationTerm := ![left, right]
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables valuation
  let atomicCode :=
    appendSourcePrefixAtomicFormulaCodePolynomial termCodeBound
  let syntaxCode := appendSourcePrefixLeSyntaxPolynomial termCodeBound
  let atomicResource :=
    appendSourcePrefixAtomicFixedPayloadPolynomial termCodeBound
  have hequalityClosed : equalityFormula.freeVariables = ∅ := by
    dsimp only [equalityFormula, args]
    exact closedBinaryRelation_freeVariables_eq_empty Language.Eq.eq left
      right hleftClosed hrightClosed
  have hstrictClosed : strictFormula.freeVariables = ∅ := by
    dsimp only [strictFormula, args]
    exact closedBinaryRelation_freeVariables_eq_empty
      Language.ORing.Rel.lt left right hleftClosed hrightClosed
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    dsimp only [targetFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hequalityClosed,
      hstrictClosed]
    simp
  have hGamma : Gamma = ∅ := by
    dsimp only [Gamma]
    rw [htargetClosed]
    simp [valuationContext]
  have hequalityCode :
      (binaryFormulaCode equalityFormula).length <= atomicCode := by
    dsimp only [equalityFormula, args, atomicCode]
    exact closedBinaryRelation_code_le_fixed Language.Eq.eq left right
      termCodeBound hleftCode hrightCode
  have hstrictCode :
      (binaryFormulaCode strictFormula).length <= atomicCode := by
    dsimp only [strictFormula, args, atomicCode]
    exact closedBinaryRelation_code_le_fixed Language.ORing.Rel.lt left right
      termCodeBound hleftCode hrightCode
  have hequalitySyntax :
      (binaryFormulaCode equalityFormula).length <= syntaxCode :=
    hequalityCode.trans (by
      unfold syntaxCode appendSourcePrefixLeSyntaxPolynomial
      omega)
  have hstrictSyntax :
      (binaryFormulaCode strictFormula).length <= syntaxCode :=
    hstrictCode.trans (by
      unfold syntaxCode appendSourcePrefixLeSyntaxPolynomial
      omega)
  have htargetCodeRaw :=
    FoundationCompactListedLocalCostPrimitives.binaryFormulaCode_or_length_le
      equalityFormula strictFormula
  have htargetCode :
      (binaryFormulaCode targetFormula).length <= syntaxCode := by
    dsimp only [targetFormula]
    exact htargetCodeRaw.trans (by
      unfold syntaxCode appendSourcePrefixLeSyntaxPolynomial
      omega)
  have hcontext : formulaCodeSum Gamma <= syntaxCode := by
    rw [hGamma]
    simp [formulaCodeSum]
  have hpositive : 1 <= syntaxCode := by
    unfold syntaxCode appendSourcePrefixLeSyntaxPolynomial
    omega
  have hequalityResource :
      compilePositiveRelationPayloadResource valuation
          Language.Eq.eq args <= atomicResource := by
    dsimp only [args, atomicResource]
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed
      valuation Language.Eq.eq left right 0 termCodeBound
      hleftClosed hrightClosed hleftCode hrightCode
  have hstrictResource :
      compilePositiveRelationPayloadResource valuation
          Language.ORing.Rel.lt args <= atomicResource := by
    dsimp only [args, atomicResource]
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed
      valuation Language.ORing.Rel.lt left right 0
      termCodeBound hleftClosed hrightClosed hleftCode hrightCode
  have hweakEquality := weakeningFullAssemblyCost_le_general
    (insert equalityFormula Gamma) syntaxCode (by
      have hraw := formulaCodeSum_insert_le Gamma equalityFormula
      unfold generalContextCoordinate
      omega)
  have hweakStrict := weakeningFullAssemblyCost_le_general
    (insert strictFormula Gamma) syntaxCode (by
      have hraw := formulaCodeSum_insert_le Gamma strictFormula
      unfold generalContextCoordinate
      omega)
  have hdisjunction := disjunctionFullAssemblyCost_le_general Gamma
    equalityFormula strictFormula syntaxCode hpositive hcontext
    hequalitySyntax hstrictSyntax htargetCode
  unfold appendSourcePrefixValuationLeStructuralEnvelopeAt
    appendSourcePrefixLeFixedPayloadPolynomial
  dsimp only [args, equalityFormula, strictFormula, targetFormula, Gamma,
    atomicCode, syntaxCode, atomicResource]
    at hequalityResource hstrictResource hweakEquality hweakStrict
      hdisjunction ⊢
  omega

theorem appendSourcePrefixValuationLeStructuralEnvelope_le_fixed
    (left right : ValuationTerm) (termCodeBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <= termCodeBound)
    (hrightCode : (binaryTermCode right).length <= termCodeBound) :
    appendSourcePrefixValuationLeStructuralEnvelope left right <=
      appendSourcePrefixLeFixedPayloadPolynomial termCodeBound := by
  unfold appendSourcePrefixValuationLeStructuralEnvelope
  change appendSourcePrefixValuationLeStructuralEnvelopeAt (fun _ => 0)
      left right <= _
  exact appendSourcePrefixValuationLeStructuralEnvelopeAt_le_fixed (fun _ => 0)
    left right termCodeBound hleftClosed hrightClosed hleftCode hrightCode

#print axioms appendSourcePrefixValuationEqStructuralEnvelope_le_fixed
#print axioms appendSourcePrefixValuationLeStructuralEnvelopeAt_le_fixed
#print axioms appendSourcePrefixValuationLeStructuralEnvelope_le_fixed

end FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds
