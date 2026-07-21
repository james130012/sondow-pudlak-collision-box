import integration.FoundationCompactPABitMembershipValuationTransportPolynomialBounds
import integration.FoundationCompactPAValuationTermCompilerPublicBounds

/-!
# Public polynomial bounds for valuation bit literals

This module replaces every remaining exact resource in the positive and
negative valuation-bit compilers by a resource computed from input syntax.
The only side condition is the fixed-width invariant that both input terms
use at most the branch variable `0`.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPABitMembershipValuationCompilerPublicBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipRuleCompilerBounds
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPABitMembershipValuationTransportPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds

/-! ## Fixed formula-code envelope for the embedded bit predicate -/

def binaryBitEmbeddedFormula :
    LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
  Rewriting.emb bitDef.val

def binaryBitAtomFirstSubstitutionBudget : Nat :=
  1 + formulaSymbolCount binaryBitEmbeddedFormula

def binaryBitAtomFirstSubstitutionEnvelope (termBound : Nat) : Nat :=
  (termBound +
      2 * binaryBitAtomFirstSubstitutionBudget * termBound) *
    (binaryFormulaCode binaryBitEmbeddedFormula).length

/-- Fixed polynomial in a common code bound for the two substituted terms. -/
def binaryBitAtomFormulaCodeEnvelope (termBound : Nat) : Nat :=
  FoundationCompactPABinaryNumeralAdditionBounds.substitutionFormulaCodeEnvelope
    (binaryBitAtomFirstSubstitutionEnvelope termBound) termBound

theorem binaryBitAtomAtTerms_code_length_le_uniform
    (index value : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode (binaryBitAtomAtTerms index value)).length <=
      binaryBitAtomFormulaCodeEnvelope termBound := by
  let intermediate :=
    FoundationCompactSyntaxTransformationCodeBounds.substituteFormulaAlong
      value 1 binaryBitEmbeddedFormula rfl
  have hintermediateEq :
      intermediate/[index] = binaryBitAtomAtTerms index value := by
    change
      (Rew.subst ![index]) ▹
          ((Rew.subst ![value]).q ▹ binaryBitEmbeddedFormula) =
        (Rew.subst ![index, value]) ▹ binaryBitEmbeddedFormula
    rw [← TransitiveRewriting.comp_app]
    apply Semiformula.ext_rewAux'
    rw [Rew.q_subst, Rew.subst_comp_subst]
    congr 1
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => simp [Rew.subst_bvar]
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => simp
        | succ coordinate => exact Fin.elim0 coordinate
  have hraw :=
    FoundationCompactSyntaxTransformationCodeBounds.binaryFormulaCode_substitutionAlong_length_le
      value binaryBitEmbeddedFormula 1
        binaryBitAtomFirstSubstitutionBudget rfl (by
          unfold binaryBitAtomFirstSubstitutionBudget
          omega)
  have hsymbols := termSymbolCount_le_binaryTermCode_length value
  have hsymbolsBound : termSymbolCount value <= termBound :=
    hsymbols.trans hvalue
  have hfactor :
      FoundationCompactSyntaxTransformationCodeBounds.substitutionCodeFactor
          value binaryBitAtomFirstSubstitutionBudget <=
        termBound +
          2 * binaryBitAtomFirstSubstitutionBudget * termBound := by
    rw [FoundationCompactSyntaxTransformationCodeBounds.substitutionCodeFactor_eq]
    exact Nat.add_le_add hvalue
      (Nat.mul_le_mul_left
        (2 * binaryBitAtomFirstSubstitutionBudget) hsymbolsBound)
  have hintermediateCode : (binaryFormulaCode intermediate).length <=
      binaryBitAtomFirstSubstitutionEnvelope termBound := by
    exact hraw.trans (by
      unfold binaryBitAtomFirstSubstitutionEnvelope
      exact Nat.mul_le_mul_right _ hfactor)
  have hsecond :=
    FoundationCompactPABinaryNumeralAdditionBounds.binaryFormulaCode_substitution_one_length_le_envelope
      intermediate index (binaryBitAtomFirstSubstitutionEnvelope termBound)
        termBound hintermediateCode hindex
  rw [hintermediateEq] at hsecond
  exact hsecond

def binaryBitLiteralFormulaCodeEnvelope (termBound : Nat) : Nat :=
  2 * binaryBitAtomFormulaCodeEnvelope termBound + 1

theorem binaryBitLiteralAtTerms_code_length_le_uniform
    (expected : Bool)
    (index value : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (termBound : Nat)
    (hindex : (binaryTermCode index).length <= termBound)
    (hvalue : (binaryTermCode value).length <= termBound) :
    (binaryFormulaCode
        (binaryBitLiteralAtTerms expected index value)).length <=
      binaryBitLiteralFormulaCodeEnvelope termBound := by
  have hatom := binaryBitAtomAtTerms_code_length_le_uniform
    index value termBound hindex hvalue
  cases expected with
  | false =>
      have hnegation :=
        FoundationCompactSyntaxTransformationCodeBounds.binaryFormulaCode_neg_length_le
          (binaryBitAtomAtTerms index value)
      simp only [binaryBitLiteralAtTerms, Bool.false_eq_true, ↓reduceIte]
      unfold binaryBitLiteralFormulaCodeEnvelope
      omega
  | true =>
      simp only [binaryBitLiteralAtTerms, ↓reduceIte]
      unfold binaryBitLiteralFormulaCodeEnvelope
      omega

def binaryBitValuationFormulaBaseCodeEnvelope (termBound : Nat) : Nat :=
  binaryBitLiteralFormulaCodeEnvelope termBound +
    binaryBitAtomFormulaCodeEnvelope termBound +
    FoundationCompactPABinaryNumeralAdditionBounds.paFormulaCodeEnvelope
      termBound + 1

theorem binaryBitValuationBaseFormulaCodes_le_uniform
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) (termBound : Nat)
    (hshortIndex :
      (binaryTermCode
        (shortBinaryNumeralTerm (termValue valuation indexTerm))).length <=
          termBound)
    (hindex : (binaryTermCode indexTerm).length <= termBound)
    (hshortValue :
      (binaryTermCode
        (shortBinaryNumeralTerm (termValue valuation valueTerm))).length <=
          termBound)
    (hvalue : (binaryTermCode valueTerm).length <= termBound) :
    (binaryFormulaCode
        (binaryBitValuationSourceFormula expected valuation
          indexTerm valueTerm)).length <=
          binaryBitValuationFormulaBaseCodeEnvelope termBound ∧
      (binaryFormulaCode
        (binaryBitValuationSourceAtomFormula valuation
          indexTerm valueTerm)).length <=
          binaryBitValuationFormulaBaseCodeEnvelope termBound ∧
      (binaryFormulaCode
        (binaryBitValuationIndexEqualityFormula valuation
          indexTerm)).length <=
          binaryBitValuationFormulaBaseCodeEnvelope termBound ∧
      (binaryFormulaCode
        (binaryBitValuationIndexReverseEqualityFormula valuation
          indexTerm)).length <=
          binaryBitValuationFormulaBaseCodeEnvelope termBound ∧
      (binaryFormulaCode
        (binaryBitValuationIndexAtomFormula valuation
          indexTerm valueTerm)).length <=
          binaryBitValuationFormulaBaseCodeEnvelope termBound ∧
      (binaryFormulaCode
        (binaryBitValuationValueEqualityFormula valuation
          valueTerm)).length <=
          binaryBitValuationFormulaBaseCodeEnvelope termBound ∧
      (binaryFormulaCode
        (binaryBitValuationValueReverseEqualityFormula valuation
          valueTerm)).length <=
          binaryBitValuationFormulaBaseCodeEnvelope termBound ∧
      (binaryFormulaCode
        (binaryBitValuationResultAtomFormula
          indexTerm valueTerm)).length <=
          binaryBitValuationFormulaBaseCodeEnvelope termBound := by
  have hsource := binaryBitLiteralAtTerms_code_length_le_uniform expected
    (shortBinaryNumeralTerm (termValue valuation indexTerm))
    (shortBinaryNumeralTerm (termValue valuation valueTerm)) termBound
    hshortIndex hshortValue
  have hsourceAtom := binaryBitAtomAtTerms_code_length_le_uniform
    (shortBinaryNumeralTerm (termValue valuation indexTerm))
    (shortBinaryNumeralTerm (termValue valuation valueTerm)) termBound
    hshortIndex hshortValue
  have hindexEquality :=
    FoundationCompactPABinaryNumeralAdditionBounds.equalityFormula_code_length_le_paEnvelope
      (shortBinaryNumeralTerm (termValue valuation indexTerm)) indexTerm
      termBound hshortIndex hindex
  have hindexReverse :=
    FoundationCompactPABinaryNumeralAdditionBounds.equalityFormula_code_length_le_paEnvelope
      indexTerm (shortBinaryNumeralTerm (termValue valuation indexTerm))
      termBound hindex hshortIndex
  have hindexAtom := binaryBitAtomAtTerms_code_length_le_uniform
    indexTerm (shortBinaryNumeralTerm (termValue valuation valueTerm))
    termBound hindex hshortValue
  have hvalueEquality :=
    FoundationCompactPABinaryNumeralAdditionBounds.equalityFormula_code_length_le_paEnvelope
      (shortBinaryNumeralTerm (termValue valuation valueTerm)) valueTerm
      termBound hshortValue hvalue
  have hvalueReverse :=
    FoundationCompactPABinaryNumeralAdditionBounds.equalityFormula_code_length_le_paEnvelope
      valueTerm (shortBinaryNumeralTerm (termValue valuation valueTerm))
      termBound hvalue hshortValue
  have hresult := binaryBitAtomAtTerms_code_length_le_uniform
    indexTerm valueTerm termBound hindex hvalue
  unfold binaryBitValuationSourceFormula
    binaryBitValuationSourceAtomFormula
    binaryBitValuationIndexEqualityFormula
    binaryBitValuationIndexReverseEqualityFormula
    binaryBitValuationIndexAtomFormula
    binaryBitValuationValueEqualityFormula
    binaryBitValuationValueReverseEqualityFormula
    binaryBitValuationResultAtomFormula
    binaryBitValuationFormulaBaseCodeEnvelope
  constructor <;> omega

def binaryBitValuationFormulaStageOneCodeEnvelope (termBound : Nat) : Nat :=
  4 * (binaryBitValuationFormulaBaseCodeEnvelope termBound +
    (binaryNatCode 5).length + 1)

def binaryBitValuationFormulaStageTwoCodeEnvelope (termBound : Nat) : Nat :=
  4 * (binaryBitValuationFormulaStageOneCodeEnvelope termBound +
    (binaryNatCode 4).length + (binaryNatCode 5).length + 1)

def binaryBitValuationFormulaClosureCodeEnvelope (termBound : Nat) : Nat :=
  2 * binaryBitValuationFormulaStageTwoCodeEnvelope termBound + 1

theorem binaryBitValuation_base_le_closure (termBound : Nat) :
    binaryBitValuationFormulaBaseCodeEnvelope termBound <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound := by
  unfold binaryBitValuationFormulaClosureCodeEnvelope
    binaryBitValuationFormulaStageTwoCodeEnvelope
    binaryBitValuationFormulaStageOneCodeEnvelope
  omega

theorem binaryBitValuation_implication_base_code_le_stageOne
    (left right : ValuationFormula) (termBound : Nat)
    (hleft : (binaryFormulaCode left).length <=
      binaryBitValuationFormulaBaseCodeEnvelope termBound)
    (hright : (binaryFormulaCode right).length <=
      binaryBitValuationFormulaBaseCodeEnvelope termBound) :
    (binaryFormulaCode (left 🡒 right)).length <=
      binaryBitValuationFormulaStageOneCodeEnvelope termBound := by
  have hraw :=
    FoundationCompactPABinaryNumeralAdditionBounds.binaryFormulaCode_implication_length_le
      left right
  unfold binaryBitValuationFormulaStageOneCodeEnvelope
  omega

theorem binaryBitValuation_implication_second_code_le_stageTwo
    (left right : ValuationFormula) (termBound : Nat)
    (hleft : (binaryFormulaCode left).length <=
      binaryBitValuationFormulaBaseCodeEnvelope termBound)
    (hright : (binaryFormulaCode right).length <=
      binaryBitValuationFormulaStageOneCodeEnvelope termBound) :
    (binaryFormulaCode (left 🡒 right)).length <=
      binaryBitValuationFormulaStageTwoCodeEnvelope termBound := by
  have hraw :=
    FoundationCompactPABinaryNumeralAdditionBounds.binaryFormulaCode_implication_length_le
      left right
  unfold binaryBitValuationFormulaStageTwoCodeEnvelope
    binaryBitValuationFormulaStageOneCodeEnvelope at *
  omega

theorem binaryBitValuation_stageTwo_le_closure (termBound : Nat) :
    binaryBitValuationFormulaStageTwoCodeEnvelope termBound <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound := by
  unfold binaryBitValuationFormulaClosureCodeEnvelope
  omega

theorem binaryBitValuation_stageOne_le_stageTwo (termBound : Nat) :
    binaryBitValuationFormulaStageOneCodeEnvelope termBound <=
      binaryBitValuationFormulaStageTwoCodeEnvelope termBound := by
  unfold binaryBitValuationFormulaStageTwoCodeEnvelope
  omega

theorem binaryBitValuation_base_le_stageTwo (termBound : Nat) :
    binaryBitValuationFormulaBaseCodeEnvelope termBound <=
      binaryBitValuationFormulaStageTwoCodeEnvelope termBound := by
  unfold binaryBitValuationFormulaStageTwoCodeEnvelope
    binaryBitValuationFormulaStageOneCodeEnvelope
  omega

theorem binaryBitValuation_negated_stageTwo_code_le_closure
    (formula : ValuationFormula) (termBound : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      binaryBitValuationFormulaStageTwoCodeEnvelope termBound) :
    (binaryFormulaCode (∼formula)).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound := by
  have hraw :=
    FoundationCompactSyntaxTransformationCodeBounds.binaryFormulaCode_neg_length_le
      formula
  unfold binaryBitValuationFormulaClosureCodeEnvelope
  omega

theorem binaryBitValuation_negated_base_code_le_closure
    (formula : ValuationFormula) (termBound : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      binaryBitValuationFormulaBaseCodeEnvelope termBound) :
    (binaryFormulaCode (∼formula)).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound := by
  exact binaryBitValuation_negated_stageTwo_code_le_closure formula termBound
    (hformula.trans (binaryBitValuation_base_le_stageTwo termBound))

theorem binaryBitValuation_negated_stageOne_code_le_closure
    (formula : ValuationFormula) (termBound : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      binaryBitValuationFormulaStageOneCodeEnvelope termBound) :
    (binaryFormulaCode (∼formula)).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound := by
  exact binaryBitValuation_negated_stageTwo_code_le_closure formula termBound
    (hformula.trans (binaryBitValuation_stageOne_le_stageTwo termBound))

/-! ## Small-context connector resources -/

/-- One formula-code coordinate covers every connector used by either the
positive or negative valuation-bit compiler.  Six is the exact largest number
of formula codes in the modus-tollens resource; the context sum is charged
separately. -/
def binaryBitValuationConnectorFormulaResourceEnvelope
    (contextBound termBound : Nat) : Nat :=
  contextBound +
    6 * binaryBitValuationFormulaClosureCodeEnvelope termBound + 1

def contextualModusPonensFormulaResource
    (Gamma : Finset ValuationFormula)
    (antecedent consequent : ValuationFormula) : Nat :=
  let implication := antecedent 🡒 consequent
  formulaCodeSum Gamma +
    (binaryFormulaCode antecedent).length +
    (binaryFormulaCode consequent).length +
    (binaryFormulaCode implication).length +
    (binaryFormulaCode (∼implication)).length +
    (binaryFormulaCode (∼consequent)).length + 1

theorem contextualModusPonensFullAssemblyCost_le_public
    (Gamma : Finset ValuationFormula)
    (antecedent consequent : ValuationFormula)
    (hcard : Gamma.card <= 4) :
    contextualModusPonensFullAssemblyCost Gamma antecedent consequent <=
      smallContextAssemblyEnvelope
        (contextualModusPonensFormulaResource Gamma antecedent consequent) := by
  let resource := contextualModusPonensFormulaResource
    Gamma antecedent consequent
  let implication := antecedent 🡒 consequent
  have hcontext : FormulaCodeBound Gamma resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    unfold resource contextualModusPonensFormulaResource
    dsimp only [implication]
    omega
  have hantecedent : (binaryFormulaCode antecedent).length <= resource := by
    unfold resource contextualModusPonensFormulaResource
    dsimp only [implication]
    omega
  have hconsequent : (binaryFormulaCode consequent).length <= resource := by
    unfold resource contextualModusPonensFormulaResource
    dsimp only [implication]
    omega
  have himplication : (binaryFormulaCode implication).length <= resource := by
    unfold resource contextualModusPonensFormulaResource
    dsimp only [implication]
    omega
  have hnegatedImplication :
      (binaryFormulaCode (∼implication)).length <= resource := by
    unfold resource contextualModusPonensFormulaResource
    dsimp only [implication]
    omega
  have hnegatedConsequent :
      (binaryFormulaCode (∼consequent)).length <= resource := by
    unfold resource contextualModusPonensFormulaResource
    dsimp only [implication]
    omega
  exact contextualModusPonensFullAssemblyCost_le_small
    Gamma antecedent consequent resource hcard hcontext
    hantecedent hconsequent himplication hnegatedImplication
    hnegatedConsequent

def modusTollensFormulaResource
    (Gamma : Finset ValuationFormula)
    (antecedent consequent : ValuationFormula) : Nat :=
  let implication := antecedent 🡒 consequent
  formulaCodeSum Gamma +
    (binaryFormulaCode antecedent).length +
    (binaryFormulaCode consequent).length +
    (binaryFormulaCode implication).length +
    (binaryFormulaCode (∼implication)).length +
    (binaryFormulaCode (∼antecedent)).length +
    (binaryFormulaCode (∼consequent)).length + 1

theorem modusTollensFullAssemblyCost_le_public
    (Gamma : Finset ValuationFormula)
    (antecedent consequent : ValuationFormula)
    (hcard : Gamma.card <= 4) :
    modusTollensFullAssemblyCost Gamma antecedent consequent <=
      smallContextAssemblyEnvelope
        (modusTollensFormulaResource Gamma antecedent consequent) := by
  let resource := modusTollensFormulaResource Gamma antecedent consequent
  let implication := antecedent 🡒 consequent
  have hcontext : FormulaCodeBound Gamma resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    unfold resource modusTollensFormulaResource
    dsimp only [implication]
    omega
  have hantecedent : (binaryFormulaCode antecedent).length <= resource := by
    unfold resource modusTollensFormulaResource
    dsimp only [implication]
    omega
  have hconsequent : (binaryFormulaCode consequent).length <= resource := by
    unfold resource modusTollensFormulaResource
    dsimp only [implication]
    omega
  have himplication : (binaryFormulaCode implication).length <= resource := by
    unfold resource modusTollensFormulaResource
    dsimp only [implication]
    omega
  have hnegatedImplication :
      (binaryFormulaCode (∼implication)).length <= resource := by
    unfold resource modusTollensFormulaResource
    dsimp only [implication]
    omega
  have hnegatedAntecedent :
      (binaryFormulaCode (∼antecedent)).length <= resource := by
    unfold resource modusTollensFormulaResource
    dsimp only [implication]
    omega
  have hnegatedConsequent :
      (binaryFormulaCode (∼consequent)).length <= resource := by
    unfold resource modusTollensFormulaResource
    dsimp only [implication]
    omega
  exact modusTollensFullAssemblyCost_le_small
    Gamma antecedent consequent resource hcard hcontext
    hantecedent hconsequent himplication hnegatedImplication
    hnegatedAntecedent hnegatedConsequent

theorem contextFormulaResource_le_binaryBitConnectorEnvelope
    (Gamma : Finset ValuationFormula) (formula : ValuationFormula)
    (contextBound termBound : Nat)
    (hcontext : formulaCodeSum Gamma <= contextBound)
    (hformula : (binaryFormulaCode formula).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound) :
    contextFormulaResource Gamma formula <=
      binaryBitValuationConnectorFormulaResourceEnvelope contextBound
        termBound := by
  unfold contextFormulaResource
    binaryBitValuationConnectorFormulaResourceEnvelope
  omega

theorem contextualModusPonensFormulaResource_le_binaryBitConnectorEnvelope
    (Gamma : Finset ValuationFormula)
    (antecedent consequent : ValuationFormula)
    (contextBound termBound : Nat)
    (hcontext : formulaCodeSum Gamma <= contextBound)
    (hantecedent : (binaryFormulaCode antecedent).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound)
    (hconsequent : (binaryFormulaCode consequent).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound)
    (himplication : (binaryFormulaCode (antecedent 🡒 consequent)).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound)
    (hnegatedImplication :
      (binaryFormulaCode (∼(antecedent 🡒 consequent))).length <=
        binaryBitValuationFormulaClosureCodeEnvelope termBound)
    (hnegatedConsequent : (binaryFormulaCode (∼consequent)).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound) :
    contextualModusPonensFormulaResource Gamma antecedent consequent <=
      binaryBitValuationConnectorFormulaResourceEnvelope contextBound
        termBound := by
  unfold contextualModusPonensFormulaResource
    binaryBitValuationConnectorFormulaResourceEnvelope
  dsimp only
  omega

theorem modusTollensFormulaResource_le_binaryBitConnectorEnvelope
    (Gamma : Finset ValuationFormula)
    (antecedent consequent : ValuationFormula)
    (contextBound termBound : Nat)
    (hcontext : formulaCodeSum Gamma <= contextBound)
    (hantecedent : (binaryFormulaCode antecedent).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound)
    (hconsequent : (binaryFormulaCode consequent).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound)
    (himplication : (binaryFormulaCode (antecedent 🡒 consequent)).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound)
    (hnegatedImplication :
      (binaryFormulaCode (∼(antecedent 🡒 consequent))).length <=
        binaryBitValuationFormulaClosureCodeEnvelope termBound)
    (hnegatedAntecedent : (binaryFormulaCode (∼antecedent)).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound)
    (hnegatedConsequent : (binaryFormulaCode (∼consequent)).length <=
      binaryBitValuationFormulaClosureCodeEnvelope termBound) :
    modusTollensFormulaResource Gamma antecedent consequent <=
      binaryBitValuationConnectorFormulaResourceEnvelope contextBound
        termBound := by
  unfold modusTollensFormulaResource
    binaryBitValuationConnectorFormulaResourceEnvelope
  dsimp only
  omega

theorem weakeningFullAssemblyCost_insert_le_public
    (Gamma : Finset ValuationFormula) (formula : ValuationFormula)
    (hcard : Gamma.card <= 4) :
    weakeningFullAssemblyCost (insert formula Gamma) <=
      smallContextAssemblyEnvelope (contextFormulaResource Gamma formula) := by
  have hinsertCard : (insert formula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le formula Gamma
    omega
  exact weakeningFullAssemblyCost_le_small
    (insert formula Gamma) (contextFormulaResource Gamma formula)
    hinsertCard
    ((contextFormulaResource_context Gamma formula).insert
      (contextFormulaResource_formula Gamma formula))

theorem binaryBitValuationContext_card_le_four
    (valuation : Nat -> Nat) (indexTerm valueTerm : ValuationTerm)
    (hindexVars : indexTerm.freeVariables ⊆ {0})
    (hvalueVars : valueTerm.freeVariables ⊆ {0}) :
    (binaryBitValuationContext valuation indexTerm valueTerm).card <= 4 := by
  have hunion : indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆ {0} := by
    intro candidate hcandidate
    rcases Finset.mem_union.mp hcandidate with hindex | hvalue
    · exact hindexVars hindex
    · exact hvalueVars hvalue
  exact valuationContext_card_le_four_of_subset_singleton
    (indexTerm.freeVariables ∪ valueTerm.freeVariables) valuation hunion

theorem binaryBitValuationContext_card_le_four_of_union_card
    (valuation : Nat -> Nat) (indexTerm valueTerm : ValuationTerm)
    (hvars :
      (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4) :
    (binaryBitValuationContext valuation indexTerm valueTerm).card <= 4 := by
  exact valuationContext_card_le_four_of_card_le_four
    (indexTerm.freeVariables ∪ valueTerm.freeVariables) valuation hvars

theorem binaryBitFreeVariables_card_le_four_of_subset_singleton
    (indexTerm valueTerm : ValuationTerm)
    (hindexVars : indexTerm.freeVariables ⊆ {0})
    (hvalueVars : valueTerm.freeVariables ⊆ {0}) :
    (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4 := by
  have hunion : indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆ {0} := by
    intro candidate hcandidate
    rcases Finset.mem_union.mp hcandidate with hindex | hvalue
    · exact hindexVars hindex
    · exact hvalueVars hvalue
  have hcard := Finset.card_le_card hunion
  simp only [Finset.card_singleton] at hcard
  omega

/-! ## Common term-code coordinate -/

def binaryBitValuationTermCodeResource
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : Nat :=
  (binaryTermCode
      (shortBinaryNumeralTerm (termValue valuation indexTerm))).length +
    (binaryTermCode indexTerm).length +
    (binaryTermCode
      (shortBinaryNumeralTerm (termValue valuation valueTerm))).length +
    (binaryTermCode valueTerm).length + 1

theorem binaryBitValuationTermCodes_le_resource
    (valuation : Nat -> Nat) (indexTerm valueTerm : ValuationTerm) :
    (binaryTermCode
        (shortBinaryNumeralTerm (termValue valuation indexTerm))).length <=
          binaryBitValuationTermCodeResource valuation indexTerm valueTerm ∧
      (binaryTermCode indexTerm).length <=
          binaryBitValuationTermCodeResource valuation indexTerm valueTerm ∧
      (binaryTermCode
        (shortBinaryNumeralTerm (termValue valuation valueTerm))).length <=
          binaryBitValuationTermCodeResource valuation indexTerm valueTerm ∧
      (binaryTermCode valueTerm).length <=
          binaryBitValuationTermCodeResource valuation indexTerm valueTerm := by
  unfold binaryBitValuationTermCodeResource
  omega

/-- Common connector bound once context syntax, term syntax, and the two term
equality compilers have each been placed below fixed coordinates.  The
negative literal is the larger branch, so the same expression covers both
Boolean endpoints. -/
def binaryBitValuationConnectorUniformPolynomial
    (contextBound termBound equalityBound : Nat) : Nat :=
  2 * equalityBound +
    binaryBitIndexTransportPayloadTermPolynomial termBound +
    binaryBitValueTransportPayloadTermPolynomial termBound +
    2 * binaryBitEqualitySymmetryPayloadTermPolynomial termBound +
    13 * smallContextAssemblyEnvelope
      (binaryBitValuationConnectorFormulaResourceEnvelope contextBound
        termBound)

/-! ## Positive literal -/

def compilePositiveBinaryBitAtValuationConnectorPolynomial
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : Nat :=
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm
  let sourceFormula := binaryBitValuationSourceFormula true
    valuation indexTerm valueTerm
  let indexEqualityFormula := binaryBitValuationIndexEqualityFormula
    valuation indexTerm
  let indexFactFormula := binaryBitValuationIndexAtomFormula
    valuation indexTerm valueTerm
  let valueEqualityFormula := binaryBitValuationValueEqualityFormula
    valuation valueTerm
  let resultFormula := binaryBitValuationResultAtomFormula
    indexTerm valueTerm
  let indexTransportConsequent := sourceFormula 🡒 indexFactFormula
  let valueTransportConsequent := indexFactFormula 🡒 resultFormula
  let termResource := binaryBitValuationTermCodeResource
    valuation indexTerm valueTerm
  smallContextAssemblyEnvelope
      (contextFormulaResource Gamma sourceFormula) +
    compileTermValueEqualityPayloadPolynomial valuation indexTerm +
    smallContextAssemblyEnvelope
      (contextFormulaResource Gamma indexEqualityFormula) +
    binaryBitIndexTransportPayloadTermPolynomial termResource +
    smallContextAssemblyEnvelope
      (contextFormulaResource Gamma
        (indexEqualityFormula 🡒 indexTransportConsequent)) +
    smallContextAssemblyEnvelope
      (contextualModusPonensFormulaResource Gamma
        indexEqualityFormula indexTransportConsequent) +
    smallContextAssemblyEnvelope
      (contextualModusPonensFormulaResource Gamma
        sourceFormula indexFactFormula) +
    compileTermValueEqualityPayloadPolynomial valuation valueTerm +
    smallContextAssemblyEnvelope
      (contextFormulaResource Gamma valueEqualityFormula) +
    binaryBitValueTransportPayloadTermPolynomial termResource +
    smallContextAssemblyEnvelope
      (contextFormulaResource Gamma
        (valueEqualityFormula 🡒 valueTransportConsequent)) +
    smallContextAssemblyEnvelope
      (contextualModusPonensFormulaResource Gamma
        valueEqualityFormula valueTransportConsequent) +
    smallContextAssemblyEnvelope
      (contextualModusPonensFormulaResource Gamma
        indexFactFormula resultFormula)

theorem compilePositiveBinaryBitAtValuationConnectorPolynomial_le_uniform
    (valuation : Nat -> Nat) (indexTerm valueTerm : ValuationTerm)
    (contextBound termBound equalityBound : Nat)
    (hcontext : formulaCodeSum
      (binaryBitValuationContext valuation indexTerm valueTerm) <=
        contextBound)
    (htermResource :
      binaryBitValuationTermCodeResource valuation indexTerm valueTerm <=
        termBound)
    (hindexEquality :
      compileTermValueEqualityPayloadPolynomial valuation indexTerm <=
        equalityBound)
    (hvalueEquality :
      compileTermValueEqualityPayloadPolynomial valuation valueTerm <=
        equalityBound) :
    compilePositiveBinaryBitAtValuationConnectorPolynomial
        valuation indexTerm valueTerm <=
      binaryBitValuationConnectorUniformPolynomial contextBound termBound
        equalityBound := by
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm
  let sourceFormula := binaryBitValuationSourceFormula true
    valuation indexTerm valueTerm
  let indexEqualityFormula := binaryBitValuationIndexEqualityFormula
    valuation indexTerm
  let indexFactFormula := binaryBitValuationIndexAtomFormula
    valuation indexTerm valueTerm
  let valueEqualityFormula := binaryBitValuationValueEqualityFormula
    valuation valueTerm
  let resultFormula := binaryBitValuationResultAtomFormula
    indexTerm valueTerm
  let indexTransportConsequent := sourceFormula 🡒 indexFactFormula
  let valueTransportConsequent := indexFactFormula 🡒 resultFormula
  let termResource := binaryBitValuationTermCodeResource
    valuation indexTerm valueTerm
  let formulaResource := binaryBitValuationConnectorFormulaResourceEnvelope
    contextBound termBound
  rcases binaryBitValuationTermCodes_le_resource
      valuation indexTerm valueTerm with
    ⟨hshortIndexRaw, hindexRaw, hshortValueRaw, hvalueRaw⟩
  have hshortIndex := hshortIndexRaw.trans htermResource
  have hindex := hindexRaw.trans htermResource
  have hshortValue := hshortValueRaw.trans htermResource
  have hvalue := hvalueRaw.trans htermResource
  rcases binaryBitValuationBaseFormulaCodes_le_uniform true valuation
      indexTerm valueTerm termBound hshortIndex hindex hshortValue hvalue with
    ⟨hsource, _hsourceAtom, hindexEqualityFormula,
      _hindexReverseEqualityFormula, hindexFact, hvalueEqualityFormula,
      _hvalueReverseEqualityFormula, hresult⟩
  have hindexTransportConsequent :=
    binaryBitValuation_implication_base_code_le_stageOne
      sourceFormula indexFactFormula termBound hsource hindexFact
  have hvalueTransportConsequent :=
    binaryBitValuation_implication_base_code_le_stageOne
      indexFactFormula resultFormula termBound hindexFact hresult
  have hindexTransportFormula :=
    binaryBitValuation_implication_second_code_le_stageTwo
      indexEqualityFormula indexTransportConsequent termBound
      hindexEqualityFormula hindexTransportConsequent
  have hvalueTransportFormula :=
    binaryBitValuation_implication_second_code_le_stageTwo
      valueEqualityFormula valueTransportConsequent termBound
      hvalueEqualityFormula hvalueTransportConsequent
  have hbaseClosure := binaryBitValuation_base_le_closure termBound
  have hstageOneClosure :=
    (binaryBitValuation_stageOne_le_stageTwo termBound).trans
      (binaryBitValuation_stageTwo_le_closure termBound)
  have hsourceClosure := hsource.trans hbaseClosure
  have hindexEqualityClosure := hindexEqualityFormula.trans hbaseClosure
  have hindexFactClosure := hindexFact.trans hbaseClosure
  have hvalueEqualityClosure := hvalueEqualityFormula.trans hbaseClosure
  have hresultClosure := hresult.trans hbaseClosure
  have hindexTransportConsequentClosure :=
    hindexTransportConsequent.trans hstageOneClosure
  have hvalueTransportConsequentClosure :=
    hvalueTransportConsequent.trans hstageOneClosure
  have hindexTransportFormulaClosure :=
    hindexTransportFormula.trans
      (binaryBitValuation_stageTwo_le_closure termBound)
  have hvalueTransportFormulaClosure :=
    hvalueTransportFormula.trans
      (binaryBitValuation_stageTwo_le_closure termBound)
  have hnegIndexTransportFormula :=
    binaryBitValuation_negated_stageTwo_code_le_closure
      (indexEqualityFormula 🡒 indexTransportConsequent) termBound
      hindexTransportFormula
  have hnegValueTransportFormula :=
    binaryBitValuation_negated_stageTwo_code_le_closure
      (valueEqualityFormula 🡒 valueTransportConsequent) termBound
      hvalueTransportFormula
  have hnegIndexTransportConsequent :=
    binaryBitValuation_negated_stageOne_code_le_closure
      indexTransportConsequent termBound hindexTransportConsequent
  have hnegValueTransportConsequent :=
    binaryBitValuation_negated_stageOne_code_le_closure
      valueTransportConsequent termBound hvalueTransportConsequent
  have hnegIndexFact := binaryBitValuation_negated_base_code_le_closure
    indexFactFormula termBound hindexFact
  have hnegResult := binaryBitValuation_negated_base_code_le_closure
    resultFormula termBound hresult
  have hweakSource :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma sourceFormula
      contextBound termBound hcontext hsourceClosure
  have hweakIndexEquality :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma
      indexEqualityFormula contextBound termBound hcontext
      hindexEqualityClosure
  have hweakIndexTransport :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma
      (indexEqualityFormula 🡒 indexTransportConsequent)
      contextBound termBound hcontext hindexTransportFormulaClosure
  have hmpIndexEquality :=
    contextualModusPonensFormulaResource_le_binaryBitConnectorEnvelope
      Gamma indexEqualityFormula indexTransportConsequent contextBound
      termBound hcontext hindexEqualityClosure
      hindexTransportConsequentClosure hindexTransportFormulaClosure
      hnegIndexTransportFormula hnegIndexTransportConsequent
  have hmpSource :=
    contextualModusPonensFormulaResource_le_binaryBitConnectorEnvelope
      Gamma sourceFormula indexFactFormula contextBound termBound hcontext
      hsourceClosure hindexFactClosure hindexTransportConsequentClosure
      hnegIndexTransportConsequent hnegIndexFact
  have hweakValueEquality :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma
      valueEqualityFormula contextBound termBound hcontext
      hvalueEqualityClosure
  have hweakValueTransport :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma
      (valueEqualityFormula 🡒 valueTransportConsequent)
      contextBound termBound hcontext hvalueTransportFormulaClosure
  have hmpValueEquality :=
    contextualModusPonensFormulaResource_le_binaryBitConnectorEnvelope
      Gamma valueEqualityFormula valueTransportConsequent contextBound
      termBound hcontext hvalueEqualityClosure
      hvalueTransportConsequentClosure hvalueTransportFormulaClosure
      hnegValueTransportFormula hnegValueTransportConsequent
  have hmpResult :=
    contextualModusPonensFormulaResource_le_binaryBitConnectorEnvelope
      Gamma indexFactFormula resultFormula contextBound termBound hcontext
      hindexFactClosure hresultClosure hvalueTransportConsequentClosure
      hnegValueTransportConsequent hnegResult
  have hindexTransport :=
    binaryBitIndexTransportPayloadTermPolynomial_mono htermResource
  have hvalueTransport :=
    binaryBitValueTransportPayloadTermPolynomial_mono htermResource
  have hsmall : forall resource, resource <= formulaResource ->
      smallContextAssemblyEnvelope resource <=
        smallContextAssemblyEnvelope formulaResource := by
    intro resource hresource
    exact smallContextAssemblyEnvelope_mono_local hresource
  have hsWeakSource := hsmall _ hweakSource
  have hsWeakIndexEquality := hsmall _ hweakIndexEquality
  have hsWeakIndexTransport := hsmall _ hweakIndexTransport
  have hsMpIndexEquality := hsmall _ hmpIndexEquality
  have hsMpSource := hsmall _ hmpSource
  have hsWeakValueEquality := hsmall _ hweakValueEquality
  have hsWeakValueTransport := hsmall _ hweakValueTransport
  have hsMpValueEquality := hsmall _ hmpValueEquality
  have hsMpResult := hsmall _ hmpResult
  unfold compilePositiveBinaryBitAtValuationConnectorPolynomial
    binaryBitValuationConnectorUniformPolynomial
  dsimp only [Gamma, sourceFormula, indexEqualityFormula, indexFactFormula,
    valueEqualityFormula, resultFormula, indexTransportConsequent,
    valueTransportConsequent, termResource, formulaResource] at *
  omega

def compilePositiveBinaryBitAtValuationPayloadPolynomial
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : Nat :=
  binaryBitLiteralPayloadPolynomial
      (termValue valuation indexTerm) (termValue valuation valueTerm) +
    compilePositiveBinaryBitAtValuationConnectorPolynomial
      valuation indexTerm valueTerm

theorem compilePositiveBinaryBitAtValuationPayloadResource_le_publicPolynomial_of_card
    (valuation : Nat -> Nat) (indexTerm valueTerm : ValuationTerm)
    (hvars :
      (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4) :
    compilePositiveBinaryBitAtValuationPayloadResource
        valuation indexTerm valueTerm <=
      compilePositiveBinaryBitAtValuationPayloadPolynomial
        valuation indexTerm valueTerm := by
  let index := termValue valuation indexTerm
  let value := termValue valuation valueTerm
  let shortIndex := shortBinaryNumeralTerm index
  let shortValue := shortBinaryNumeralTerm value
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm
  let sourceFormula := binaryBitValuationSourceFormula true
    valuation indexTerm valueTerm
  let indexEqualityFormula := binaryBitValuationIndexEqualityFormula
    valuation indexTerm
  let indexFactFormula := binaryBitValuationIndexAtomFormula
    valuation indexTerm valueTerm
  let valueEqualityFormula := binaryBitValuationValueEqualityFormula
    valuation valueTerm
  let resultFormula := binaryBitValuationResultAtomFormula
    indexTerm valueTerm
  let indexTransportConsequent := sourceFormula 🡒 indexFactFormula
  let valueTransportConsequent := indexFactFormula 🡒 resultFormula
  let termResource := binaryBitValuationTermCodeResource
    valuation indexTerm valueTerm
  have hcard : Gamma.card <= 4 :=
    binaryBitValuationContext_card_le_four_of_union_card
      valuation indexTerm valueTerm hvars
  have hindexCard : indexTerm.freeVariables.card <= 4 := by
    exact (Finset.card_le_card Finset.subset_union_left).trans hvars
  have hvalueCard : valueTerm.freeVariables.card <= 4 := by
    exact (Finset.card_le_card Finset.subset_union_right).trans hvars
  rcases binaryBitValuationTermCodes_le_resource
      valuation indexTerm valueTerm with
    ⟨hshortIndex, hindexTerm, hshortValue, hvalueTerm⟩
  have hindexEquality :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial_of_card
      valuation indexTerm hindexCard
  have hvalueEquality :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial_of_card
      valuation valueTerm hvalueCard
  have hindexTransport :=
    binaryBitIndexTransportPayloadResource_le_termPolynomial
      shortIndex indexTerm shortValue termResource
      hshortIndex hindexTerm hshortValue
  have hvalueTransport :=
    binaryBitValueTransportPayloadResource_le_termPolynomial
      indexTerm shortValue valueTerm termResource
      hindexTerm hshortValue hvalueTerm
  have hweakSource := weakeningFullAssemblyCost_insert_le_public
    Gamma sourceFormula hcard
  have hweakIndexEquality := weakeningFullAssemblyCost_insert_le_public
    Gamma indexEqualityFormula hcard
  have hweakIndexTransport := weakeningFullAssemblyCost_insert_le_public
    Gamma (indexEqualityFormula 🡒 indexTransportConsequent) hcard
  have hmpIndexEquality := contextualModusPonensFullAssemblyCost_le_public
    Gamma indexEqualityFormula indexTransportConsequent hcard
  have hmpSource := contextualModusPonensFullAssemblyCost_le_public
    Gamma sourceFormula indexFactFormula hcard
  have hweakValueEquality := weakeningFullAssemblyCost_insert_le_public
    Gamma valueEqualityFormula hcard
  have hweakValueTransport := weakeningFullAssemblyCost_insert_le_public
    Gamma (valueEqualityFormula 🡒 valueTransportConsequent) hcard
  have hmpValueEquality := contextualModusPonensFullAssemblyCost_le_public
    Gamma valueEqualityFormula valueTransportConsequent hcard
  have hmpResult := contextualModusPonensFullAssemblyCost_le_public
    Gamma indexFactFormula resultFormula hcard
  unfold compilePositiveBinaryBitAtValuationPayloadResource
    compilePositiveBinaryBitAtValuationPayloadPolynomial
    compilePositiveBinaryBitAtValuationConnectorPolynomial
  dsimp only [index, value, shortIndex, shortValue, Gamma,
    sourceFormula, indexEqualityFormula, indexFactFormula,
    valueEqualityFormula, resultFormula, indexTransportConsequent,
    valueTransportConsequent, termResource] at *
  omega

theorem compilePositiveBinaryBitAtValuationPayloadResource_le_publicPolynomial
    (valuation : Nat -> Nat) (indexTerm valueTerm : ValuationTerm)
    (hindexVars : indexTerm.freeVariables ⊆ {0})
    (hvalueVars : valueTerm.freeVariables ⊆ {0}) :
    compilePositiveBinaryBitAtValuationPayloadResource
        valuation indexTerm valueTerm <=
      compilePositiveBinaryBitAtValuationPayloadPolynomial
        valuation indexTerm valueTerm := by
  exact
    compilePositiveBinaryBitAtValuationPayloadResource_le_publicPolynomial_of_card
      valuation indexTerm valueTerm
      (binaryBitFreeVariables_card_le_four_of_subset_singleton
        indexTerm valueTerm hindexVars hvalueVars)

/-! ## Negative literal -/

def compileNegativeBinaryBitAtValuationConnectorPolynomial
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : Nat :=
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm
  let sourceFormula := binaryBitValuationSourceFormula false
    valuation indexTerm valueTerm
  let sourceAtom := binaryBitValuationSourceAtomFormula
    valuation indexTerm valueTerm
  let indexEqualityFormula := binaryBitValuationIndexEqualityFormula
    valuation indexTerm
  let indexReverseEqualityFormula :=
    binaryBitValuationIndexReverseEqualityFormula valuation indexTerm
  let indexAtom := binaryBitValuationIndexAtomFormula
    valuation indexTerm valueTerm
  let valueEqualityFormula := binaryBitValuationValueEqualityFormula
    valuation valueTerm
  let valueReverseEqualityFormula :=
    binaryBitValuationValueReverseEqualityFormula valuation valueTerm
  let resultAtom := binaryBitValuationResultAtomFormula indexTerm valueTerm
  let reverseIndexTransportConsequent := indexAtom 🡒 sourceAtom
  let reverseValueTransportConsequent := resultAtom 🡒 indexAtom
  let termResource := binaryBitValuationTermCodeResource
    valuation indexTerm valueTerm
  smallContextAssemblyEnvelope
      (contextFormulaResource Gamma sourceFormula) +
    compileTermValueEqualityPayloadPolynomial valuation indexTerm +
    smallContextAssemblyEnvelope
      (contextFormulaResource Gamma indexEqualityFormula) +
    binaryBitEqualitySymmetryPayloadTermPolynomial termResource +
    smallContextAssemblyEnvelope
      (contextFormulaResource Gamma
        (indexEqualityFormula 🡒 indexReverseEqualityFormula)) +
    smallContextAssemblyEnvelope
      (contextualModusPonensFormulaResource Gamma
        indexEqualityFormula indexReverseEqualityFormula) +
    binaryBitIndexTransportPayloadTermPolynomial termResource +
    smallContextAssemblyEnvelope
      (contextFormulaResource Gamma
        (indexReverseEqualityFormula 🡒 reverseIndexTransportConsequent)) +
    smallContextAssemblyEnvelope
      (contextualModusPonensFormulaResource Gamma
        indexReverseEqualityFormula reverseIndexTransportConsequent) +
    smallContextAssemblyEnvelope
      (modusTollensFormulaResource Gamma indexAtom sourceAtom) +
    compileTermValueEqualityPayloadPolynomial valuation valueTerm +
    smallContextAssemblyEnvelope
      (contextFormulaResource Gamma valueEqualityFormula) +
    binaryBitEqualitySymmetryPayloadTermPolynomial termResource +
    smallContextAssemblyEnvelope
      (contextFormulaResource Gamma
        (valueEqualityFormula 🡒 valueReverseEqualityFormula)) +
    smallContextAssemblyEnvelope
      (contextualModusPonensFormulaResource Gamma
        valueEqualityFormula valueReverseEqualityFormula) +
    binaryBitValueTransportPayloadTermPolynomial termResource +
    smallContextAssemblyEnvelope
      (contextFormulaResource Gamma
        (valueReverseEqualityFormula 🡒 reverseValueTransportConsequent)) +
    smallContextAssemblyEnvelope
      (contextualModusPonensFormulaResource Gamma
        valueReverseEqualityFormula reverseValueTransportConsequent) +
    smallContextAssemblyEnvelope
      (modusTollensFormulaResource Gamma resultAtom indexAtom)

theorem compileNegativeBinaryBitAtValuationConnectorPolynomial_le_uniform
    (valuation : Nat -> Nat) (indexTerm valueTerm : ValuationTerm)
    (contextBound termBound equalityBound : Nat)
    (hcontext : formulaCodeSum
      (binaryBitValuationContext valuation indexTerm valueTerm) <=
        contextBound)
    (htermResource :
      binaryBitValuationTermCodeResource valuation indexTerm valueTerm <=
        termBound)
    (hindexEquality :
      compileTermValueEqualityPayloadPolynomial valuation indexTerm <=
        equalityBound)
    (hvalueEquality :
      compileTermValueEqualityPayloadPolynomial valuation valueTerm <=
        equalityBound) :
    compileNegativeBinaryBitAtValuationConnectorPolynomial
        valuation indexTerm valueTerm <=
      binaryBitValuationConnectorUniformPolynomial contextBound termBound
        equalityBound := by
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm
  let sourceFormula := binaryBitValuationSourceFormula false
    valuation indexTerm valueTerm
  let sourceAtom := binaryBitValuationSourceAtomFormula
    valuation indexTerm valueTerm
  let indexEqualityFormula := binaryBitValuationIndexEqualityFormula
    valuation indexTerm
  let indexReverseEqualityFormula :=
    binaryBitValuationIndexReverseEqualityFormula valuation indexTerm
  let indexAtom := binaryBitValuationIndexAtomFormula
    valuation indexTerm valueTerm
  let valueEqualityFormula := binaryBitValuationValueEqualityFormula
    valuation valueTerm
  let valueReverseEqualityFormula :=
    binaryBitValuationValueReverseEqualityFormula valuation valueTerm
  let resultAtom := binaryBitValuationResultAtomFormula indexTerm valueTerm
  let reverseIndexTransportConsequent := indexAtom 🡒 sourceAtom
  let reverseValueTransportConsequent := resultAtom 🡒 indexAtom
  let indexSymmetryFormula :=
    indexEqualityFormula 🡒 indexReverseEqualityFormula
  let indexTransportFormula :=
    indexReverseEqualityFormula 🡒 reverseIndexTransportConsequent
  let valueSymmetryFormula :=
    valueEqualityFormula 🡒 valueReverseEqualityFormula
  let valueTransportFormula :=
    valueReverseEqualityFormula 🡒 reverseValueTransportConsequent
  let termResource := binaryBitValuationTermCodeResource
    valuation indexTerm valueTerm
  let formulaResource := binaryBitValuationConnectorFormulaResourceEnvelope
    contextBound termBound
  rcases binaryBitValuationTermCodes_le_resource
      valuation indexTerm valueTerm with
    ⟨hshortIndexRaw, hindexRaw, hshortValueRaw, hvalueRaw⟩
  have hshortIndex := hshortIndexRaw.trans htermResource
  have hindex := hindexRaw.trans htermResource
  have hshortValue := hshortValueRaw.trans htermResource
  have hvalue := hvalueRaw.trans htermResource
  rcases binaryBitValuationBaseFormulaCodes_le_uniform false valuation
      indexTerm valueTerm termBound hshortIndex hindex hshortValue hvalue with
    ⟨hsource, hsourceAtom, hindexEqualityFormula,
      hindexReverseEqualityFormula, hindexAtom, hvalueEqualityFormula,
      hvalueReverseEqualityFormula, hresultAtom⟩
  have hreverseIndexTransportConsequent :=
    binaryBitValuation_implication_base_code_le_stageOne
      indexAtom sourceAtom termBound hindexAtom hsourceAtom
  have hreverseValueTransportConsequent :=
    binaryBitValuation_implication_base_code_le_stageOne
      resultAtom indexAtom termBound hresultAtom hindexAtom
  have hindexSymmetryFormula :=
    binaryBitValuation_implication_base_code_le_stageOne
      indexEqualityFormula indexReverseEqualityFormula termBound
      hindexEqualityFormula hindexReverseEqualityFormula
  have hvalueSymmetryFormula :=
    binaryBitValuation_implication_base_code_le_stageOne
      valueEqualityFormula valueReverseEqualityFormula termBound
      hvalueEqualityFormula hvalueReverseEqualityFormula
  have hindexTransportFormula :=
    binaryBitValuation_implication_second_code_le_stageTwo
      indexReverseEqualityFormula reverseIndexTransportConsequent termBound
      hindexReverseEqualityFormula hreverseIndexTransportConsequent
  have hvalueTransportFormula :=
    binaryBitValuation_implication_second_code_le_stageTwo
      valueReverseEqualityFormula reverseValueTransportConsequent termBound
      hvalueReverseEqualityFormula hreverseValueTransportConsequent
  have hbaseClosure := binaryBitValuation_base_le_closure termBound
  have hstageOneClosure :=
    (binaryBitValuation_stageOne_le_stageTwo termBound).trans
      (binaryBitValuation_stageTwo_le_closure termBound)
  have hsourceClosure := hsource.trans hbaseClosure
  have hsourceAtomClosure := hsourceAtom.trans hbaseClosure
  have hindexEqualityClosure := hindexEqualityFormula.trans hbaseClosure
  have hindexReverseEqualityClosure :=
    hindexReverseEqualityFormula.trans hbaseClosure
  have hindexAtomClosure := hindexAtom.trans hbaseClosure
  have hvalueEqualityClosure := hvalueEqualityFormula.trans hbaseClosure
  have hvalueReverseEqualityClosure :=
    hvalueReverseEqualityFormula.trans hbaseClosure
  have hresultAtomClosure := hresultAtom.trans hbaseClosure
  have hreverseIndexTransportConsequentClosure :=
    hreverseIndexTransportConsequent.trans hstageOneClosure
  have hreverseValueTransportConsequentClosure :=
    hreverseValueTransportConsequent.trans hstageOneClosure
  have hindexSymmetryFormulaClosure :=
    hindexSymmetryFormula.trans hstageOneClosure
  have hvalueSymmetryFormulaClosure :=
    hvalueSymmetryFormula.trans hstageOneClosure
  have hindexTransportFormulaClosure :=
    hindexTransportFormula.trans
      (binaryBitValuation_stageTwo_le_closure termBound)
  have hvalueTransportFormulaClosure :=
    hvalueTransportFormula.trans
      (binaryBitValuation_stageTwo_le_closure termBound)
  have hnegIndexSymmetryFormula :=
    binaryBitValuation_negated_stageOne_code_le_closure
      indexSymmetryFormula termBound hindexSymmetryFormula
  have hnegValueSymmetryFormula :=
    binaryBitValuation_negated_stageOne_code_le_closure
      valueSymmetryFormula termBound hvalueSymmetryFormula
  have hnegIndexReverseEquality :=
    binaryBitValuation_negated_base_code_le_closure
      indexReverseEqualityFormula termBound hindexReverseEqualityFormula
  have hnegValueReverseEquality :=
    binaryBitValuation_negated_base_code_le_closure
      valueReverseEqualityFormula termBound hvalueReverseEqualityFormula
  have hnegIndexTransportFormula :=
    binaryBitValuation_negated_stageTwo_code_le_closure
      indexTransportFormula termBound hindexTransportFormula
  have hnegValueTransportFormula :=
    binaryBitValuation_negated_stageTwo_code_le_closure
      valueTransportFormula termBound hvalueTransportFormula
  have hnegReverseIndexConsequent :=
    binaryBitValuation_negated_stageOne_code_le_closure
      reverseIndexTransportConsequent termBound
      hreverseIndexTransportConsequent
  have hnegReverseValueConsequent :=
    binaryBitValuation_negated_stageOne_code_le_closure
      reverseValueTransportConsequent termBound
      hreverseValueTransportConsequent
  have hnegIndexAtom := binaryBitValuation_negated_base_code_le_closure
    indexAtom termBound hindexAtom
  have hnegSourceAtom := binaryBitValuation_negated_base_code_le_closure
    sourceAtom termBound hsourceAtom
  have hnegResultAtom := binaryBitValuation_negated_base_code_le_closure
    resultAtom termBound hresultAtom
  have hweakSource :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma sourceFormula
      contextBound termBound hcontext hsourceClosure
  have hweakIndexEquality :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma
      indexEqualityFormula contextBound termBound hcontext
      hindexEqualityClosure
  have hweakIndexSymmetry :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma
      indexSymmetryFormula contextBound termBound hcontext
      hindexSymmetryFormulaClosure
  have hmpIndexSymmetry :=
    contextualModusPonensFormulaResource_le_binaryBitConnectorEnvelope
      Gamma indexEqualityFormula indexReverseEqualityFormula contextBound
      termBound hcontext hindexEqualityClosure hindexReverseEqualityClosure
      hindexSymmetryFormulaClosure hnegIndexSymmetryFormula
      hnegIndexReverseEquality
  have hweakIndexTransport :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma
      indexTransportFormula contextBound termBound hcontext
      hindexTransportFormulaClosure
  have hmpIndexTransport :=
    contextualModusPonensFormulaResource_le_binaryBitConnectorEnvelope
      Gamma indexReverseEqualityFormula reverseIndexTransportConsequent
      contextBound termBound hcontext hindexReverseEqualityClosure
      hreverseIndexTransportConsequentClosure hindexTransportFormulaClosure
      hnegIndexTransportFormula hnegReverseIndexConsequent
  have hmtIndex :=
    modusTollensFormulaResource_le_binaryBitConnectorEnvelope
      Gamma indexAtom sourceAtom contextBound termBound hcontext
      hindexAtomClosure hsourceAtomClosure
      hreverseIndexTransportConsequentClosure hnegReverseIndexConsequent
      hnegIndexAtom hnegSourceAtom
  have hweakValueEquality :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma
      valueEqualityFormula contextBound termBound hcontext
      hvalueEqualityClosure
  have hweakValueSymmetry :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma
      valueSymmetryFormula contextBound termBound hcontext
      hvalueSymmetryFormulaClosure
  have hmpValueSymmetry :=
    contextualModusPonensFormulaResource_le_binaryBitConnectorEnvelope
      Gamma valueEqualityFormula valueReverseEqualityFormula contextBound
      termBound hcontext hvalueEqualityClosure hvalueReverseEqualityClosure
      hvalueSymmetryFormulaClosure hnegValueSymmetryFormula
      hnegValueReverseEquality
  have hweakValueTransport :=
    contextFormulaResource_le_binaryBitConnectorEnvelope Gamma
      valueTransportFormula contextBound termBound hcontext
      hvalueTransportFormulaClosure
  have hmpValueTransport :=
    contextualModusPonensFormulaResource_le_binaryBitConnectorEnvelope
      Gamma valueReverseEqualityFormula reverseValueTransportConsequent
      contextBound termBound hcontext hvalueReverseEqualityClosure
      hreverseValueTransportConsequentClosure hvalueTransportFormulaClosure
      hnegValueTransportFormula hnegReverseValueConsequent
  have hmtValue :=
    modusTollensFormulaResource_le_binaryBitConnectorEnvelope
      Gamma resultAtom indexAtom contextBound termBound hcontext
      hresultAtomClosure hindexAtomClosure
      hreverseValueTransportConsequentClosure hnegReverseValueConsequent
      hnegResultAtom hnegIndexAtom
  have hindexTransport :=
    binaryBitIndexTransportPayloadTermPolynomial_mono htermResource
  have hvalueTransport :=
    binaryBitValueTransportPayloadTermPolynomial_mono htermResource
  have hsymmetry :=
    binaryBitEqualitySymmetryPayloadTermPolynomial_mono htermResource
  have hsmall : forall resource, resource <= formulaResource ->
      smallContextAssemblyEnvelope resource <=
        smallContextAssemblyEnvelope formulaResource := by
    intro resource hresource
    exact smallContextAssemblyEnvelope_mono_local hresource
  have hsWeakSource := hsmall _ hweakSource
  have hsWeakIndexEquality := hsmall _ hweakIndexEquality
  have hsWeakIndexSymmetry := hsmall _ hweakIndexSymmetry
  have hsMpIndexSymmetry := hsmall _ hmpIndexSymmetry
  have hsWeakIndexTransport := hsmall _ hweakIndexTransport
  have hsMpIndexTransport := hsmall _ hmpIndexTransport
  have hsMtIndex := hsmall _ hmtIndex
  have hsWeakValueEquality := hsmall _ hweakValueEquality
  have hsWeakValueSymmetry := hsmall _ hweakValueSymmetry
  have hsMpValueSymmetry := hsmall _ hmpValueSymmetry
  have hsWeakValueTransport := hsmall _ hweakValueTransport
  have hsMpValueTransport := hsmall _ hmpValueTransport
  have hsMtValue := hsmall _ hmtValue
  unfold compileNegativeBinaryBitAtValuationConnectorPolynomial
    binaryBitValuationConnectorUniformPolynomial
  dsimp only [Gamma, sourceFormula, sourceAtom, indexEqualityFormula,
    indexReverseEqualityFormula, indexAtom, valueEqualityFormula,
    valueReverseEqualityFormula, resultAtom,
    reverseIndexTransportConsequent, reverseValueTransportConsequent,
    indexSymmetryFormula, indexTransportFormula, valueSymmetryFormula,
    valueTransportFormula, termResource, formulaResource] at *
  omega

def compileNegativeBinaryBitAtValuationPayloadPolynomial
    (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : Nat :=
  binaryBitLiteralPayloadPolynomial
      (termValue valuation indexTerm) (termValue valuation valueTerm) +
    compileNegativeBinaryBitAtValuationConnectorPolynomial
      valuation indexTerm valueTerm

theorem compileNegativeBinaryBitAtValuationPayloadResource_le_publicPolynomial_of_card
    (valuation : Nat -> Nat) (indexTerm valueTerm : ValuationTerm)
    (hvars :
      (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4) :
    compileNegativeBinaryBitAtValuationPayloadResource
        valuation indexTerm valueTerm <=
      compileNegativeBinaryBitAtValuationPayloadPolynomial
        valuation indexTerm valueTerm := by
  let index := termValue valuation indexTerm
  let value := termValue valuation valueTerm
  let shortIndex := shortBinaryNumeralTerm index
  let shortValue := shortBinaryNumeralTerm value
  let Gamma := binaryBitValuationContext valuation indexTerm valueTerm
  let sourceFormula := binaryBitValuationSourceFormula false
    valuation indexTerm valueTerm
  let sourceAtom := binaryBitValuationSourceAtomFormula
    valuation indexTerm valueTerm
  let indexEqualityFormula := binaryBitValuationIndexEqualityFormula
    valuation indexTerm
  let indexReverseEqualityFormula :=
    binaryBitValuationIndexReverseEqualityFormula valuation indexTerm
  let indexAtom := binaryBitValuationIndexAtomFormula
    valuation indexTerm valueTerm
  let valueEqualityFormula := binaryBitValuationValueEqualityFormula
    valuation valueTerm
  let valueReverseEqualityFormula :=
    binaryBitValuationValueReverseEqualityFormula valuation valueTerm
  let resultAtom := binaryBitValuationResultAtomFormula indexTerm valueTerm
  let reverseIndexTransportConsequent := indexAtom 🡒 sourceAtom
  let reverseValueTransportConsequent := resultAtom 🡒 indexAtom
  let termResource := binaryBitValuationTermCodeResource
    valuation indexTerm valueTerm
  have hcard : Gamma.card <= 4 :=
    binaryBitValuationContext_card_le_four_of_union_card
      valuation indexTerm valueTerm hvars
  have hindexCard : indexTerm.freeVariables.card <= 4 := by
    exact (Finset.card_le_card Finset.subset_union_left).trans hvars
  have hvalueCard : valueTerm.freeVariables.card <= 4 := by
    exact (Finset.card_le_card Finset.subset_union_right).trans hvars
  rcases binaryBitValuationTermCodes_le_resource
      valuation indexTerm valueTerm with
    ⟨hshortIndex, hindexTerm, hshortValue, hvalueTerm⟩
  have hindexEquality :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial_of_card
      valuation indexTerm hindexCard
  have hvalueEquality :=
    compileTermValueEqualityPayloadResource_le_publicPolynomial_of_card
      valuation valueTerm hvalueCard
  have hindexSymmetry :=
    binaryBitEqualitySymmetryImplicationPayloadResource_le_termPolynomial
      shortIndex indexTerm termResource hshortIndex hindexTerm
  have hvalueSymmetry :=
    binaryBitEqualitySymmetryImplicationPayloadResource_le_termPolynomial
      shortValue valueTerm termResource hshortValue hvalueTerm
  have hindexTransport :=
    binaryBitIndexTransportPayloadResource_le_termPolynomial
      indexTerm shortIndex shortValue termResource
      hindexTerm hshortIndex hshortValue
  have hvalueTransport :=
    binaryBitValueTransportPayloadResource_le_termPolynomial
      indexTerm valueTerm shortValue termResource
      hindexTerm hvalueTerm hshortValue
  have hweakSource := weakeningFullAssemblyCost_insert_le_public
    Gamma sourceFormula hcard
  have hweakIndexEquality := weakeningFullAssemblyCost_insert_le_public
    Gamma indexEqualityFormula hcard
  have hweakIndexSymmetry := weakeningFullAssemblyCost_insert_le_public
    Gamma (indexEqualityFormula 🡒 indexReverseEqualityFormula) hcard
  have hmpIndexSymmetry := contextualModusPonensFullAssemblyCost_le_public
    Gamma indexEqualityFormula indexReverseEqualityFormula hcard
  have hweakIndexTransport := weakeningFullAssemblyCost_insert_le_public
    Gamma (indexReverseEqualityFormula 🡒 reverseIndexTransportConsequent)
      hcard
  have hmpIndexTransport := contextualModusPonensFullAssemblyCost_le_public
    Gamma indexReverseEqualityFormula reverseIndexTransportConsequent hcard
  have hmtIndex := modusTollensFullAssemblyCost_le_public
    Gamma indexAtom sourceAtom hcard
  have hweakValueEquality := weakeningFullAssemblyCost_insert_le_public
    Gamma valueEqualityFormula hcard
  have hweakValueSymmetry := weakeningFullAssemblyCost_insert_le_public
    Gamma (valueEqualityFormula 🡒 valueReverseEqualityFormula) hcard
  have hmpValueSymmetry := contextualModusPonensFullAssemblyCost_le_public
    Gamma valueEqualityFormula valueReverseEqualityFormula hcard
  have hweakValueTransport := weakeningFullAssemblyCost_insert_le_public
    Gamma (valueReverseEqualityFormula 🡒 reverseValueTransportConsequent)
      hcard
  have hmpValueTransport := contextualModusPonensFullAssemblyCost_le_public
    Gamma valueReverseEqualityFormula reverseValueTransportConsequent hcard
  have hmtValue := modusTollensFullAssemblyCost_le_public
    Gamma resultAtom indexAtom hcard
  unfold compileNegativeBinaryBitAtValuationPayloadResource
    compileNegativeBinaryBitAtValuationPayloadPolynomial
    compileNegativeBinaryBitAtValuationConnectorPolynomial
  dsimp only [index, value, shortIndex, shortValue, Gamma,
    sourceFormula, sourceAtom, indexEqualityFormula,
    indexReverseEqualityFormula, indexAtom, valueEqualityFormula,
    valueReverseEqualityFormula, resultAtom,
    reverseIndexTransportConsequent, reverseValueTransportConsequent,
    termResource] at *
  omega

theorem compileNegativeBinaryBitAtValuationPayloadResource_le_publicPolynomial
    (valuation : Nat -> Nat) (indexTerm valueTerm : ValuationTerm)
    (hindexVars : indexTerm.freeVariables ⊆ {0})
    (hvalueVars : valueTerm.freeVariables ⊆ {0}) :
    compileNegativeBinaryBitAtValuationPayloadResource
        valuation indexTerm valueTerm <=
      compileNegativeBinaryBitAtValuationPayloadPolynomial
        valuation indexTerm valueTerm := by
  exact
    compileNegativeBinaryBitAtValuationPayloadResource_le_publicPolynomial_of_card
      valuation indexTerm valueTerm
      (binaryBitFreeVariables_card_le_four_of_subset_singleton
        indexTerm valueTerm hindexVars hvalueVars)

/-! ## Boolean endpoint -/

def compileBinaryBitLiteralAtValuationConnectorPolynomial
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : Nat :=
  if expected then
    compilePositiveBinaryBitAtValuationConnectorPolynomial
      valuation indexTerm valueTerm
  else
    compileNegativeBinaryBitAtValuationConnectorPolynomial
      valuation indexTerm valueTerm

theorem compileBinaryBitLiteralAtValuationConnectorPolynomial_le_uniform
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (contextBound termBound equalityBound : Nat)
    (hcontext : formulaCodeSum
      (binaryBitValuationContext valuation indexTerm valueTerm) <=
        contextBound)
    (htermResource :
      binaryBitValuationTermCodeResource valuation indexTerm valueTerm <=
        termBound)
    (hindexEquality :
      compileTermValueEqualityPayloadPolynomial valuation indexTerm <=
        equalityBound)
    (hvalueEquality :
      compileTermValueEqualityPayloadPolynomial valuation valueTerm <=
        equalityBound) :
    compileBinaryBitLiteralAtValuationConnectorPolynomial expected valuation
        indexTerm valueTerm <=
      binaryBitValuationConnectorUniformPolynomial contextBound termBound
        equalityBound := by
  cases expected with
  | false =>
      simpa [compileBinaryBitLiteralAtValuationConnectorPolynomial] using
        compileNegativeBinaryBitAtValuationConnectorPolynomial_le_uniform
          valuation indexTerm valueTerm contextBound termBound equalityBound
          hcontext htermResource hindexEquality hvalueEquality
  | true =>
      simpa [compileBinaryBitLiteralAtValuationConnectorPolynomial] using
        compilePositiveBinaryBitAtValuationConnectorPolynomial_le_uniform
          valuation indexTerm valueTerm contextBound termBound equalityBound
          hcontext htermResource hindexEquality hvalueEquality

theorem compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound_of_card
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) (sourceBound : Nat)
    (hvars :
      (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4)
    (hsource : binaryBitLiteralPayloadPolynomial
      (termValue valuation indexTerm) (termValue valuation valueTerm) <=
        sourceBound) :
    compileBinaryBitLiteralAtValuationPayloadResource expected
        valuation indexTerm valueTerm <=
      sourceBound +
        compileBinaryBitLiteralAtValuationConnectorPolynomial expected
          valuation indexTerm valueTerm := by
  cases expected with
  | false =>
      have hpublic :=
        compileNegativeBinaryBitAtValuationPayloadResource_le_publicPolynomial_of_card
          valuation indexTerm valueTerm hvars
      simp only [compileBinaryBitLiteralAtValuationPayloadResource,
        compileBinaryBitLiteralAtValuationConnectorPolynomial,
        Bool.false_eq_true, ↓reduceIte]
      unfold compileNegativeBinaryBitAtValuationPayloadPolynomial at hpublic
      omega
  | true =>
      have hpublic :=
        compilePositiveBinaryBitAtValuationPayloadResource_le_publicPolynomial_of_card
          valuation indexTerm valueTerm hvars
      simp only [compileBinaryBitLiteralAtValuationPayloadResource,
        compileBinaryBitLiteralAtValuationConnectorPolynomial,
        ↓reduceIte]
      unfold compilePositiveBinaryBitAtValuationPayloadPolynomial at hpublic
      omega

theorem compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) (sourceBound : Nat)
    (hindexVars : indexTerm.freeVariables ⊆ {0})
    (hvalueVars : valueTerm.freeVariables ⊆ {0})
    (hsource : binaryBitLiteralPayloadPolynomial
      (termValue valuation indexTerm) (termValue valuation valueTerm) <=
        sourceBound) :
    compileBinaryBitLiteralAtValuationPayloadResource expected
        valuation indexTerm valueTerm <=
      sourceBound +
        compileBinaryBitLiteralAtValuationConnectorPolynomial expected
          valuation indexTerm valueTerm := by
  exact
    compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound_of_card
      expected valuation indexTerm valueTerm sourceBound
      (binaryBitFreeVariables_card_le_four_of_subset_singleton
        indexTerm valueTerm hindexVars hvalueVars)
      hsource

def compileBinaryBitLiteralAtValuationPayloadPolynomial
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm) : Nat :=
  if expected then
    compilePositiveBinaryBitAtValuationPayloadPolynomial
      valuation indexTerm valueTerm
  else
    compileNegativeBinaryBitAtValuationPayloadPolynomial
      valuation indexTerm valueTerm

theorem compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hvars :
      (indexTerm.freeVariables ∪ valueTerm.freeVariables).card <= 4) :
    compileBinaryBitLiteralAtValuationPayloadResource expected
        valuation indexTerm valueTerm <=
      compileBinaryBitLiteralAtValuationPayloadPolynomial expected
        valuation indexTerm valueTerm := by
  cases expected with
  | false =>
      simpa [compileBinaryBitLiteralAtValuationPayloadResource,
        compileBinaryBitLiteralAtValuationPayloadPolynomial] using
        compileNegativeBinaryBitAtValuationPayloadResource_le_publicPolynomial_of_card
          valuation indexTerm valueTerm hvars
  | true =>
      simpa [compileBinaryBitLiteralAtValuationPayloadResource,
        compileBinaryBitLiteralAtValuationPayloadPolynomial] using
        compilePositiveBinaryBitAtValuationPayloadResource_le_publicPolynomial_of_card
          valuation indexTerm valueTerm hvars

theorem compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial
    (expected : Bool) (valuation : Nat -> Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hindexVars : indexTerm.freeVariables ⊆ {0})
    (hvalueVars : valueTerm.freeVariables ⊆ {0}) :
    compileBinaryBitLiteralAtValuationPayloadResource expected
        valuation indexTerm valueTerm <=
      compileBinaryBitLiteralAtValuationPayloadPolynomial expected
        valuation indexTerm valueTerm := by
  exact
    compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
      expected valuation indexTerm valueTerm
      (binaryBitFreeVariables_card_le_four_of_subset_singleton
        indexTerm valueTerm hindexVars hvalueVars)

#print axioms binaryBitAtomAtTerms_code_length_le_uniform
#print axioms binaryBitLiteralAtTerms_code_length_le_uniform
#print axioms binaryBitValuationBaseFormulaCodes_le_uniform
#print axioms binaryBitValuation_implication_second_code_le_stageTwo
#print axioms binaryBitValuation_negated_stageTwo_code_le_closure
#print axioms contextualModusPonensFullAssemblyCost_le_public
#print axioms modusTollensFullAssemblyCost_le_public
#print axioms binaryBitValuationContext_card_le_four
#print axioms
  compilePositiveBinaryBitAtValuationPayloadResource_le_publicPolynomial_of_card
#print axioms
  compilePositiveBinaryBitAtValuationPayloadResource_le_publicPolynomial
#print axioms
  compileNegativeBinaryBitAtValuationPayloadResource_le_publicPolynomial_of_card
#print axioms
  compileNegativeBinaryBitAtValuationPayloadResource_le_publicPolynomial
#print axioms
  compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial_of_card
#print axioms
  compileBinaryBitLiteralAtValuationPayloadResource_le_publicPolynomial
#print axioms
  compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound_of_card
#print axioms
  compileBinaryBitLiteralAtValuationPayloadResource_le_sourceBound
#print axioms
  compilePositiveBinaryBitAtValuationConnectorPolynomial_le_uniform
#print axioms
  compileNegativeBinaryBitAtValuationConnectorPolynomial_le_uniform
#print axioms
  compileBinaryBitLiteralAtValuationConnectorPolynomial_le_uniform

end FoundationCompactPABitMembershipValuationCompilerPublicBounds
