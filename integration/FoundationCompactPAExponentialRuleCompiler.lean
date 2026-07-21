import integration.FoundationCompactPAQuantitativeCompilerCore
import Foundation.FirstOrder.Arithmetic.Exponential.Exp

/-!
# Fixed PA rule for the exponential graph

The bounded verifier formulas use `expDef` to state that a large table bound
is a power of two.  Compiling the definition by numeric bounded enumeration
is exponentially expensive.  This module instead fixes one genuine PA proof
of the uniform successor rule and later specializes that proof at short
binary numerals.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExponentialRuleCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactCertifiedDerivationSpecialization
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

def exponentialZeroSentence : LO.FirstOrder.ArithmeticSentence :=
  “!expDef 1 0”

theorem models_exponentialZeroSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ exponentialZeroSentence := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
    ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ PA inferInstance
  rw [models_iff]
  simp [exponentialZeroSentence, expDef]

theorem exponentialZeroSentence_provable :
    PA ⊢ exponentialZeroSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA exponentialZeroSentence
  intro M _ _
  exact models_exponentialZeroSentence M

def exponentialSuccSentence : LO.FirstOrder.ArithmeticSentence :=
  “∀ x y, !expDef y x → !expDef (2 * y) (x + 1)”

theorem models_exponentialSuccSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ exponentialSuccSentence := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
    ModelsTheory.of_provably_subtheory M 𝗜𝚺₁ PA inferInstance
  rw [models_iff]
  simp only [exponentialSuccSentence, Semiformula.eval_all,
    LO.LogicalConnective.HomClass.map_imply]
  intro exponent value
  simpa [expDef, exponential_graph] using
    (fun hExp : Exponential exponent value => Exponential.succ hExp)

theorem exponentialSuccSentence_provable :
    PA ⊢ exponentialSuccSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA exponentialSuccSentence
  intro M _ _
  exact models_exponentialSuccSentence M

noncomputable def certifiedProofOfProvable
    {sentence : LO.FirstOrder.ArithmeticSentence}
    (hprovable : PA ⊢ sentence) :
    CertifiedPAProof
      (Rewriting.emb sentence :
        LO.FirstOrder.ArithmeticProposition) := by
  let derivation :
      LO.FirstOrder.Derivation2 PA
        {(Rewriting.emb sentence :
          LO.FirstOrder.ArithmeticProposition)} :=
    Classical.choice <|
      (LO.FirstOrder.provable_iff_derivable2 (T := PA)).mp hprovable
  exact
    { derivation := derivation
      certificate := certificateOfDerivation derivation
      certificate_valid := certificateOfDerivation_valid derivation }

noncomputable def exponentialSuccDerivation :
    LO.FirstOrder.Derivation2 PA
      {(Rewriting.emb exponentialSuccSentence :
        LO.FirstOrder.ArithmeticProposition)} :=
  Classical.choice <|
    (LO.FirstOrder.provable_iff_derivable2 (T := PA)).mp
      exponentialSuccSentence_provable

noncomputable def exponentialSuccCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb exponentialSuccSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable exponentialSuccSentence_provable

noncomputable def exponentialZeroCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb exponentialZeroSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable exponentialZeroSentence_provable

/--
Term-level counterpart of `Rewriting.emb_subst_eq_subst_emb`.  The Foundation
library states the latter for formulas; the exponential specialization also
needs the same commuting square for closed arithmetic terms.
-/
theorem emb_subst_term_eq_subst_emb
    {k n : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Empty k)
    (values : Fin k → LO.FirstOrder.ArithmeticSemiterm Empty n) :
    (Rew.emb (Rew.subst values term) :
      LO.FirstOrder.ArithmeticSemiterm Nat n) =
      Rew.subst (fun index => Rew.emb (values index))
        (Rew.emb term : LO.FirstOrder.ArithmeticSemiterm Nat k) := by
  rw [← Rew.comp_app, ← Rew.comp_app]
  congr 1
  ext index
  · simp [Rew.comp_app]
  · exact Empty.elim index

/-- Embedding commutes with applying a closed arithmetic term operator. -/
theorem emb_operator_eq_operator_emb
    {k n : Nat}
    (operator : LO.FirstOrder.Semiterm.Operator ℒₒᵣ k)
    (values : Fin k → LO.FirstOrder.ArithmeticSemiterm Empty n) :
    (Rew.emb (operator.operator values) :
      LO.FirstOrder.ArithmeticSemiterm Nat n) =
      operator.operator (fun index => Rew.emb (values index)) := by
  simpa [Semiterm.Operator.operator] using
    (emb_subst_term_eq_subst_emb operator.term values)

/-- A closed arithmetic constant is unchanged by free-variable embedding. -/
theorem emb_const_eq_const
    {n : Nat} (constant : LO.FirstOrder.Semiterm.Const ℒₒᵣ) :
    (Rew.emb (constant : LO.FirstOrder.ArithmeticSemiterm Empty n) :
      LO.FirstOrder.ArithmeticSemiterm Nat n) =
      (constant : LO.FirstOrder.ArithmeticSemiterm Nat n) := by
  change Rew.emb (constant.operator ![]) = constant.operator ![]
  rw [emb_operator_eq_operator_emb]
  congr 1
  funext index
  exact Fin.elim0 index

theorem emb_two_mul_bvar :
    (Rew.emb
        (‘(2 * #0)’ : LO.FirstOrder.ArithmeticSemiterm Empty 2) :
      LO.FirstOrder.ArithmeticSemiterm Nat 2) =
      (‘(2 * #0)’ : LO.FirstOrder.ArithmeticSemiterm Nat 2) := by
  rw [show
    (‘(2 * #0)’ : LO.FirstOrder.ArithmeticSemiterm Empty 2) =
      op(*).operator
        ![((2 : Nat) : LO.FirstOrder.ArithmeticSemiterm Empty 2), #0] by
    rfl]
  rw [emb_operator_eq_operator_emb]
  congr 1
  funext index
  cases index using Fin.cases with
  | zero =>
      exact emb_const_eq_const (Semiterm.Operator.numeral ℒₒᵣ 2)
  | succ index =>
      cases index using Fin.cases with
      | zero => rfl
      | succ index => exact Fin.elim0 index

theorem emb_bvar_add_one :
    (Rew.emb
        (‘(#1 + 1)’ : LO.FirstOrder.ArithmeticSemiterm Empty 2) :
      LO.FirstOrder.ArithmeticSemiterm Nat 2) =
      (‘(#1 + 1)’ : LO.FirstOrder.ArithmeticSemiterm Nat 2) := by
  rw [show
    (‘(#1 + 1)’ : LO.FirstOrder.ArithmeticSemiterm Empty 2) =
      op(+).operator
        ![#1, ((1 : Nat) : LO.FirstOrder.ArithmeticSemiterm Empty 2)] by
    rfl]
  rw [emb_operator_eq_operator_emb]
  congr 1
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index =>
      cases index using Fin.cases with
      | zero =>
          exact emb_const_eq_const (Semiterm.Operator.numeral ℒₒᵣ 1)
      | succ index => exact Fin.elim0 index

def exponentialSuccOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ (!expDef #0 #1 → !expDef (2 * #0) (#1 + 1))”

theorem exponentialSuccSentence_emb_formula :
    (Rewriting.emb exponentialSuccSentence :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ exponentialSuccOuterBody := by
  simp [exponentialSuccSentence, exponentialSuccOuterBody]
  constructor
  · rw [Rewriting.emb_subst_eq_subst_emb]
    congr 1
    funext index
    cases index using Fin.cases with
    | zero => rfl
    | succ index =>
        cases index using Fin.cases with
        | zero => rfl
        | succ index => exact Fin.elim0 index
  · rw [Rewriting.emb_subst_eq_subst_emb]
    congr 1
    funext index
    cases index using Fin.cases with
    | zero => exact emb_two_mul_bvar
    | succ index =>
        cases index using Fin.cases with
        | zero => exact emb_bvar_add_one
        | succ index => exact Fin.elim0 index

noncomputable def exponentialSuccUniversalProof :
    CertifiedPAProof (∀⁰ exponentialSuccOuterBody) :=
  CertifiedPAProof.cast exponentialSuccSentence_emb_formula
    exponentialSuccCertifiedProof

noncomputable def exponentialSuccAfterExponent
    (exponent : LO.FirstOrder.ArithmeticSemiterm Nat 0) :=
  CertifiedPAProof.specialize exponentialSuccUniversalProof exponent

def exponentialSuccValueBody
    (exponent : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!expDef #0 !!(Rew.bShift exponent) →
    !expDef (2 * #0) (!!(Rew.bShift exponent) + 1)”

theorem exponentialSuccAfterExponent_formula
    (exponent : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    exponentialSuccOuterBody/[exponent] =
      ∀⁰ exponentialSuccValueBody exponent := by
  have hterm :
      ((Rew.subst ![exponent]).q)
          (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) =
        Rew.bShift exponent := by
    simpa using
      (Rew.q_bvar_succ (Rew.subst ![exponent]) (0 : Fin 1))
  simp [exponentialSuccOuterBody, exponentialSuccValueBody]
  constructor
  · rw [Rew.q_subst, ← TransitiveRewriting.comp_app,
      Rew.subst_comp_subst]
    congr 2
    congr 1
    funext index
    cases index using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ index =>
        cases index using Fin.cases with
        | zero => simp [Rew.comp_app]
        | succ index => exact Fin.elim0 index
  · rw [Rew.q_subst, ← TransitiveRewriting.comp_app,
      Rew.subst_comp_subst]
    congr 2
    congr 1
    funext index
    cases index using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ index =>
        cases index using Fin.cases with
        | zero => simp [Rew.comp_app]
        | succ index => exact Fin.elim0 index

noncomputable def exponentialSuccAfterExponentAsUniversal
    (exponent : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof (∀⁰ exponentialSuccValueBody exponent) :=
  CertifiedPAProof.cast
    (exponentialSuccAfterExponent_formula exponent)
    (exponentialSuccAfterExponent exponent)

noncomputable def exponentialSuccImplicationRaw
    (exponent value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      ((exponentialSuccValueBody exponent)/[value]) :=
  CertifiedPAProof.specialize
    (exponentialSuccAfterExponentAsUniversal exponent) value

theorem exponentialSuccImplicationRaw_formula
    (exponent value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (exponentialSuccValueBody exponent)/[value] =
      (“!expDef !!value !!exponent →
        !expDef (2 * !!value) (!!exponent + 1)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [exponentialSuccValueBody]
  constructor
  · rw [← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
    congr 2
    congr 1
    funext index
    cases index using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ index =>
        cases index using Fin.cases with
        | zero => simp [Rew.comp_app]
        | succ index => exact Fin.elim0 index
  · rw [← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
    congr 2
    congr 1
    funext index
    cases index using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ index =>
        cases index using Fin.cases with
        | zero => simp [Rew.comp_app]
        | succ index => exact Fin.elim0 index

noncomputable def exponentialSuccImplication
    (exponent value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!expDef !!value !!exponent →
        !expDef (2 * !!value) (!!exponent + 1)” :
        LO.FirstOrder.ArithmeticProposition) :=
  CertifiedPAProof.cast
    (exponentialSuccImplicationRaw_formula exponent value)
    (exponentialSuccImplicationRaw exponent value)

theorem exponentialSuccImplication_payloadLength_le
    (exponent value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (exponentialSuccImplication exponent value).payloadLength <=
      exponentialSuccCertifiedProof.payloadLength +
        specializationCost exponentialSuccOuterBody exponent +
        specializationCost (exponentialSuccValueBody exponent) value := by
  have hfirst := specialize_payloadLength_le_cost
    exponentialSuccUniversalProof exponent
  have hsecond := specialize_payloadLength_le_cost
    (exponentialSuccAfterExponentAsUniversal exponent) value
  change
    (CertifiedPAProof.cast
      (exponentialSuccImplicationRaw_formula exponent value)
      (exponentialSuccImplicationRaw exponent value)).payloadLength <= _
  rw [CertifiedPAProof.cast_payloadLength]
  change
    (CertifiedPAProof.specialize
      (exponentialSuccAfterExponentAsUniversal exponent) value).payloadLength <= _
  have hfirst' :
      (exponentialSuccAfterExponent exponent).payloadLength <=
        exponentialSuccCertifiedProof.payloadLength +
          specializationCost exponentialSuccOuterBody exponent := by
    change
      (CertifiedPAProof.specialize exponentialSuccUniversalProof
        exponent).payloadLength <= _
    have huniversalCast :
        exponentialSuccUniversalProof.payloadLength =
          exponentialSuccCertifiedProof.payloadLength :=
      CertifiedPAProof.cast_payloadLength
        exponentialSuccSentence_emb_formula
        exponentialSuccCertifiedProof
    calc
      (CertifiedPAProof.specialize exponentialSuccUniversalProof
          exponent).payloadLength <=
          exponentialSuccUniversalProof.payloadLength +
            specializationCost exponentialSuccOuterBody exponent :=
        hfirst
      _ = exponentialSuccCertifiedProof.payloadLength +
            specializationCost exponentialSuccOuterBody exponent := by
        rw [huniversalCast]
  have hafterCast :
      (exponentialSuccAfterExponentAsUniversal exponent).payloadLength =
        (exponentialSuccAfterExponent exponent).payloadLength :=
    CertifiedPAProof.cast_payloadLength
      (exponentialSuccAfterExponent_formula exponent)
      (exponentialSuccAfterExponent exponent)
  calc
    (CertifiedPAProof.specialize
        (exponentialSuccAfterExponentAsUniversal exponent) value).payloadLength <=
        (exponentialSuccAfterExponentAsUniversal exponent).payloadLength +
          specializationCost (exponentialSuccValueBody exponent) value :=
      hsecond
    _ = (exponentialSuccAfterExponent exponent).payloadLength +
          specializationCost (exponentialSuccValueBody exponent) value := by
      rw [hafterCast]
    _ <= (exponentialSuccCertifiedProof.payloadLength +
          specializationCost exponentialSuccOuterBody exponent) +
          specializationCost (exponentialSuccValueBody exponent) value :=
      Nat.add_le_add_right hfirst' _

/--
The exponent coordinate used by the fast `expDef` compiler.  It has one
addition node per exponent step, so its syntax is linear in `height`.
-/
def exponentialExponentTerm :
    Nat → LO.FirstOrder.ArithmeticSemiterm Nat 0
  | 0 => Rew.emb (closedNumeralTerm 0)
  | height + 1 => ‘(!!(exponentialExponentTerm height) + 1)’

/--
The value coordinate used by the fast `expDef` compiler.  The represented
number is exponential, but the term itself has only one multiplication node
per exponent step.
-/
def exponentialPowerValueTerm :
    Nat → LO.FirstOrder.ArithmeticSemiterm Nat 0
  | 0 => Rew.emb (closedNumeralTerm 1)
  | height + 1 => ‘(2 * !!(exponentialPowerValueTerm height))’

theorem exponentialZeroCertifiedProof_formula :
    (Rewriting.emb exponentialZeroSentence :
        LO.FirstOrder.ArithmeticProposition) =
      (“!expDef !!(exponentialPowerValueTerm 0)
          !!(exponentialExponentTerm 0)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp only [exponentialZeroSentence, exponentialPowerValueTerm,
    exponentialExponentTerm]
  rw [Rewriting.emb_subst_eq_subst_emb]
  congr 1
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index =>
      cases index using Fin.cases with
      | zero => rfl
      | succ index => exact Fin.elim0 index

noncomputable def exponentialPowerZeroProof :
    CertifiedPAProof
      (“!expDef !!(exponentialPowerValueTerm 0)
          !!(exponentialExponentTerm 0)” :
        LO.FirstOrder.ArithmeticProposition) :=
  CertifiedPAProof.cast exponentialZeroCertifiedProof_formula
    exponentialZeroCertifiedProof

theorem exponentialPowerStep_formula (height : Nat) :
    (“!expDef !!(exponentialPowerValueTerm height)
          !!(exponentialExponentTerm height) →
        !expDef (2 * !!(exponentialPowerValueTerm height))
          (!!(exponentialExponentTerm height) + 1)” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!expDef !!(exponentialPowerValueTerm height)
          !!(exponentialExponentTerm height) →
        !expDef !!(exponentialPowerValueTerm (height + 1))
          !!(exponentialExponentTerm (height + 1))” :
        LO.FirstOrder.ArithmeticProposition) := by
  rfl

/--
Real PA proof of `expDef(2^height, height)`.  The recursion performs exactly
`height` applications of the fixed successor theorem; it never enumerates
the represented interval of size `2^height`.
-/
noncomputable def proveExponentialPower :
    (height : Nat) →
    CertifiedPAProof
      (“!expDef !!(exponentialPowerValueTerm height)
          !!(exponentialExponentTerm height)” :
        LO.FirstOrder.ArithmeticProposition)
  | 0 => exponentialPowerZeroProof
  | height + 1 =>
      CertifiedPAProof.modusPonens
        (CertifiedPAProof.cast
          (exponentialPowerStep_formula height)
          (exponentialSuccImplication
            (exponentialExponentTerm height)
            (exponentialPowerValueTerm height)))
        (proveExponentialPower height)

theorem exponentialSuccCertifiedProof_verifier_eq_true :
    listedCompactCertifiedPAProofVerifier
      exponentialSuccCertifiedProof.code
      (compactFormulaCode
        (Rewriting.emb exponentialSuccSentence :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  exponentialSuccCertifiedProof.verifier_eq_true

theorem exponentialSuccImplication_verifier_eq_true
    (exponent value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (exponentialSuccImplication exponent value).code
      (compactFormulaCode
        (“!expDef !!value !!exponent →
          !expDef (2 * !!value) (!!exponent + 1)” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (exponentialSuccImplication exponent value).verifier_eq_true

@[simp] theorem exponentialExponentTerm_val
    (height : Nat) (valuation : Nat → Nat) :
    (exponentialExponentTerm height).val ![] valuation = height := by
  induction height with
  | zero =>
      change (closedNumeralTerm 0).val ![] Empty.elim = 0
      exact val_closedNumeralTerm 0
  | succ height ih =>
      simp [exponentialExponentTerm, ih]

@[simp] theorem exponentialPowerValueTerm_val
    (height : Nat) (valuation : Nat → Nat) :
    (exponentialPowerValueTerm height).val ![] valuation = 2 ^ height := by
  induction height with
  | zero =>
      change (closedNumeralTerm 1).val ![] Empty.elim = 1
      exact val_closedNumeralTerm 1
  | succ height ih =>
      simp [exponentialPowerValueTerm, ih, pow_succ, Nat.mul_comm]

theorem proveExponentialPower_verifier_eq_true
    (height : Nat) :
    listedCompactCertifiedPAProofVerifier
      (proveExponentialPower height).code
      (compactFormulaCode
        (“!expDef !!(exponentialPowerValueTerm height)
            !!(exponentialExponentTerm height)” :
          LO.FirstOrder.ArithmeticProposition)) = true :=
  (proveExponentialPower height).verifier_eq_true

#print axioms models_exponentialZeroSentence
#print axioms exponentialZeroSentence_provable
#print axioms exponentialZeroCertifiedProof
#print axioms models_exponentialSuccSentence
#print axioms exponentialSuccSentence_provable
#print axioms exponentialSuccCertifiedProof
#print axioms exponentialSuccCertifiedProof_verifier_eq_true
#print axioms exponentialSuccImplication
#print axioms exponentialSuccImplication_verifier_eq_true
#print axioms exponentialSuccImplication_payloadLength_le
#print axioms exponentialExponentTerm_val
#print axioms exponentialPowerValueTerm_val
#print axioms proveExponentialPower
#print axioms proveExponentialPower_verifier_eq_true

end FoundationCompactPAExponentialRuleCompiler
