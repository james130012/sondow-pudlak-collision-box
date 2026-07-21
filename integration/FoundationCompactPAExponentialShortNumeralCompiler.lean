import integration.FoundationCompactPAExponentialRuleCompiler
import integration.FoundationCompactPAValuationTermCompiler

/-!
# Fast exponential proofs at the exact short-binary numeral coordinate

The recursive exponential compiler uses linear-size arithmetic terms for the
exponent and value.  The direct proof predicate is instantiated with short
binary numerals instead.  This module constructs checked PA equalities between
those two presentations before transporting the exponential fact.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExponentialShortNumeralCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralMultiplication
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExponentialRuleCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

def exponentialShortNumeralFormula
    (height : Nat) : LO.FirstOrder.ArithmeticProposition :=
  “!expDef !!(shortBinaryNumeralTerm (2 ^ height))
      !!(shortBinaryNumeralTerm height)”

def exponentialValueTransportSentence :
    LO.FirstOrder.ArithmeticSentence :=
  “∀ leftValue rightValue exponent,
    leftValue = rightValue →
    (!expDef leftValue exponent →
      !expDef rightValue exponent)”

theorem models_exponentialValueTransportSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ exponentialValueTransportSentence := by
  rw [models_iff]
  simp only [exponentialValueTransportSentence,
    Semiformula.eval_all, LO.LogicalConnective.HomClass.map_imply]
  intro leftValue rightValue exponent hvalue
  have hvalue' : leftValue = rightValue := by
    simpa using hvalue
  clear hvalue
  subst rightValue
  exact fun hExp => by simpa using hExp

theorem exponentialValueTransportSentence_provable :
    PA ⊢ exponentialValueTransportSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    exponentialValueTransportSentence
  intro M _ _
  exact models_exponentialValueTransportSentence M

noncomputable def exponentialValueTransportCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb exponentialValueTransportSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable exponentialValueTransportSentence_provable

def exponentialExponentTransportSentence :
    LO.FirstOrder.ArithmeticSentence :=
  “∀ value leftExponent rightExponent,
    leftExponent = rightExponent →
    (!expDef value leftExponent →
      !expDef value rightExponent)”

theorem models_exponentialExponentTransportSentence
    (M : Type*) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* PA] :
    M↓[ℒₒᵣ] ⊧ exponentialExponentTransportSentence := by
  rw [models_iff]
  simp only [exponentialExponentTransportSentence,
    Semiformula.eval_all, LO.LogicalConnective.HomClass.map_imply]
  intro value leftExponent rightExponent hexponent
  have hexponent' : leftExponent = rightExponent := by
    simpa using hexponent
  clear hexponent
  subst rightExponent
  exact fun hExp => by simpa using hExp

theorem exponentialExponentTransportSentence_provable :
    PA ⊢ exponentialExponentTransportSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} PA
    exponentialExponentTransportSentence
  intro M _ _
  exact models_exponentialExponentTransportSentence M

noncomputable def exponentialExponentTransportCertifiedProof :
    CertifiedPAProof
      (Rewriting.emb exponentialExponentTransportSentence :
        LO.FirstOrder.ArithmeticProposition) :=
  certifiedProofOfProvable exponentialExponentTransportSentence_provable

theorem subst_expDef_instance
    {sourceArity targetArity : Nat}
    (values : Fin sourceArity →
      LO.FirstOrder.ArithmeticSemiterm Nat targetArity)
    (first second :
      LO.FirstOrder.ArithmeticSemiterm Nat sourceArity) :
    Rewriting.app (Rew.subst values)
        ((Rewriting.emb expDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2)/[first, second]) =
      (Rewriting.emb expDef.val :
        LO.FirstOrder.ArithmeticSemiformula Nat 2)/[
          Rew.subst values first, Rew.subst values second] := by
  rw [← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
  congr 2
  congr 1
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index =>
      cases index using Fin.cases with
      | zero => rfl
      | succ index => exact Fin.elim0 index

theorem q_subst_expDef_instance
    {sourceArity targetArity : Nat}
    (values : Fin sourceArity →
      LO.FirstOrder.ArithmeticSemiterm Nat targetArity)
    (first second :
      LO.FirstOrder.ArithmeticSemiterm Nat (sourceArity + 1)) :
    Rewriting.app (Rew.subst values).q
        ((Rewriting.emb expDef.val :
          LO.FirstOrder.ArithmeticSemiformula Nat 2)/[first, second]) =
      (Rewriting.emb expDef.val :
        LO.FirstOrder.ArithmeticSemiformula Nat 2)/[
          (Rew.subst values).q first,
          (Rew.subst values).q second] := by
  rw [Rew.q_subst]
  exact subst_expDef_instance
    (#0 :> Rew.bShift ∘ values) first second

def exponentialValueTransportOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰
    (#2 = #1 →
      (!expDef #2 #0 → !expDef #1 #0))”

theorem exponentialValueTransportSentence_emb_formula :
    (Rewriting.emb exponentialValueTransportSentence :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ exponentialValueTransportOuterBody := by
  simp [exponentialValueTransportSentence,
    exponentialValueTransportOuterBody]
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
    | zero => rfl
    | succ index =>
        cases index using Fin.cases with
        | zero => rfl
        | succ index => exact Fin.elim0 index

noncomputable def exponentialValueTransportUniversalProof :
    CertifiedPAProof (∀⁰ exponentialValueTransportOuterBody) :=
  CertifiedPAProof.cast
    exponentialValueTransportSentence_emb_formula
    exponentialValueTransportCertifiedProof

def exponentialValueTransportMiddleBody
    (leftValue : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    (!!(Rew.bShift (Rew.bShift leftValue)) = #1 →
      (!expDef !!(Rew.bShift (Rew.bShift leftValue)) #0 →
        !expDef #1 #0))”

theorem exponentialValueTransportAfterFirst_formula
    (leftValue : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    exponentialValueTransportOuterBody/[leftValue] =
      ∀⁰ exponentialValueTransportMiddleBody leftValue := by
  simp [exponentialValueTransportOuterBody,
    exponentialValueTransportMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]
  constructor <;>
    rw [Rew.q_subst, Rew.q_subst, subst_expDef_instance] <;>
    congr 1 <;>
    funext index <;>
    cases index using Fin.cases <;>
    simp [Rew.comp_app, substQQ_bvarOne, substQQ_bvarTwo]

def exponentialValueTransportInnerBody
    (leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift leftValue) = !!(Rew.bShift rightValue) →
    (!expDef !!(Rew.bShift leftValue) #0 →
      !expDef !!(Rew.bShift rightValue) #0)”

theorem exponentialValueTransportAfterSecond_formula
    (leftValue rightValue :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (exponentialValueTransportMiddleBody leftValue)/[rightValue] =
      ∀⁰ exponentialValueTransportInnerBody leftValue rightValue := by
  have hleft :
      (Rew.subst ![rightValue]).q
          (Rew.bShift (Rew.bShift leftValue)) =
        Rew.bShift leftValue := by
    simp
  simp [exponentialValueTransportMiddleBody,
    exponentialValueTransportInnerBody, substQ_bvarOne, hleft]
  constructor <;>
    rw [q_subst_expDef_instance] <;>
    simp [substQ_bvarOne, hleft]

theorem exponentialValueTransportFinal_formula
    (leftValue rightValue exponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (exponentialValueTransportInnerBody
      leftValue rightValue)/[exponent] =
      (“!!leftValue = !!rightValue →
        (!expDef !!leftValue !!exponent →
          !expDef !!rightValue !!exponent)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [exponentialValueTransportInnerBody]
  constructor <;>
    rw [subst_expDef_instance] <;>
    simp

noncomputable def exponentialValueTransportImplication
    (leftValue rightValue exponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!leftValue = !!rightValue →
        (!expDef !!leftValue !!exponent →
          !expDef !!rightValue !!exponent)” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeThriceWithCasts
    exponentialValueTransportUniversalProof
    leftValue rightValue exponent
    (exponentialValueTransportAfterFirst_formula leftValue)
    (exponentialValueTransportAfterSecond_formula leftValue rightValue)
    (exponentialValueTransportFinal_formula
      leftValue rightValue exponent)

def exponentialExponentTransportOuterBody :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰ ∀⁰
    (#1 = #0 →
      (!expDef #2 #1 → !expDef #2 #0))”

theorem exponentialExponentTransportSentence_emb_formula :
    (Rewriting.emb exponentialExponentTransportSentence :
      LO.FirstOrder.ArithmeticProposition) =
      ∀⁰ exponentialExponentTransportOuterBody := by
  simp [exponentialExponentTransportSentence,
    exponentialExponentTransportOuterBody]
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
    | zero => rfl
    | succ index =>
        cases index using Fin.cases with
        | zero => rfl
        | succ index => exact Fin.elim0 index

noncomputable def exponentialExponentTransportUniversalProof :
    CertifiedPAProof (∀⁰ exponentialExponentTransportOuterBody) :=
  CertifiedPAProof.cast
    exponentialExponentTransportSentence_emb_formula
    exponentialExponentTransportCertifiedProof

def exponentialExponentTransportMiddleBody
    (value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “∀⁰
    (#1 = #0 →
      (!expDef !!(Rew.bShift (Rew.bShift value)) #1 →
        !expDef !!(Rew.bShift (Rew.bShift value)) #0))”

theorem exponentialExponentTransportAfterFirst_formula
    (value : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    exponentialExponentTransportOuterBody/[value] =
      ∀⁰ exponentialExponentTransportMiddleBody value := by
  simp [exponentialExponentTransportOuterBody,
    exponentialExponentTransportMiddleBody,
    substQQ_bvarOne, substQQ_bvarTwo]
  constructor <;>
    rw [Rew.q_subst, Rew.q_subst, subst_expDef_instance] <;>
    simp [substQQ_bvarOne, substQQ_bvarTwo]

def exponentialExponentTransportInnerBody
    (value leftExponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift leftExponent) = #0 →
    (!expDef !!(Rew.bShift value) !!(Rew.bShift leftExponent) →
      !expDef !!(Rew.bShift value) #0)”

theorem exponentialExponentTransportAfterSecond_formula
    (value leftExponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (exponentialExponentTransportMiddleBody value)/[leftExponent] =
      ∀⁰ exponentialExponentTransportInnerBody value leftExponent := by
  have hvalue :
      (Rew.subst ![leftExponent]).q
          (Rew.bShift (Rew.bShift value)) =
        Rew.bShift value := by
    simp
  simp [exponentialExponentTransportMiddleBody,
    exponentialExponentTransportInnerBody, substQ_bvarOne, hvalue]
  constructor <;>
    rw [q_subst_expDef_instance] <;>
    simp [substQ_bvarOne, hvalue]

theorem exponentialExponentTransportFinal_formula
    (value leftExponent rightExponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (exponentialExponentTransportInnerBody
      value leftExponent)/[rightExponent] =
      (“!!leftExponent = !!rightExponent →
        (!expDef !!value !!leftExponent →
          !expDef !!value !!rightExponent)” :
        LO.FirstOrder.ArithmeticProposition) := by
  simp [exponentialExponentTransportInnerBody]
  constructor <;>
    rw [subst_expDef_instance] <;>
    simp

noncomputable def exponentialExponentTransportImplication
    (value leftExponent rightExponent :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!leftExponent = !!rightExponent →
        (!expDef !!value !!leftExponent →
          !expDef !!value !!rightExponent)” :
        LO.FirstOrder.ArithmeticProposition) :=
  specializeThriceWithCasts
    exponentialExponentTransportUniversalProof
    value leftExponent rightExponent
    (exponentialExponentTransportAfterFirst_formula value)
    (exponentialExponentTransportAfterSecond_formula value leftExponent)
    (exponentialExponentTransportFinal_formula
      value leftExponent rightExponent)

theorem exponentialExponentTerm_freeVariables_eq_empty
    (height : Nat) :
    (exponentialExponentTerm height).freeVariables = ∅ := by
  induction height with
  | zero =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro index hindex
      simp [exponentialExponentTerm, closedNumeralTerm,
        Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
        Semiterm.freeVariables_func, Rew.func] at hindex
  | succ height ih =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro index hindex
      simp [exponentialExponentTerm, Semiterm.Operator.operator,
        Semiterm.Operator.Add.term_eq, Semiterm.Operator.numeral_one,
        Semiterm.freeVariables_func, Rew.func, ih] at hindex

theorem exponentialPowerValueTerm_freeVariables_eq_empty
    (height : Nat) :
    (exponentialPowerValueTerm height).freeVariables = ∅ := by
  induction height with
  | zero =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro index hindex
      simp [exponentialPowerValueTerm, closedNumeralTerm,
        Semiterm.Operator.operator, Semiterm.Operator.numeral_one,
        Semiterm.freeVariables_func, Rew.func] at hindex
  | succ height ih =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro index hindex
      simp [exponentialPowerValueTerm, Semiterm.Operator.operator,
        Semiterm.Operator.Mul.term_eq, Semiterm.Operator.numeral,
        Semiterm.freeVariables_func, Rew.func, ih] at hindex

theorem termValue_exponentialExponentTerm
    (height : Nat) (valuation : Nat → Nat) :
    termValue valuation (exponentialExponentTerm height) = height := by
  simpa [termValue] using exponentialExponentTerm_val height valuation

theorem termValue_exponentialPowerValueTerm
    (height : Nat) (valuation : Nat → Nat) :
    termValue valuation (exponentialPowerValueTerm height) = 2 ^ height := by
  simpa [termValue] using exponentialPowerValueTerm_val height valuation

def certifiedProofOfEmptyContext
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAContextProof ∅ formula) :
    CertifiedPAProof formula where
  derivation := by simpa using proof.derivation
  certificate := proof.certificate
  certificate_valid := by simpa using proof.certificate_valid

noncomputable def exponentialExponentShortToRecursiveProof
    (height : Nat) :
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm height) =
        !!(exponentialExponentTerm height)” :
        LO.FirstOrder.ArithmeticProposition) := by
  let raw := compileTermValueEquality
    (fun _ : Nat => 0) (exponentialExponentTerm height)
  have hcontext :
      valuationContext
          (exponentialExponentTerm height).freeVariables
          (fun _ : Nat => 0) = ∅ := by
    rw [exponentialExponentTerm_freeVariables_eq_empty]
    simp [valuationContext]
  rw [hcontext] at raw
  have hformula :
      (“!!(shortBinaryNumeralTerm
          (termValue (fun _ : Nat => 0)
            (exponentialExponentTerm height))) =
        !!(exponentialExponentTerm height)” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(shortBinaryNumeralTerm height) =
        !!(exponentialExponentTerm height)” :
        LO.FirstOrder.ArithmeticProposition) := by
    rw [termValue_exponentialExponentTerm]
  exact CertifiedPAProof.cast hformula
    (certifiedProofOfEmptyContext raw)

noncomputable def exponentialValueShortToRecursiveProof
    (height : Nat) :
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm (2 ^ height)) =
        !!(exponentialPowerValueTerm height)” :
        LO.FirstOrder.ArithmeticProposition) := by
  let raw := compileTermValueEquality
    (fun _ : Nat => 0) (exponentialPowerValueTerm height)
  have hcontext :
      valuationContext
          (exponentialPowerValueTerm height).freeVariables
          (fun _ : Nat => 0) = ∅ := by
    rw [exponentialPowerValueTerm_freeVariables_eq_empty]
    simp [valuationContext]
  rw [hcontext] at raw
  have hformula :
      (“!!(shortBinaryNumeralTerm
          (termValue (fun _ : Nat => 0)
            (exponentialPowerValueTerm height))) =
        !!(exponentialPowerValueTerm height)” :
        LO.FirstOrder.ArithmeticProposition) =
      (“!!(shortBinaryNumeralTerm (2 ^ height)) =
        !!(exponentialPowerValueTerm height)” :
        LO.FirstOrder.ArithmeticProposition) := by
    rw [termValue_exponentialPowerValueTerm]
  exact CertifiedPAProof.cast hformula
    (certifiedProofOfEmptyContext raw)

theorem exponentialExponentShortToRecursiveProof_verifier_eq_true
    (height : Nat) :
    listedCompactCertifiedPAProofVerifier
        (exponentialExponentShortToRecursiveProof height).code
        (compactFormulaCode
          (“!!(shortBinaryNumeralTerm height) =
            !!(exponentialExponentTerm height)” :
            LO.FirstOrder.ArithmeticProposition)) = true :=
  (exponentialExponentShortToRecursiveProof height).verifier_eq_true

theorem exponentialValueShortToRecursiveProof_verifier_eq_true
    (height : Nat) :
    listedCompactCertifiedPAProofVerifier
        (exponentialValueShortToRecursiveProof height).code
        (compactFormulaCode
          (“!!(shortBinaryNumeralTerm (2 ^ height)) =
            !!(exponentialPowerValueTerm height)” :
            LO.FirstOrder.ArithmeticProposition)) = true :=
  (exponentialValueShortToRecursiveProof height).verifier_eq_true

theorem embeddedClosedNumeralZero_eq_paZeroTerm :
    (Rew.emb (closedNumeralTerm 0) :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) = paZeroTerm := by
  simp [closedNumeralTerm, paZeroTerm, arithmeticZeroTerm,
    Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.Zero.term_eq]

theorem embeddedClosedNumeralOne_eq_paOneTerm :
    (Rew.emb (closedNumeralTerm 1) :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) = paOneTerm := by
  simp [closedNumeralTerm, paOneTerm, arithmeticOneTerm,
    Semiterm.Operator.operator, Semiterm.Operator.numeral_one,
    Semiterm.Operator.One.term_eq]

theorem embeddedClosedNumeralTwo_eq_arithmeticTwoTerm :
    (Rew.emb (closedNumeralTerm 2) :
      LO.FirstOrder.ArithmeticSemiterm Nat 0) = arithmeticTwoTerm := by
  simp [closedNumeralTerm, arithmeticTwoTerm, arithmeticOneTerm,
    Semiterm.Operator.operator, Semiterm.Operator.numeral,
    Semiterm.Operator.foldr, Semiterm.Operator.comp,
    Semiterm.Operator.Add.term_eq, Semiterm.Operator.One.term_eq,
    Rew.func]
  funext index
  cases index using Fin.cases with
  | zero =>
      simp [Semiterm.Operator.One.term_eq, Rew.comp_app]
  | succ index =>
      cases index using Fin.cases with
      | zero =>
          simp [Semiterm.Operator.One.term_eq, Rew.comp_app]
      | succ index => exact Fin.elim0 index

noncomputable def exponentialExponentShortToRecursiveDirectProof :
    (height : Nat) →
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm height) =
        !!(exponentialExponentTerm height)” :
        LO.FirstOrder.ArithmeticProposition)
  | 0 => exponentialExponentShortToRecursiveProof 0
  | height + 1 => by
      let previous :=
        exponentialExponentShortToRecursiveDirectProof height
      let source := paAddTerm
        (shortBinaryNumeralTerm height) paOneTerm
      let target := paAddTerm
        (exponentialExponentTerm height) paOneTerm
      let incrementReverse := proveEqualitySymmetry source
        (shortBinaryNumeralTerm (height + 1))
        (proveBinaryNumeralIncrement height)
      let congruenceRaw := proveAddCongruence
        (shortBinaryNumeralTerm height) paOneTerm
        (exponentialExponentTerm height) paOneTerm
        previous (proveEqualityReflexivityAtTerm paOneTerm)
      let congruence : CertifiedPAProof
          (“!!source = !!target” :
            LO.FirstOrder.ArithmeticProposition) :=
        CertifiedPAProof.cast
          (addEqualityAsTerm_formula
            (shortBinaryNumeralTerm height) paOneTerm
            (exponentialExponentTerm height) paOneTerm)
          congruenceRaw
      let through := proveEqualityTransitivity
        (shortBinaryNumeralTerm (height + 1)) source target
        incrementReverse congruence
      have htarget :
          exponentialExponentTerm (height + 1) = target := by
        rw [exponentialExponentTerm]
        have hformula :
            ‘(!!(exponentialExponentTerm height) + 1)’ =
              paAddTerm (exponentialExponentTerm height)
                (Rew.emb (closedNumeralTerm 1)) := by
          simp [paAddTerm, closedNumeralTerm]
        rw [hformula, embeddedClosedNumeralOne_eq_paOneTerm]
      have hformula :
          (“!!(shortBinaryNumeralTerm (height + 1)) = !!target” :
              LO.FirstOrder.ArithmeticProposition) =
            (“!!(shortBinaryNumeralTerm (height + 1)) =
              !!(exponentialExponentTerm (height + 1))” :
              LO.FirstOrder.ArithmeticProposition) := by
        rw [htarget]
      exact CertifiedPAProof.cast hformula through

noncomputable def exponentialValueShortToRecursiveDirectProof :
    (height : Nat) →
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm (2 ^ height)) =
        !!(exponentialPowerValueTerm height)” :
        LO.FirstOrder.ArithmeticProposition)
  | 0 => exponentialValueShortToRecursiveProof 0
  | height + 1 => by
      let previous :=
        exponentialValueShortToRecursiveDirectProof height
      let source := paMulTerm arithmeticTwoTerm
        (shortBinaryNumeralTerm (2 ^ height))
      let target := paMulTerm arithmeticTwoTerm
        (exponentialPowerValueTerm height)
      let congruenceRaw := proveMulCongruence
        arithmeticTwoTerm (shortBinaryNumeralTerm (2 ^ height))
        arithmeticTwoTerm (exponentialPowerValueTerm height)
        (proveEqualityReflexivityAtTerm arithmeticTwoTerm) previous
      let congruence : CertifiedPAProof
          (“!!source = !!target” :
            LO.FirstOrder.ArithmeticProposition) :=
        CertifiedPAProof.cast
          (mulEqualityAsTerm_formula
            arithmeticTwoTerm (shortBinaryNumeralTerm (2 ^ height))
            arithmeticTwoTerm (exponentialPowerValueTerm height))
          congruenceRaw
      have hpower :
          2 ^ (height + 1) = Nat.bit false (2 ^ height) := by
        simp [pow_succ, Nat.bit_val, Nat.mul_comm]
      have hpowerNonzero : 2 ^ height ≠ 0 := by
        exact pow_ne_zero height (by decide)
      have hsource :
          shortBinaryNumeralTerm (2 ^ (height + 1)) = source := by
        rw [hpower,
          shortBinaryNumeralTerm_bit_false (2 ^ height) hpowerNonzero]
      have htarget :
          exponentialPowerValueTerm (height + 1) = target := by
        rw [exponentialPowerValueTerm]
        have hformula :
            ‘(2 * !!(exponentialPowerValueTerm height))’ =
              paMulTerm (Rew.emb (closedNumeralTerm 2))
                (exponentialPowerValueTerm height) := by
          simp [paMulTerm, closedNumeralTerm]
        rw [hformula, embeddedClosedNumeralTwo_eq_arithmeticTwoTerm]
      have hformula :
          (“!!source = !!target” :
              LO.FirstOrder.ArithmeticProposition) =
            (“!!(shortBinaryNumeralTerm (2 ^ (height + 1))) =
              !!(exponentialPowerValueTerm (height + 1))” :
              LO.FirstOrder.ArithmeticProposition) := by
        rw [hsource, htarget]
      exact CertifiedPAProof.cast hformula congruence

theorem exponentialExponentShortToRecursiveDirectProof_verifier_eq_true
    (height : Nat) :
    listedCompactCertifiedPAProofVerifier
        (exponentialExponentShortToRecursiveDirectProof height).code
        (compactFormulaCode
          (“!!(shortBinaryNumeralTerm height) =
            !!(exponentialExponentTerm height)” :
            LO.FirstOrder.ArithmeticProposition)) = true :=
  (exponentialExponentShortToRecursiveDirectProof height).verifier_eq_true

theorem exponentialValueShortToRecursiveDirectProof_verifier_eq_true
    (height : Nat) :
    listedCompactCertifiedPAProofVerifier
        (exponentialValueShortToRecursiveDirectProof height).code
        (compactFormulaCode
          (“!!(shortBinaryNumeralTerm (2 ^ height)) =
            !!(exponentialPowerValueTerm height)” :
            LO.FirstOrder.ArithmeticProposition)) = true :=
  (exponentialValueShortToRecursiveDirectProof height).verifier_eq_true

noncomputable def exponentialExponentRecursiveToShortProof
    (height : Nat) :
    CertifiedPAProof
      (“!!(exponentialExponentTerm height) =
        !!(shortBinaryNumeralTerm height)” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveEqualitySymmetry
    (shortBinaryNumeralTerm height)
    (exponentialExponentTerm height)
    (exponentialExponentShortToRecursiveDirectProof height)

noncomputable def exponentialValueRecursiveToShortProof
    (height : Nat) :
    CertifiedPAProof
      (“!!(exponentialPowerValueTerm height) =
        !!(shortBinaryNumeralTerm (2 ^ height))” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveEqualitySymmetry
    (shortBinaryNumeralTerm (2 ^ height))
    (exponentialPowerValueTerm height)
    (exponentialValueShortToRecursiveDirectProof height)

/--
Checked PA proof of the exact `expDef` instance used by the direct proof
predicate.  The exponential fact is first built at recursive linear terms and
then transported, by proved equalities, to both short-binary numeral terms.
-/
noncomputable def proveExponentialPowerAtShortNumerals
    (height : Nat) :
    CertifiedPAProof (exponentialShortNumeralFormula height) := by
  let recursiveValue := exponentialPowerValueTerm height
  let shortValue := shortBinaryNumeralTerm (2 ^ height)
  let recursiveExponent := exponentialExponentTerm height
  let shortExponent := shortBinaryNumeralTerm height
  let valueTransportAfterEquality :=
    CertifiedPAProof.modusPonens
      (exponentialValueTransportImplication
        recursiveValue shortValue recursiveExponent)
      (exponentialValueRecursiveToShortProof height)
  let shortValueFact :=
    CertifiedPAProof.modusPonens valueTransportAfterEquality
      (proveExponentialPower height)
  let exponentTransportAfterEquality :=
    CertifiedPAProof.modusPonens
      (exponentialExponentTransportImplication
        shortValue recursiveExponent shortExponent)
      (exponentialExponentRecursiveToShortProof height)
  exact CertifiedPAProof.modusPonens
    exponentTransportAfterEquality shortValueFact

theorem proveExponentialPowerAtShortNumerals_verifier_eq_true
    (height : Nat) :
    listedCompactCertifiedPAProofVerifier
        (proveExponentialPowerAtShortNumerals height).code
        (compactFormulaCode
          (exponentialShortNumeralFormula height)) = true :=
  (proveExponentialPowerAtShortNumerals height).verifier_eq_true

#print axioms exponentialExponentTerm_freeVariables_eq_empty
#print axioms exponentialPowerValueTerm_freeVariables_eq_empty
#print axioms models_exponentialValueTransportSentence
#print axioms exponentialValueTransportSentence_provable
#print axioms exponentialValueTransportCertifiedProof
#print axioms models_exponentialExponentTransportSentence
#print axioms exponentialExponentTransportSentence_provable
#print axioms exponentialExponentTransportCertifiedProof
#print axioms exponentialExponentShortToRecursiveProof
#print axioms exponentialValueShortToRecursiveProof
#print axioms exponentialExponentShortToRecursiveProof_verifier_eq_true
#print axioms exponentialValueShortToRecursiveProof_verifier_eq_true
#print axioms exponentialExponentShortToRecursiveDirectProof
#print axioms exponentialValueShortToRecursiveDirectProof
#print axioms exponentialExponentShortToRecursiveDirectProof_verifier_eq_true
#print axioms exponentialValueShortToRecursiveDirectProof_verifier_eq_true
#print axioms exponentialExponentRecursiveToShortProof
#print axioms exponentialValueRecursiveToShortProof
#print axioms proveExponentialPowerAtShortNumerals
#print axioms proveExponentialPowerAtShortNumerals_verifier_eq_true

end FoundationCompactPAExponentialShortNumeralCompiler
