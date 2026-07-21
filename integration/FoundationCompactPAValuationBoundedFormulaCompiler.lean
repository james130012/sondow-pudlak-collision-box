import integration.FoundationCompactPAValuationAtomicCompiler
import integration.FoundationCompactPAValuationContextRewriting
import integration.FoundationCompactPAContextualTermBoundedUniversalCompiler

/-!
# Proof-producing compiler for true bounded formulas under a valuation

The indexed certificate below contains only semantic atomic checks,
connective choices, explicit short-binary existential witnesses, and finite
branch certificates for bounded universals.  It stores no PA derivation,
proof code, proof-existence statement, or proof-length premise.

Compilation recursively constructs real certified `Derivation2 PA` objects.
An arbitrary bound term is normalized internally and connected to the genuine
finite-exhaustion compiler before universal introduction.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAValuationBoundedFormulaCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPACertifiedContextEquality

theorem shortBinarySubstitution_freeVariables_subset
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : Nat) :
    (body/[shortBinaryNumeralTerm witness]).freeVariables ⊆
      body.freeVariables := by
  intro index hindex
  have hrewritten :
      (body/[shortBinaryNumeralTerm witness]).FVar? index := hindex
  rcases LO.FirstOrder.Semiformula.fvar?_rew hrewritten with
      hbound | hfree
  · rcases hbound with ⟨boundIndex, himage⟩
    have hboundZero : boundIndex = (0 : Fin 1) := Fin.eq_zero boundIndex
    subst boundIndex
    have himpossible : index ∈
        (shortBinaryNumeralTerm witness).freeVariables := himage
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at himpossible
    simp at himpossible
  · rcases hfree with ⟨sourceIndex, hsource, himage⟩
    have hsame : index = sourceIndex := by
      simpa [LO.FirstOrder.Semiterm.FVar?] using himage
    subst index
    exact hsource

theorem boundSource_freeVariables_subset_universal
    (boundSource : ValuationTerm)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    boundSource.freeVariables ⊆
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift boundSource) body).freeVariables := by
  intro index hindex
  simp only [Semiformula.freeVariables_all,
    termBoundedUniversalBody, Semiformula.freeVariables_imp]
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  refine ⟨1, Finset.mem_univ _, ?_⟩
  exact LO.FirstOrder.Semiterm.fvar?_bShift.mpr hindex

theorem body_freeVariables_subset_universal
    (boundSource : ValuationTerm)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    body.freeVariables ⊆
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift boundSource) body).freeVariables := by
  intro index hindex
  simp only [Semiformula.freeVariables_all,
    termBoundedUniversalBody, Semiformula.freeVariables_imp]
  exact Finset.mem_union_right _ hindex

theorem free_bShift_term
    (term : ValuationTerm) :
    Rew.free (Rew.bShift term) = Rew.shift term := by
  rw [← Rew.comp_app]
  simp

noncomputable def lowerPositiveTerm :
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1) ->
      term.Positive -> ValuationTerm
  | #index, hpositive => by
      have himpossible : (0 : Nat) < index :=
        LO.FirstOrder.Semiterm.Positive.bvar.mp hpositive
      have hzero : index = (0 : Fin 1) := Fin.eq_zero index
      subst index
      simp at himpossible
  | &index, _ => &index
  | .func .zero _, _ => .func .zero ![]
  | .func .one _, _ => .func .one ![]
  | .func .add args, hpositive => .func .add ![
      lowerPositiveTerm (args 0)
        ((LO.FirstOrder.Semiterm.Positive.func
          Language.Add.add args).mp hpositive 0),
      lowerPositiveTerm (args 1)
        ((LO.FirstOrder.Semiterm.Positive.func
          Language.Add.add args).mp hpositive 1)]
  | .func .mul args, hpositive => .func .mul ![
      lowerPositiveTerm (args 0)
        ((LO.FirstOrder.Semiterm.Positive.func
          Language.Mul.mul args).mp hpositive 0),
      lowerPositiveTerm (args 1)
        ((LO.FirstOrder.Semiterm.Positive.func
          Language.Mul.mul args).mp hpositive 1)]

theorem bShift_lowerPositiveTerm
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (hpositive : term.Positive) :
    Rew.bShift (lowerPositiveTerm term hpositive) = term := by
  induction term with
  | bvar index =>
      have himpossible : (0 : Nat) < index :=
        LO.FirstOrder.Semiterm.Positive.bvar.mp hpositive
      have hzero : index = (0 : Fin 1) := Fin.eq_zero index
      subst index
      simp at himpossible
  | fvar index => rfl
  | @func arity functionSymbol args inductionHypothesis =>
      cases functionSymbol with
      | zero =>
          unfold lowerPositiveTerm
          simp [Rew.func]
          funext index
          exact Fin.elim0 index
      | one =>
          unfold lowerPositiveTerm
          simp [Rew.func]
          funext index
          exact Fin.elim0 index
      | add =>
          unfold lowerPositiveTerm
          simp only [Rew.func]
          congr 1
          funext index
          cases index using Fin.cases with
          | zero => exact inductionHypothesis 0 _
          | succ index =>
              cases index using Fin.cases with
              | zero => exact inductionHypothesis 1 _
              | succ index => exact Fin.elim0 index
      | mul =>
          unfold lowerPositiveTerm
          simp only [Rew.func]
          congr 1
          funext index
          cases index using Fin.cases with
          | zero => exact inductionHypothesis 0 _
          | succ index =>
              cases index using Fin.cases with
              | zero => exact inductionHypothesis 1 _
              | succ index => exact Fin.elim0 index

theorem formulaValue_free
    (head : Nat) (tail : Nat -> Nat)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    formulaValue (extendValuation head tail) (Rewriting.free formula) <->
      LO.FirstOrder.Semiformula.Eval ![head] tail formula := by
  rw [show formulaValue (extendValuation head tail)
      (Rewriting.free formula) <->
      LO.FirstOrder.Semiformula.Eval
        (fun _ : Fin 1 => head) tail formula by
    simp [formulaValue, LO.FirstOrder.Semiformula.eval_rew,
      extendValuation, Function.comp_def]]
  have hboundEnvironment : (fun _ : Fin 1 => head) = ![head] := by
    funext index
    have hzero : index = (0 : Fin 1) := Fin.eq_zero index
    subst index
    rfl
  rw [hboundEnvironment]

theorem termValue_bShift
    (head : Nat) (tail : Nat -> Nat)
    (term : ValuationTerm) :
    LO.FirstOrder.Semiterm.val ![head] tail (Rew.bShift term) =
      termValue tail term := by
  induction term with
  | bvar index => exact Fin.elim0 index
  | fvar index => rfl
  | @func arity functionSymbol args inductionHypothesis =>
      cases functionSymbol with
      | zero => rfl
      | one => rfl
      | add =>
          change LO.FirstOrder.Semiterm.val ![head] tail
              (Rew.bShift (args 0)) +
              LO.FirstOrder.Semiterm.val ![head] tail
              (Rew.bShift (args 1)) = _
          rw [inductionHypothesis 0, inductionHypothesis 1]
          exact termValue_add tail args
      | mul =>
          change LO.FirstOrder.Semiterm.val ![head] tail
              (Rew.bShift (args 0)) *
              LO.FirstOrder.Semiterm.val ![head] tail
              (Rew.bShift (args 1)) = _
          rw [inductionHypothesis 0, inductionHypothesis 1]
          exact termValue_mul tail args

theorem formulaValue_shortBinarySubstitution
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : Nat) :
    formulaValue valuation (body/[shortBinaryNumeralTerm witness]) <->
      LO.FirstOrder.Semiformula.Eval ![witness] valuation body := by
  rw [show formulaValue valuation
      (body/[shortBinaryNumeralTerm witness]) <->
      LO.FirstOrder.Semiformula.Eval
        (fun _ : Fin 1 =>
          LO.FirstOrder.Semiterm.val ![] valuation
            (shortBinaryNumeralTerm witness)) valuation body by
    simp [formulaValue, LO.FirstOrder.Semiformula.eval_rew,
      Function.comp_def]]
  have hboundEnvironment : (fun _ : Fin 1 =>
      LO.FirstOrder.Semiterm.val ![] valuation
        (shortBinaryNumeralTerm witness)) = ![witness] := by
    funext index
    have hzero : index = (0 : Fin 1) := Fin.eq_zero index
    subst index
    exact termValue_shortBinaryNumeralTerm valuation witness
  rw [hboundEnvironment]

theorem termBoundedUniversal_eq_ball
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (∀⁰ termBoundedUniversalBody boundTerm body) =
      (∀⁰[“x. x < !!boundTerm”] body) := by
  unfold termBoundedUniversalBody termBoundFormula
  rw [finiteCaseLessThanFormula_eq_operator]
  rfl

theorem ball_body_truth
    (valuation : Nat -> Nat)
    (boundSource : ValuationTerm)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (htruth : formulaValue valuation
      (∀⁰[“x. x < !!(Rew.bShift boundSource)”] body))
    (index : Nat)
    (hindex : index < termValue valuation boundSource) :
    formulaValue (extendValuation index valuation)
      (Rewriting.free body) := by
  rw [formulaValue_free]
  have hall : ∀ value : Nat,
      LO.FirstOrder.Semiformula.Eval ![value] valuation
        (“#0 < !!(Rew.bShift boundSource)” :
          LO.FirstOrder.ArithmeticSemiformula Nat 1) ->
      LO.FirstOrder.Semiformula.Eval ![value] valuation body := by
    simpa [formulaValue] using htruth
  apply hall index
  change index < LO.FirstOrder.Semiterm.val ![index] valuation
    (Rew.bShift boundSource)
  rw [termValue_bShift]
  exact hindex

noncomputable def compileShiftedBoundEquality
    (valuation : Nat -> Nat)
    (outerVariables : Finset Nat)
    (boundSource : ValuationTerm)
    (hvariables : boundSource.freeVariables ⊆ outerVariables) :
    CertifiedPAContextProof
      ((valuationContext outerVariables valuation).image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0
          (termValue valuation boundSource)) =
        !!(Rew.shift boundSource)” : ValuationFormula) := by
  let shiftedValuation := extendValuation 0 valuation
  let localContext := valuationContext
    (Rew.shift boundSource).freeVariables shiftedValuation
  let termRaw := compileTermValueEquality
    shiftedValuation (Rew.shift boundSource)
  have hvalue := termValue_shift 0 valuation boundSource
  let termProof : CertifiedPAContextProof localContext
      (“!!(shortBinaryNumeralTerm (termValue valuation boundSource)) =
        !!(Rew.shift boundSource)” : ValuationFormula) := by
    have hformula :
        (“!!(shortBinaryNumeralTerm
            (termValue shiftedValuation (Rew.shift boundSource))) =
          !!(Rew.shift boundSource)” : ValuationFormula) =
        (“!!(shortBinaryNumeralTerm (termValue valuation boundSource)) =
          !!(Rew.shift boundSource)” : ValuationFormula) := by
      rw [hvalue]
    exact CertifiedPAContextProof.cast hformula termRaw
  let bridge := proveShortBinaryNumeralEqualsIterated
    (termValue valuation boundSource)
  let contextualBridge := CertifiedPAContextProof.weakenCertified
    localContext bridge
  let bridgeBackward := CertifiedPAContextProof.equalitySymmetry
    (shortBinaryNumeralTerm (termValue valuation boundSource))
    (iteratedSuccessorTerm 0 (termValue valuation boundSource))
    contextualBridge
  let localEquality := contextualEqualityTransitivity
    (iteratedSuccessorTerm 0 (termValue valuation boundSource))
    (shortBinaryNumeralTerm (termValue valuation boundSource))
    (Rew.shift boundSource) bridgeBackward termProof
  exact CertifiedPAContextProof.weakenContext localEquality
    (shiftedTermValuationContext_subset
      0 valuation boundSource outerVariables hvariables)

mutual

  inductive CheckedValuationBoundedFormulaCertificate :
      (valuation : Nat -> Nat) -> ValuationFormula -> Type
    | verum (valuation : Nat -> Nat) :
        CheckedValuationBoundedFormulaCertificate valuation
          (⊤ : ValuationFormula)
    | positiveAtomic
        (valuation : Nat -> Nat)
        (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
        (args : Fin 2 -> ValuationTerm)
        (htruth : formulaValue valuation
          (LO.FirstOrder.Semiformula.rel relationSymbol args)) :
        CheckedValuationBoundedFormulaCertificate valuation
          (LO.FirstOrder.Semiformula.rel relationSymbol args)
    | negativeAtomic
        (valuation : Nat -> Nat)
        (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
        (args : Fin 2 -> ValuationTerm)
        (htruth : formulaValue valuation
          (LO.FirstOrder.Semiformula.nrel relationSymbol args)) :
        CheckedValuationBoundedFormulaCertificate valuation
          (LO.FirstOrder.Semiformula.nrel relationSymbol args)
    | conjunction
        {valuation : Nat -> Nat}
        {left right : ValuationFormula}
        (leftCertificate :
          CheckedValuationBoundedFormulaCertificate valuation left)
        (rightCertificate :
          CheckedValuationBoundedFormulaCertificate valuation right) :
        CheckedValuationBoundedFormulaCertificate valuation (left ⋏ right)
    | disjunctionLeft
        {valuation : Nat -> Nat}
        {left right : ValuationFormula}
        (leftCertificate :
          CheckedValuationBoundedFormulaCertificate valuation left) :
        CheckedValuationBoundedFormulaCertificate valuation (left ⋎ right)
    | disjunctionRight
        {valuation : Nat -> Nat}
        {left right : ValuationFormula}
        (rightCertificate :
          CheckedValuationBoundedFormulaCertificate valuation right) :
        CheckedValuationBoundedFormulaCertificate valuation (left ⋎ right)
    | existsWitness
        {valuation : Nat -> Nat}
        (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
        (witness : Nat)
        (bodyCertificate : CheckedValuationBoundedFormulaCertificate
          valuation (body/[shortBinaryNumeralTerm witness])) :
        CheckedValuationBoundedFormulaCertificate valuation (∃⁰ body)
    | boundedUniversal
        {valuation : Nat -> Nat}
        (boundSource : ValuationTerm)
        (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
        (branches : CheckedValuationUniversalBranches valuation body
          (termValue valuation boundSource)) :
        CheckedValuationBoundedFormulaCertificate valuation
          (∀⁰ termBoundedUniversalBody
            (Rew.bShift boundSource) body)
    | cast
        {valuation : Nat -> Nat}
        {source target : ValuationFormula}
        (formulaEq : source = target)
        (sourceCertificate :
          CheckedValuationBoundedFormulaCertificate valuation source) :
        CheckedValuationBoundedFormulaCertificate valuation target

  inductive CheckedValuationUniversalBranches :
      (valuation : Nat -> Nat) ->
      (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) ->
      Nat -> Type
    | nil (valuation : Nat -> Nat)
        (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
        CheckedValuationUniversalBranches valuation body 0
    | snoc {valuation : Nat -> Nat}
        {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
        {bound : Nat}
        (initial : CheckedValuationUniversalBranches
          valuation body bound)
        (last : CheckedValuationBoundedFormulaCertificate
          (extendValuation bound valuation) (Rewriting.free body)) :
        CheckedValuationUniversalBranches valuation body (bound + 1)

end

namespace CheckedValuationBoundedFormulaCertificate

theorem universalBranches_nonempty_of_each
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (bound : Nat)
    (hcertificate : ∀ index, index < bound ->
      Nonempty (CheckedValuationBoundedFormulaCertificate
        (extendValuation index valuation) (Rewriting.free body))) :
    Nonempty (CheckedValuationUniversalBranches valuation body bound) := by
  induction bound with
  | zero => exact ⟨.nil valuation body⟩
  | succ previousBound inductionHypothesis =>
      have hprefix : ∀ index, index < previousBound ->
          Nonempty (CheckedValuationBoundedFormulaCertificate
            (extendValuation index valuation) (Rewriting.free body)) := by
        intro index hindex
        exact hcertificate index
          (Nat.lt_trans hindex (Nat.lt_succ_self previousBound))
      rcases inductionHypothesis hprefix with ⟨initial⟩
      rcases hcertificate previousBound (Nat.lt_succ_self previousBound) with
        ⟨last⟩
      exact ⟨.snoc initial last⟩

mutual

  noncomputable def compile :
      {valuation : Nat -> Nat} -> {formula : ValuationFormula} ->
      CheckedValuationBoundedFormulaCertificate valuation formula ->
      CertifiedPAContextProof
        (valuationContext formula.freeVariables valuation) formula
    | _, _, .verum valuation =>
        CertifiedPAContextProof.weakenCertified _ CertifiedPAProof.verumProof
    | _, _, .positiveAtomic valuation relationSymbol args htruth =>
        compilePositiveRelation valuation relationSymbol args htruth
    | _, _, .negativeAtomic valuation relationSymbol args htruth =>
        compileNegativeRelation valuation relationSymbol args htruth
    | valuation, _, .conjunction (left := left) (right := right)
        leftCertificate rightCertificate => by
        let leftRaw := compile leftCertificate
        let rightRaw := compile rightCertificate
        have hleft : left.freeVariables ⊆
            (left ⋏ right).freeVariables := by
          simp
        have hright : right.freeVariables ⊆
            (left ⋏ right).freeVariables := by
          simp
        let leftProof := CertifiedPAContextProof.weakenContext leftRaw
          (valuationContext_mono valuation hleft)
        let rightProof := CertifiedPAContextProof.weakenContext rightRaw
          (valuationContext_mono valuation hright)
        exact CertifiedPAContextProof.conjunction leftProof rightProof
    | valuation, _, .disjunctionLeft (left := left) (right := right)
        leftCertificate => by
        let leftRaw := compile leftCertificate
        have hleft : left.freeVariables ⊆
            (left ⋎ right).freeVariables := by
          simp
        let leftProof := CertifiedPAContextProof.weakenContext leftRaw
          (valuationContext_mono valuation hleft)
        exact CertifiedPAContextProof.disjunctionLeft leftProof
    | valuation, _, .disjunctionRight (left := left) (right := right)
        rightCertificate => by
        let rightRaw := compile rightCertificate
        have hright : right.freeVariables ⊆
            (left ⋎ right).freeVariables := by
          simp
        let rightProof := CertifiedPAContextProof.weakenContext rightRaw
          (valuationContext_mono valuation hright)
        exact CertifiedPAContextProof.disjunctionRight rightProof
    | valuation, _, .existsWitness body witness bodyCertificate => by
        let bodyRaw := compile bodyCertificate
        have hvariables :
            (body/[shortBinaryNumeralTerm witness]).freeVariables ⊆
              (∃⁰ body).freeVariables :=
          (shortBinarySubstitution_freeVariables_subset body witness).trans
            (by simp)
        let bodyProof := CertifiedPAContextProof.weakenContext bodyRaw
          (valuationContext_mono valuation hvariables)
        exact CertifiedPAContextProof.existsIntro
          (shortBinaryNumeralTerm witness) bodyProof
    | valuation, _, .boundedUniversal boundSource body branches => by
        let outerFormula := ∀⁰ termBoundedUniversalBody
          (Rew.bShift boundSource) body
        let outerVariables := outerFormula.freeVariables
        have hboundVariables : boundSource.freeVariables ⊆ outerVariables :=
          boundSource_freeVariables_subset_universal boundSource body
        have hbodyVariables : body.freeVariables ⊆ outerVariables :=
          body_freeVariables_subset_universal boundSource body
        let boundRaw := compileShiftedBoundEquality
          valuation outerVariables boundSource hboundVariables
        let boundEquality : CertifiedPAContextProof
            ((valuationContext outerVariables valuation).image
              Rewriting.shift)
            (“!!(iteratedSuccessorTerm 0
                (termValue valuation boundSource)) =
              !!(Rew.free (Rew.bShift boundSource))” :
              ValuationFormula) := by
          have hfree := free_bShift_term boundSource
          have hformula :
              (“!!(iteratedSuccessorTerm 0
                    (termValue valuation boundSource)) =
                !!(Rew.shift boundSource)” : ValuationFormula) =
              (“!!(iteratedSuccessorTerm 0
                    (termValue valuation boundSource)) =
                !!(Rew.free (Rew.bShift boundSource))” :
                ValuationFormula) := by
            rw [hfree]
          exact CertifiedPAContextProof.cast hformula boundRaw
        let compiledBranches := compileBranches
          branches outerVariables hbodyVariables
        exact compileContextualTermBoundedUniversal
          (termValue valuation boundSource)
          (Rew.bShift boundSource) body boundEquality compiledBranches
    | _, _, .cast formulaEq sourceCertificate => by
        subst formulaEq
        exact compile sourceCertificate

  noncomputable def compileBranches
      {valuation : Nat -> Nat}
      {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
      {bound : Nat}
      (branches : CheckedValuationUniversalBranches valuation body bound)
      (outerVariables : Finset Nat)
      (hbodyVariables : body.freeVariables ⊆ outerVariables) :
      CertifiedContextFiniteUniversalBranches
        ((valuationContext outerVariables valuation).image Rewriting.shift)
        (Rewriting.free body) bound :=
    match branches with
    | .nil _ _ => .nil
    | .snoc initial last =>
        let initialCompiled := compileBranches initial
          outerVariables hbodyVariables
        let lastRaw := compile last
        let lastProof := CertifiedPAContextProof.weakenContext lastRaw
          (freedFormulaValuationContext_subset_branch
            _ _ body outerVariables hbodyVariables)
        .snoc initialCompiled lastProof

end

theorem compile_certificate_valid
    {valuation : Nat -> Nat}
    {formula : ValuationFormula}
    (certificate :
      CheckedValuationBoundedFormulaCertificate valuation formula) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        certificate.compile.derivation)
      certificate.compile.certificate :=
  certificate.compile.certificate_valid

theorem certificate_nonempty_of_sigmaZero_truth
    (formula : ValuationFormula)
    (hhierarchy : Hierarchy Polarity.sigma 0 formula)
    (valuation : Nat -> Nat)
    (htruth : formulaValue valuation formula) :
    Nonempty
      (CheckedValuationBoundedFormulaCertificate valuation formula) := by
  cases formula using LO.FirstOrder.Semiformula.cases' with
  | hverum =>
      exact ⟨.verum valuation⟩
  | hfalsum =>
      have himpossible : False := by
        simpa [formulaValue] using htruth
      exact False.elim himpossible
  | hrel relationSymbol args =>
      cases relationSymbol with
      | eq => exact ⟨.positiveAtomic valuation Language.Eq.eq args htruth⟩
      | lt => exact ⟨.positiveAtomic valuation
          Language.ORing.Rel.lt args htruth⟩
  | hnrel relationSymbol args =>
      cases relationSymbol with
      | eq => exact ⟨.negativeAtomic valuation Language.Eq.eq args htruth⟩
      | lt => exact ⟨.negativeAtomic valuation
          Language.ORing.Rel.lt args htruth⟩
  | hand left right =>
      have hchildren :
          Hierarchy Polarity.sigma 0 left ∧
            Hierarchy Polarity.sigma 0 right := by
        simpa using hhierarchy
      have hvalues : formulaValue valuation left ∧
          formulaValue valuation right := by
        simpa [formulaValue] using htruth
      rcases certificate_nonempty_of_sigmaZero_truth
        left hchildren.1 valuation hvalues.1 with ⟨leftCertificate⟩
      rcases certificate_nonempty_of_sigmaZero_truth
        right hchildren.2 valuation hvalues.2 with ⟨rightCertificate⟩
      exact ⟨.conjunction leftCertificate rightCertificate⟩
  | hor left right =>
      have hchildren :
          Hierarchy Polarity.sigma 0 left ∧
            Hierarchy Polarity.sigma 0 right := by
        simpa using hhierarchy
      have hvalue : formulaValue valuation left ∨
          formulaValue valuation right := by
        simpa [formulaValue] using htruth
      rcases hvalue with hleft | hright
      · rcases certificate_nonempty_of_sigmaZero_truth
          left hchildren.1 valuation hleft with ⟨leftCertificate⟩
        exact ⟨.disjunctionLeft leftCertificate⟩
      · rcases certificate_nonempty_of_sigmaZero_truth
          right hchildren.2 valuation hright with ⟨rightCertificate⟩
        exact ⟨.disjunctionRight rightCertificate⟩
  | hall quantifiedBody =>
      cases hhierarchy with
      | ball boundPositive bodyHierarchy =>
          rename_i boundedBody boundTerm
          let boundSource := lowerPositiveTerm boundTerm boundPositive
          have hboundTerm := bShift_lowerPositiveTerm boundTerm boundPositive
          have hsourceTruth : formulaValue valuation
              (∀⁰[“x. x < !!(Rew.bShift boundSource)”]
                boundedBody) := by
            rw [hboundTerm]
            exact htruth
          let bound := termValue valuation boundSource
          have hbranchTruth : ∀ index, index < bound ->
              formulaValue (extendValuation index valuation)
                (Rewriting.free boundedBody) := by
            intro index hindex
            exact ball_body_truth valuation boundSource boundedBody
              hsourceTruth index hindex
          have hfreeHierarchy : Hierarchy Polarity.sigma 0
              (Rewriting.free boundedBody) :=
            bodyHierarchy.rew Rew.free
          have hbranchCertificates : ∀ index, index < bound ->
              Nonempty (CheckedValuationBoundedFormulaCertificate
                (extendValuation index valuation)
                (Rewriting.free boundedBody)) := by
            intro index hindex
            exact certificate_nonempty_of_sigmaZero_truth
              (Rewriting.free boundedBody) hfreeHierarchy
              (extendValuation index valuation)
              (hbranchTruth index hindex)
          rcases universalBranches_nonempty_of_each bound
            hbranchCertificates with ⟨branches⟩
          let sourceCertificate :=
            CheckedValuationBoundedFormulaCertificate.boundedUniversal
              boundSource boundedBody branches
          have hformula :
              (∀⁰ termBoundedUniversalBody
                (Rew.bShift boundSource) boundedBody) =
              (∀⁰[“x. x < !!boundTerm”] boundedBody) := by
            rw [termBoundedUniversal_eq_ball]
            rw [hboundTerm]
          exact ⟨.cast hformula sourceCertificate⟩
  | hexs quantifiedBody =>
      cases hhierarchy with
      | bexs boundPositive bodyHierarchy =>
          rename_i boundedBody boundTerm
          let boundedMatrix :
              LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
            (“#0 < !!boundTerm” ⋏ boundedBody)
          have hquantifiedHierarchy :
              Hierarchy Polarity.sigma 0 boundedMatrix := by
            have hguardHierarchy : Hierarchy Polarity.sigma 0
                (“#0 < !!boundTerm” :
                  LO.FirstOrder.ArithmeticSemiformula Nat 1) := by
              simp
            exact Hierarchy.and hguardHierarchy bodyHierarchy
          have hexists : ∃ witness : Nat,
              LO.FirstOrder.Semiformula.Eval ![witness] valuation
                boundedMatrix := by
            simpa [formulaValue, boundedMatrix] using htruth
          rcases hexists with ⟨witness, hwitness⟩
          have hsubstitutionHierarchy : Hierarchy Polarity.sigma 0
              (boundedMatrix/[shortBinaryNumeralTerm witness]) :=
            hquantifiedHierarchy.rew
              (Rew.subst ![shortBinaryNumeralTerm witness])
          have hsubstitutionTruth : formulaValue valuation
              (boundedMatrix/[shortBinaryNumeralTerm witness]) :=
            (formulaValue_shortBinarySubstitution
              valuation boundedMatrix witness).mpr hwitness
          rcases certificate_nonempty_of_sigmaZero_truth
            (boundedMatrix/[shortBinaryNumeralTerm witness])
            hsubstitutionHierarchy valuation hsubstitutionTruth with
              ⟨bodyCertificate⟩
          simpa [boundedMatrix] using
            (show Nonempty
                (CheckedValuationBoundedFormulaCertificate valuation
                  (∃⁰ boundedMatrix)) from
              ⟨.existsWitness boundedMatrix witness bodyCertificate⟩)
termination_by formula.complexity
decreasing_by
  all_goals
    subst_vars
    simp_all [LO.FirstOrder.ball, LO.FirstOrder.bexs,
      LO.FirstOrder.Semiformula.imp_eq,
      LO.FirstOrder.Semiformula.Operator.operator,
      LO.FirstOrder.Semiformula.Operator.LT.sentence_eq]

noncomputable def ofSigmaZeroTruth
    (formula : ValuationFormula)
    (hhierarchy : Hierarchy Polarity.sigma 0 formula)
    (valuation : Nat -> Nat)
    (htruth : formulaValue valuation formula) :
    CheckedValuationBoundedFormulaCertificate valuation formula :=
  Classical.choice
    (certificate_nonempty_of_sigmaZero_truth
      formula hhierarchy valuation htruth)

noncomputable def compileSigmaZeroTruth
    (formula : ValuationFormula)
    (hhierarchy : Hierarchy Polarity.sigma 0 formula)
    (valuation : Nat -> Nat)
    (htruth : formulaValue valuation formula) :
    CertifiedPAContextProof
      (valuationContext formula.freeVariables valuation) formula :=
  (ofSigmaZeroTruth formula hhierarchy valuation htruth).compile

#print axioms compile
#print axioms compile_certificate_valid
#print axioms certificate_nonempty_of_sigmaZero_truth
#print axioms compileSigmaZeroTruth

end CheckedValuationBoundedFormulaCertificate

end FoundationCompactPAValuationBoundedFormulaCompiler
