import integration.FoundationCompactNumericListedDirectArithmeticPrimitives
import integration.FoundationCompactNumericListedDirectTokenStreamTableau
import integration.FoundationCompactPABinaryLengthValuationContextCompiler
import integration.FoundationCompactPABitMembershipValuationContextCompiler
import integration.FoundationCompactPAValuationBoundedFormulaCompiler
import integration.FoundationCompactPAFastArithmeticLeafRecognizer
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Closed proof compiler for one compact fixed-width entry

The compiler keeps the two large arithmetic leaves out of the generic
bounded-formula expansion.  Binary length and bit membership are discharged
by their dedicated valuation compilers; the bitwise comparison is assembled
as a genuine finite contextual universal.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFixedWidthEntryHybridCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPABinaryLengthRuleCompiler
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler.CheckedValuationBoundedFormulaCertificate
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFastArithmeticLeafRecognizer
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

def compactFixedWidthEntryClosedFormula
    (table width index value : Nat) : ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
    ![shortBinaryNumeralTerm table, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm index, shortBinaryNumeralTerm value]

private def zeroValuation : Nat -> Nat := fun _ => 0

private def fixedWidthIndexWidthTerm
    (width index : Nat) : ValuationTerm :=
  paMulTerm (shortBinaryNumeralTerm index)
    (shortBinaryNumeralTerm width)

private def fixedWidthLeftBitIndexTerm
    (width index : Nat) : ValuationTerm :=
  paAddTerm (Rew.shift (fixedWidthIndexWidthTerm width index)) (&0)

private def fixedWidthLeftBitValueTerm (table : Nat) : ValuationTerm :=
  Rew.shift (shortBinaryNumeralTerm table)

private def fixedWidthRightBitIndexTerm : ValuationTerm := &0

private def fixedWidthRightBitValueTerm (value : Nat) : ValuationTerm :=
  Rew.shift (shortBinaryNumeralTerm value)

private def fixedWidthBitBody
    (table width index value : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  binaryBitAtomAtTerms
      (.func .add ![
        Rew.bShift (fixedWidthIndexWidthTerm width index), #0])
      (Rew.bShift (shortBinaryNumeralTerm table)) 🡘
    binaryBitAtomAtTerms #0
      (Rew.bShift (shortBinaryNumeralTerm value))

private def fixedWidthUniversalFormula
    (table width index value : Nat) : ArithmeticProposition :=
  (fixedWidthBitBody table width index value).ballLT
    (shortBinaryNumeralTerm width)

private def fixedWidthWitnessGuard
    (value : Nat) : ArithmeticProposition :=
  “!!(shortBinaryNumeralTerm (Nat.size value)) <
    !!(shortBinaryNumeralTerm value) + 1”

private def fixedWidthSizeGuard
    (width value : Nat) : ArithmeticProposition :=
  “!!(shortBinaryNumeralTerm (Nat.size value)) ≤
    !!(shortBinaryNumeralTerm width)”

private def fixedWidthLengthFormula
    (value : Nat) : ArithmeticProposition :=
  binaryLengthAtValuationFormula
    (shortBinaryNumeralTerm (Nat.size value))
    (shortBinaryNumeralTerm value)

private def fixedWidthPostWitnessFormula
    (table width index value : Nat) : ArithmeticProposition :=
  fixedWidthWitnessGuard value ⋏
    (fixedWidthLengthFormula value ⋏
      (fixedWidthSizeGuard width value ⋏
        fixedWidthUniversalFormula table width index value))

private def liftClosedFormula
    (formula : ArithmeticProposition) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  Rew.bShift ▹ formula

private def fixedWidthWitnessGuardBody
    (value : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm value)) + 1”

private def fixedWidthLengthBody
    (value : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!lengthDef #0
    !!(Rew.bShift (shortBinaryNumeralTerm value))”

private def fixedWidthSizeGuardBody
    (width : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 ≤ !!(Rew.bShift (shortBinaryNumeralTerm width))”

private def fixedWidthExistentialBody
    (table width index value : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  fixedWidthWitnessGuardBody value ⋏
    (fixedWidthLengthBody value ⋏
      (fixedWidthSizeGuardBody width ⋏
        liftClosedFormula
          (fixedWidthUniversalFormula table width index value)))

private theorem shiftedTerm_freeVariables_eq_empty
    (term : ValuationTerm)
    (hclosed : term.freeVariables = ∅) :
    (Rew.shift term).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro candidate hcandidate
  rcases mem_freeVariables_shiftTerm term hcandidate with
    ⟨sourceIndex, hsource, _⟩
  have hsourceEmpty : sourceIndex ∈ (∅ : Finset Nat) := by
    rw [← hclosed]
    exact hsource
  simpa using hsourceEmpty

private theorem binaryFunction_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    {boundArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    (LO.FirstOrder.Semiterm.func functionSymbol
        ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero =>
        exact Finset.mem_union_left right.freeVariables hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            exact Finset.mem_union_right left.freeVariables hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr
        ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr
        ⟨1, Finset.mem_univ 1, hright⟩

private theorem rewrite_binaryFunctionTerm
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right :
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting
        (LO.FirstOrder.Semiterm.func functionSymbol ![left, right]) =
      LO.FirstOrder.Semiterm.func functionSymbol
        ![rewriting left, rewriting right] := by
  rw [Rew.func]
  congr 1
  funext coordinate
  cases coordinate using Fin.cases with
  | zero => rfl
  | succ coordinate =>
      cases coordinate using Fin.cases with
      | zero => rfl
      | succ coordinate => exact Fin.elim0 coordinate

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Mul.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticOneTerm_eq_func
    {Variable : Type*} {boundArity : Nat} :
    (‘1’ : LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.One.one ![] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    Rew.func]

private theorem arithmeticAddTerm_freeVariables
    {boundArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    (‘!!left + !!right’ :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func]
  exact binaryFunction_freeVariables Language.Add.add left right

private theorem arithmeticOneTerm_freeVariables_eq_empty
    {boundArity : Nat} :
    (‘1’ :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity).freeVariables =
        ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    LO.FirstOrder.Semiterm.freeVariables_func]

private theorem lessEqualFormula_freeVariables
    {boundArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    (“!!left ≤ !!right” :
      LO.FirstOrder.ArithmeticSemiformula Nat boundArity).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  rw [LO.FirstOrder.Semiformula.Operator.le_def]
  ext candidate
  simp [LO.FirstOrder.Semiformula.freeVariables_rel]

private theorem paAddTerm_freeVariables
    (left right : ValuationTerm) :
    (paAddTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseAddTerm_eq_paAddTerm]
  exact binaryFunction_freeVariables Language.Add.add left right

private theorem paMulTerm_freeVariables
    (left right : ValuationTerm) :
    (paMulTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  exact binaryFunction_freeVariables Language.Mul.mul left right

private theorem termValue_paAddTerm
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (paAddTerm left right) =
      termValue valuation left + termValue valuation right := by
  rw [← finiteCaseAddTerm_eq_paAddTerm]
  change
    termValue valuation
        (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]) =
      termValue valuation left + termValue valuation right
  exact termValue_add valuation ![left, right]

private theorem termValue_paMulTerm
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (paMulTerm left right) =
      termValue valuation left * termValue valuation right := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  change
    termValue valuation
        (LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right]) =
      termValue valuation left * termValue valuation right
  exact termValue_mul valuation ![left, right]

private theorem termValue_fixedWidthIndexWidthTerm
    (valuation : Nat -> Nat) (width index : Nat) :
    termValue valuation (fixedWidthIndexWidthTerm width index) =
      index * width := by
  rw [fixedWidthIndexWidthTerm, termValue_paMulTerm,
    termValue_shortBinaryNumeralTerm,
    termValue_shortBinaryNumeralTerm]

private theorem termValue_fixedWidthLeftBitIndexTerm
    (width index bitIndex : Nat) :
    termValue (extendValuation bitIndex zeroValuation)
        (fixedWidthLeftBitIndexTerm width index) =
      index * width + bitIndex := by
  rw [fixedWidthLeftBitIndexTerm, termValue_paAddTerm,
    termValue_shift, termValue_fixedWidthIndexWidthTerm]
  rfl

private theorem termValue_fixedWidthLeftBitValueTerm
    (table bitIndex : Nat) :
    termValue (extendValuation bitIndex zeroValuation)
        (fixedWidthLeftBitValueTerm table) = table := by
  rw [fixedWidthLeftBitValueTerm, termValue_shift,
    termValue_shortBinaryNumeralTerm]

private theorem termValue_fixedWidthRightBitIndexTerm
    (bitIndex : Nat) :
    termValue (extendValuation bitIndex zeroValuation)
        fixedWidthRightBitIndexTerm = bitIndex := by
  rfl

private theorem termValue_fixedWidthRightBitValueTerm
    (value bitIndex : Nat) :
    termValue (extendValuation bitIndex zeroValuation)
        (fixedWidthRightBitValueTerm value) = value := by
  rw [fixedWidthRightBitValueTerm, termValue_shift,
    termValue_shortBinaryNumeralTerm]

private theorem fixedWidthIndexWidthTerm_freeVariables_eq_empty
    (width index : Nat) :
    (fixedWidthIndexWidthTerm width index).freeVariables = ∅ := by
  rw [fixedWidthIndexWidthTerm, paMulTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  exact Finset.empty_union ∅

private theorem fixedWidthLeftBitIndexTerm_freeVariables
    (width index : Nat) :
    (fixedWidthLeftBitIndexTerm width index).freeVariables = {0} := by
  have hshift := shiftedTerm_freeVariables_eq_empty
    (fixedWidthIndexWidthTerm width index)
    (fixedWidthIndexWidthTerm_freeVariables_eq_empty width index)
  rw [fixedWidthLeftBitIndexTerm, paAddTerm_freeVariables, hshift]
  exact Finset.empty_union {0}

private theorem fixedWidthLeftBitValueTerm_freeVariables_eq_empty
    (table : Nat) :
    (fixedWidthLeftBitValueTerm table).freeVariables = ∅ := by
  exact shiftedTerm_freeVariables_eq_empty
    (shortBinaryNumeralTerm table)
    (shortBinaryNumeralTerm_freeVariables_eq_empty table)

private theorem fixedWidthRightBitValueTerm_freeVariables_eq_empty
    (value : Nat) :
    (fixedWidthRightBitValueTerm value).freeVariables = ∅ := by
  exact shiftedTerm_freeVariables_eq_empty
    (shortBinaryNumeralTerm value)
    (shortBinaryNumeralTerm_freeVariables_eq_empty value)

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula :
      LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹
        ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹
        ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app,
        TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_emb_empty
    {boundArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty boundArity) :
    (Rewriting.emb (ξ := Empty) formula) = formula := by
  change
    (Rew.emb : Rew ℒₒᵣ Empty boundArity Empty boundArity) ▹
        formula = formula
  rw [Rew.emb_eq_id]
  exact ReflectiveRewriting.id_app formula

private theorem rewriting_formulaOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator :
      LO.FirstOrder.Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms =
      operator.operator (rewriting ∘ terms) := by
  unfold LO.FirstOrder.Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution
    rewriting operator.sentence terms

private theorem membershipOperator_eq_binaryBitAtomAtTerms
    {boundArity : Nat}
    (indexTerm valueTerm :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
        ![indexTerm, valueTerm] =
      binaryBitAtomAtTerms indexTerm valueTerm := by
  unfold binaryBitAtomAtTerms
  unfold LO.FirstOrder.Semiformula.Operator.operator
  rw [LO.FirstOrder.Arithmetic.operator_mem_def]

private theorem rewrite_membershipOperator
    {sourceVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      Nat targetArity)
    (indexTerm valueTerm :
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹
        LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
          ![indexTerm, valueTerm] =
      binaryBitAtomAtTerms (rewriting indexTerm)
        (rewriting valueTerm) := by
  have hterms :
      rewriting ∘ ![indexTerm, valueTerm] =
        ![rewriting indexTerm, rewriting valueTerm] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => rfl
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => rfl
        | succ coordinate => exact Fin.elim0 coordinate
  calc
    rewriting ▹
        LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
          ![indexTerm, valueTerm] =
        LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
          (rewriting ∘ ![indexTerm, valueTerm]) :=
      rewriting_formulaOperator rewriting
        LO.FirstOrder.Semiformula.Operator.Mem.mem
        ![indexTerm, valueTerm]
    _ = LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
          ![rewriting indexTerm, rewriting valueTerm] := by
      rw [hterms]
    _ = binaryBitAtomAtTerms (rewriting indexTerm)
          (rewriting valueTerm) :=
      membershipOperator_eq_binaryBitAtomAtTerms _ _

private theorem rewrite_binaryBitAtomAtTerms
    {sourceArity targetArity : Nat}
    (rewriting :
      Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    (indexTerm valueTerm :
      LO.FirstOrder.ArithmeticSemiterm Nat sourceArity) :
    rewriting ▹ binaryBitAtomAtTerms indexTerm valueTerm =
      binaryBitAtomAtTerms (rewriting indexTerm)
        (rewriting valueTerm) := by
  calc
    rewriting ▹ binaryBitAtomAtTerms indexTerm valueTerm =
        rewriting ▹
          LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
            ![indexTerm, valueTerm] := by
      rw [membershipOperator_eq_binaryBitAtomAtTerms]
    _ = binaryBitAtomAtTerms (rewriting indexTerm)
          (rewriting valueTerm) :=
      rewrite_membershipOperator rewriting indexTerm valueTerm

private theorem free_binaryBitAtomAtTerms
    (indexTerm valueTerm :
      LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    Rewriting.free (binaryBitAtomAtTerms indexTerm valueTerm) =
      binaryBitAtomAtTerms (Rew.free indexTerm)
        (Rew.free valueTerm) :=
  rewrite_binaryBitAtomAtTerms Rew.free indexTerm valueTerm

private theorem rewriting_iff
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (left right :
      LO.FirstOrder.ArithmeticSemiformula sourceVariables sourceArity) :
    rewriting ▹ (left 🡘 right) =
      ((rewriting ▹ left) 🡘 (rewriting ▹ right)) := by
  simp [LO.FirstOrder.Semiformula.iff_eq]

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : LO.FirstOrder.ArithmeticSemiformula sourceVariables
      (sourceArity + 1))
    (bound : LO.FirstOrder.ArithmeticSemiterm sourceVariables
      sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm sourceVariables
              (sourceArity + 1)),
            Rew.bShift bound] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm targetVariables
              (targetArity + 1)),
          Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero =>
        change rewriting.q (#0) = #0
        exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            change rewriting.q (Rew.bShift bound) =
              Rew.bShift (rewriting bound)
            exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold LO.FirstOrder.Semiformula.ballLT
  rw [Rewriting.smul_ball, rewriting_formulaOperator, hguardTerms]

private theorem free_fixedWidthBitBodyLeftIndex
    (width index : Nat) :
    Rew.free
        (.func .add ![
          Rew.bShift (fixedWidthIndexWidthTerm width index), #0] :
          LO.FirstOrder.ArithmeticSemiterm Nat 1) =
      fixedWidthLeftBitIndexTerm width index := by
  change
    Rew.free
        (LO.FirstOrder.Semiterm.func Language.Add.add ![
          Rew.bShift (fixedWidthIndexWidthTerm width index), #0]) =
      fixedWidthLeftBitIndexTerm width index
  calc
    Rew.free
        (LO.FirstOrder.Semiterm.func Language.Add.add ![
          Rew.bShift (fixedWidthIndexWidthTerm width index), #0] :
          LO.FirstOrder.ArithmeticSemiterm Nat 1) =
        finiteCaseAddTerm
          (Rew.free
            (Rew.bShift (fixedWidthIndexWidthTerm width index)))
          (Rew.free
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)) := by
      unfold finiteCaseAddTerm
      rw [Rew.func]
      congr 1
      funext coordinate
      cases coordinate using Fin.cases with
      | zero => rfl
      | succ coordinate =>
          cases coordinate using Fin.cases with
          | zero => rfl
          | succ coordinate => exact Fin.elim0 coordinate
    _ = finiteCaseAddTerm
          (Rew.shift (fixedWidthIndexWidthTerm width index)) (&0) := by
      rw [free_bShift_term]
      rfl
    _ = paAddTerm
          (Rew.shift (fixedWidthIndexWidthTerm width index)) (&0) :=
      finiteCaseAddTerm_eq_paAddTerm _ _
    _ = fixedWidthLeftBitIndexTerm width index := rfl

private theorem free_fixedWidthBitBodyLeftValue
    (table : Nat) :
    Rew.free (Rew.bShift (shortBinaryNumeralTerm table)) =
      fixedWidthLeftBitValueTerm table := by
  rw [free_bShift_term]
  rfl

private theorem free_fixedWidthBitBodyRightIndex :
    Rew.free (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) =
      fixedWidthRightBitIndexTerm := by
  rfl

private theorem free_fixedWidthBitBodyRightValue
    (value : Nat) :
    Rew.free (Rew.bShift (shortBinaryNumeralTerm value)) =
      fixedWidthRightBitValueTerm value := by
  rw [free_bShift_term]
  rfl

private theorem free_iff
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    Rewriting.free (left 🡘 right) =
      (Rewriting.free left 🡘 Rewriting.free right) := by
  simp [LO.FirstOrder.Semiformula.iff_eq]

private theorem fixedWidthBitBody_free
    (table width index value : Nat) :
    Rewriting.free (fixedWidthBitBody table width index value) =
      (binaryBitAtomAtTerms
          (fixedWidthLeftBitIndexTerm width index)
          (fixedWidthLeftBitValueTerm table) 🡘
        binaryBitAtomAtTerms fixedWidthRightBitIndexTerm
          (fixedWidthRightBitValueTerm value)) := by
  unfold fixedWidthBitBody
  rw [free_iff, free_binaryBitAtomAtTerms,
    free_binaryBitAtomAtTerms,
    free_fixedWidthBitBodyLeftIndex,
    free_fixedWidthBitBodyLeftValue,
    free_fixedWidthBitBodyRightIndex,
    free_fixedWidthBitBodyRightValue]

private theorem liftClosedFormula_subst
    (formula : ArithmeticProposition)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (liftClosedFormula formula)/[witness] = formula := by
  unfold liftClosedFormula
  calc
    Rew.subst ![witness] ▹ (Rew.bShift ▹ formula) =
        ((Rew.subst ![witness]).comp Rew.bShift) ▹ formula :=
      (TransitiveRewriting.comp_app _ _ _).symm
    _ = Rew.id ▹ formula := by
      rw [Rew.subst_comp_bShift_eq_id]
    _ = formula := ReflectiveRewriting.id_app formula

private theorem subst_bShiftTerm
    (term witness : ValuationTerm) :
    Rew.subst ![witness] (Rew.bShift term) = term := by
  calc
    Rew.subst ![witness] (Rew.bShift term) =
        ((Rew.subst ![witness]).comp Rew.bShift) term := by
      rw [Rew.comp_app]
    _ = Rew.id term := by
      rw [Rew.subst_comp_bShift_eq_id]
    _ = term := Rew.id_app term

private theorem subst_fixedWidthWitnessGuardBody
    (value : Nat) :
    (fixedWidthWitnessGuardBody value)/[
        shortBinaryNumeralTerm (Nat.size value)] =
      fixedWidthWitnessGuard value := by
  have hliftedValue :
      Rew.subst ![shortBinaryNumeralTerm (Nat.size value)]
          (Rew.bShift (shortBinaryNumeralTerm value)) =
        shortBinaryNumeralTerm value := by
    exact subst_bShiftTerm _ _
  simp [fixedWidthWitnessGuardBody, fixedWidthWitnessGuard,
    hliftedValue]

private theorem subst_fixedWidthSizeGuardBody
    (width value : Nat) :
    (fixedWidthSizeGuardBody width)/[
        shortBinaryNumeralTerm (Nat.size value)] =
      fixedWidthSizeGuard width value := by
  have hliftedWidth :
      Rew.subst ![shortBinaryNumeralTerm (Nat.size value)]
          (Rew.bShift (shortBinaryNumeralTerm width)) =
        shortBinaryNumeralTerm width := by
    exact subst_bShiftTerm _ _
  simp [fixedWidthSizeGuardBody, fixedWidthSizeGuard,
    LO.FirstOrder.Semiformula.Operator.le_def, hliftedWidth]

private theorem subst_fixedWidthLengthBody
    (value : Nat) :
    (fixedWidthLengthBody value)/[
        shortBinaryNumeralTerm (Nat.size value)] =
      fixedWidthLengthFormula value := by
  have hliftedValue :
      Rew.subst ![shortBinaryNumeralTerm (Nat.size value)]
          (Rew.bShift (shortBinaryNumeralTerm value)) =
        shortBinaryNumeralTerm value := by
    exact subst_bShiftTerm _ _
  have hwitness :
      Rew.subst ![shortBinaryNumeralTerm (Nat.size value)]
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) =
        shortBinaryNumeralTerm (Nat.size value) := by
    exact Rew.subst_bvar _ 0
  unfold fixedWidthLengthBody fixedWidthLengthFormula
  unfold binaryLengthAtValuationFormula
  calc
    Rewriting.app
          (Rew.subst ![shortBinaryNumeralTerm (Nat.size value)])
          ((Rewriting.emb lengthDef.val :
              LO.FirstOrder.ArithmeticSemiformula Nat 2)/[
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
            Rew.bShift (shortBinaryNumeralTerm value)]) =
        (Rewriting.emb lengthDef.val :
            LO.FirstOrder.ArithmeticSemiformula Nat 2)/[
          Rew.subst ![shortBinaryNumeralTerm (Nat.size value)]
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          Rew.subst ![shortBinaryNumeralTerm (Nat.size value)]
            (Rew.bShift (shortBinaryNumeralTerm value))] :=
      subst_lengthDef_instance _ _ _
    _ = (Rewriting.emb lengthDef.val :
            LO.FirstOrder.ArithmeticSemiformula Nat 2)/[
          shortBinaryNumeralTerm (Nat.size value),
          shortBinaryNumeralTerm value] := by
      rw [hwitness, hliftedValue]

private theorem fixedWidthExistentialBody_subst
    (table width index value : Nat) :
    (fixedWidthExistentialBody table width index value)/[
        shortBinaryNumeralTerm (Nat.size value)] =
      fixedWidthPostWitnessFormula table width index value := by
  unfold fixedWidthExistentialBody fixedWidthPostWitnessFormula
  simp only [LogicalConnective.HomClass.map_and]
  change
    (fixedWidthWitnessGuardBody value)/[
          shortBinaryNumeralTerm (Nat.size value)] ⋏
        ((fixedWidthLengthBody value)/[
            shortBinaryNumeralTerm (Nat.size value)] ⋏
          ((fixedWidthSizeGuardBody width)/[
              shortBinaryNumeralTerm (Nat.size value)] ⋏
            (liftClosedFormula
                (fixedWidthUniversalFormula table width index value))/[
              shortBinaryNumeralTerm (Nat.size value)])) =
      fixedWidthWitnessGuard value ⋏
        (fixedWidthLengthFormula value ⋏
          (fixedWidthSizeGuard width value ⋏
            fixedWidthUniversalFormula table width index value))
  rw [subst_fixedWidthWitnessGuardBody,
    subst_fixedWidthLengthBody,
    subst_fixedWidthSizeGuardBody,
    liftClosedFormula_subst]

private def fixedWidthSourceWitnessGuardBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “#0 < #4 + 1”

private def fixedWidthSourceLengthBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “!lengthDef #0 #4”

private def fixedWidthSourceSizeGuardBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “#0 ≤ #2”

private def fixedWidthSourceLeftBitIndexTerm :
    LO.FirstOrder.ArithmeticSemiterm Empty 6 :=
  ‘#4 * #3 + #0’

private def fixedWidthSourceBitBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 6 :=
  (LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
      ![fixedWidthSourceLeftBitIndexTerm,
        (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 6)]) 🡘
    LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
      ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 6), #5]

private def fixedWidthSourceUniversalBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  fixedWidthSourceBitBody.ballLT
    (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 5)

private def fixedWidthSourceExistentialBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  fixedWidthSourceWitnessGuardBody ⋏
    (fixedWidthSourceLengthBody ⋏
      (fixedWidthSourceSizeGuardBody ⋏
        fixedWidthSourceUniversalBody))

private theorem bShift_fixedWidthSourceWitnessBound :
    Rew.bShift
        (‘#3 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 4) =
      (‘#4 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 5) := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem compactFixedWidthEntryDef_val_eq_sourceExists :
    compactFixedWidthEntryDef.val =
      ∃⁰ fixedWidthSourceExistentialBody := by
  unfold compactFixedWidthEntryDef compactNatSizeDef
  change
    (fixedWidthSourceLengthBody ⋏
        (fixedWidthSourceSizeGuardBody ⋏
          fixedWidthSourceUniversalBody)).bexsLTSucc
        (#3 : LO.FirstOrder.ArithmeticSemiterm Empty 4) =
      ∃⁰ fixedWidthSourceExistentialBody
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
  unfold LO.FirstOrder.Semiformula.bexsLT
  unfold fixedWidthSourceExistentialBody
  unfold fixedWidthSourceWitnessGuardBody
  rw [bShift_fixedWidthSourceWitnessBound]
  rfl

private def fixedWidthOuterTerms
    (table width index value : Nat) :
    Fin 4 -> ValuationTerm :=
  ![shortBinaryNumeralTerm table,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm index,
    shortBinaryNumeralTerm value]

private def fixedWidthBodyTerms
    (table width index value : Nat) :
    Fin 5 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
    Rew.bShift (shortBinaryNumeralTerm table),
    Rew.bShift (shortBinaryNumeralTerm width),
    Rew.bShift (shortBinaryNumeralTerm index),
    Rew.bShift (shortBinaryNumeralTerm value)]

private theorem fixedWidthBodyRewriting_eq_embSubsts
    (table width index value : Nat) :
    (Rew.subst (fixedWidthOuterTerms table width index value)).q.comp
        (Rew.emb : Rew ℒₒᵣ Empty 5 Nat 5) =
      Rew.embSubsts (fixedWidthBodyTerms table width index value) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar]
        change
          (Rew.subst
            (fixedWidthOuterTerms table width index value)).q (#0) = #0
        exact Rew.q_bvar_zero _
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar]
            change
              (Rew.subst
                  (fixedWidthOuterTerms table width index value)).q
                  (#((0 : Fin 4).succ)) =
                Rew.bShift (shortBinaryNumeralTerm table)
            rw [Rew.q_bvar_succ, Rew.subst_bvar]
            rfl
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero =>
                rw [Rew.comp_app, Rew.emb_bvar,
                  Rew.embSubsts_bvar]
                change
                  (Rew.subst
                      (fixedWidthOuterTerms table width index value)).q
                      (#((1 : Fin 4).succ)) =
                    Rew.bShift (shortBinaryNumeralTerm width)
                rw [Rew.q_bvar_succ, Rew.subst_bvar]
                rfl
            | succ coordinate =>
                cases coordinate using Fin.cases with
                | zero =>
                    rw [Rew.comp_app, Rew.emb_bvar,
                      Rew.embSubsts_bvar]
                    change
                      (Rew.subst
                          (fixedWidthOuterTerms table width index value)).q
                          (#((2 : Fin 4).succ)) =
                        Rew.bShift (shortBinaryNumeralTerm index)
                    rw [Rew.q_bvar_succ, Rew.subst_bvar]
                    rfl
                | succ coordinate =>
                    cases coordinate using Fin.cases with
                    | zero =>
                        rw [Rew.comp_app, Rew.emb_bvar,
                          Rew.embSubsts_bvar]
                        change
                          (Rew.subst
                              (fixedWidthOuterTerms table width index
                                value)).q
                              (#((3 : Fin 4).succ)) =
                            Rew.bShift (shortBinaryNumeralTerm value)
                        rw [Rew.q_bvar_succ, Rew.subst_bvar]
                        rfl
                    | succ coordinate => exact Fin.elim0 coordinate
  · exact Empty.elim coordinate

private theorem fixedWidthIndexWidthTerm_eq_func
    (width index : Nat) :
    fixedWidthIndexWidthTerm width index =
      LO.FirstOrder.Semiterm.func Language.Mul.mul
        ![shortBinaryNumeralTerm index,
          shortBinaryNumeralTerm width] := by
  unfold fixedWidthIndexWidthTerm
  exact (finiteCaseMulTerm_eq_paMulTerm _ _).symm

private theorem fixedWidthBodyQ_bvarZero
    (table width index value : Nat) :
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#0 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
  rw [Rew.q_bvar_zero, Rew.q_bvar_zero]

private theorem fixedWidthBodyQ_table
    (table width index value : Nat) :
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm table)) := by
  change
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#((1 : Fin 5).succ)) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm table))
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar,
    Rew.q_comp_bShift_app]
  rfl

private theorem fixedWidthBodyQ_width
    (table width index value : Nat) :
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#3 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm width)) := by
  change
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#((2 : Fin 5).succ)) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm width))
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar,
    Rew.q_comp_bShift_app]
  rfl

private theorem fixedWidthBodyQ_index
    (table width index value : Nat) :
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#4 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm index)) := by
  change
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#((3 : Fin 5).succ)) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm index))
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar,
    Rew.q_comp_bShift_app]
  rfl

private theorem fixedWidthBodyQ_value
    (table width index value : Nat) :
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#5 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm value)) := by
  change
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#((4 : Fin 5).succ)) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm value))
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar,
    Rew.q_comp_bShift_app]
  rfl

private theorem fixedWidthSourceWitnessGuardBody_rewrite
    (table width index value : Nat) :
    Rew.embSubsts (fixedWidthBodyTerms table width index value) ▹
        fixedWidthSourceWitnessGuardBody =
      fixedWidthWitnessGuardBody value := by
  have hterms :
      Rew.embSubsts (fixedWidthBodyTerms table width index value) ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5),
            (‘#4 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 5)] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          (‘!!(Rew.bShift (shortBinaryNumeralTerm value)) + 1’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 1)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => simp [fixedWidthBodyTerms]
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            simp [fixedWidthBodyTerms,
              LO.FirstOrder.Semiterm.Operator.operator,
              LO.FirstOrder.Semiterm.Operator.numeral_one,
              LO.FirstOrder.Semiterm.Operator.Add.term_eq,
              LO.FirstOrder.Semiterm.Operator.One.term_eq,
              Rew.func, Matrix.fun_eq_vec_two]
        | succ coordinate => exact Fin.elim0 coordinate
  change
    Rew.embSubsts (fixedWidthBodyTerms table width index value) ▹
        LO.FirstOrder.Semiformula.Operator.LT.lt.operator
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5),
            (‘#4 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 5)] =
      LO.FirstOrder.Semiformula.Operator.LT.lt.operator
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          (‘!!(Rew.bShift (shortBinaryNumeralTerm value)) + 1’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 1)]
  rw [rewriting_formulaOperator, hterms]

private theorem fixedWidthSourceLengthBody_rewrite
    (table width index value : Nat) :
    Rew.embSubsts (fixedWidthBodyTerms table width index value) ▹
        fixedWidthSourceLengthBody =
      fixedWidthLengthBody value := by
  have hterms :
      Rew.embSubsts (fixedWidthBodyTerms table width index value) ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5),
            (#4 : LO.FirstOrder.ArithmeticSemiterm Empty 5)] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          Rew.bShift (shortBinaryNumeralTerm value)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => simp [fixedWidthBodyTerms]
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => simp [fixedWidthBodyTerms]
        | succ coordinate => exact Fin.elim0 coordinate
  have hsource :
      fixedWidthSourceLengthBody =
        (Rewriting.emb (ξ := Empty) lengthDef.val) ⇜
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5), #4] := by
    unfold fixedWidthSourceLengthBody
    rw [rewriting_emb_empty]
  have htarget :
      fixedWidthLengthBody value =
        (Rewriting.emb (ξ := Nat) lengthDef.val) ⇜
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
            Rew.bShift (shortBinaryNumeralTerm value)] := by
    unfold fixedWidthLengthBody
    rfl
  rw [hsource, htarget,
    rewriting_embeddedFormulaSubstitution, hterms]

private theorem fixedWidthSourceSizeGuardBody_rewrite
    (table width index value : Nat) :
    Rew.embSubsts (fixedWidthBodyTerms table width index value) ▹
        fixedWidthSourceSizeGuardBody =
      fixedWidthSizeGuardBody width := by
  have hterms :
      Rew.embSubsts (fixedWidthBodyTerms table width index value) ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5),
            (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 5)] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          Rew.bShift (shortBinaryNumeralTerm width)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => simp [fixedWidthBodyTerms]
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => simp [fixedWidthBodyTerms]
        | succ coordinate => exact Fin.elim0 coordinate
  change
    Rew.embSubsts (fixedWidthBodyTerms table width index value) ▹
        LO.FirstOrder.Semiformula.Operator.LE.le.operator
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5), #2] =
      LO.FirstOrder.Semiformula.Operator.LE.le.operator
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          Rew.bShift (shortBinaryNumeralTerm width)]
  rw [rewriting_formulaOperator, hterms]

private theorem fixedWidthSourceLeftBitIndexTerm_rewrite
    (table width index value : Nat) :
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        fixedWidthSourceLeftBitIndexTerm =
      Rew.bShift.q
        (.func .add ![
          Rew.bShift (fixedWidthIndexWidthTerm width index), #0] :
          LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
  unfold fixedWidthSourceLeftBitIndexTerm
  rw [arithmeticAddTerm_eq_func, arithmeticMulTerm_eq_func,
    fixedWidthIndexWidthTerm_eq_func]
  change
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (LO.FirstOrder.Semiterm.func Language.Add.add ![
          LO.FirstOrder.Semiterm.func Language.Mul.mul ![#4, #3], #0]) =
      Rew.bShift.q
        (LO.FirstOrder.Semiterm.func Language.Add.add ![
          Rew.bShift
            (LO.FirstOrder.Semiterm.func Language.Mul.mul ![
              shortBinaryNumeralTerm index,
              shortBinaryNumeralTerm width]),
          #0])
  have hmul :
      (Rew.embSubsts
          (fixedWidthBodyTerms table width index value)).q
          (LO.FirstOrder.Semiterm.func Language.Mul.mul ![#4, #3]) =
        Rew.bShift.q
          (Rew.bShift
            (LO.FirstOrder.Semiterm.func Language.Mul.mul ![
              shortBinaryNumeralTerm index,
              shortBinaryNumeralTerm width])) := by
    calc
      (Rew.embSubsts
          (fixedWidthBodyTerms table width index value)).q
          (LO.FirstOrder.Semiterm.func Language.Mul.mul ![#4, #3]) =
        LO.FirstOrder.Semiterm.func Language.Mul.mul ![
          (Rew.embSubsts
            (fixedWidthBodyTerms table width index value)).q #4,
          (Rew.embSubsts
            (fixedWidthBodyTerms table width index value)).q #3] :=
        rewrite_binaryFunctionTerm _ _ _ _
      _ = LO.FirstOrder.Semiterm.func Language.Mul.mul ![
            Rew.bShift.q
              (Rew.bShift (shortBinaryNumeralTerm index)),
            Rew.bShift.q
              (Rew.bShift (shortBinaryNumeralTerm width))] := by
        rw [fixedWidthBodyQ_index, fixedWidthBodyQ_width]
      _ = Rew.bShift.q
            (LO.FirstOrder.Semiterm.func Language.Mul.mul ![
              Rew.bShift (shortBinaryNumeralTerm index),
              Rew.bShift (shortBinaryNumeralTerm width)]) :=
        (rewrite_binaryFunctionTerm _ _ _ _).symm
      _ = Rew.bShift.q
            (Rew.bShift
              (LO.FirstOrder.Semiterm.func Language.Mul.mul ![
                shortBinaryNumeralTerm index,
                shortBinaryNumeralTerm width])) := by
        exact congrArg (fun term => Rew.bShift.q term)
          (rewrite_binaryFunctionTerm Rew.bShift Language.Mul.mul
            (shortBinaryNumeralTerm index)
            (shortBinaryNumeralTerm width)).symm
  calc
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (LO.FirstOrder.Semiterm.func Language.Add.add ![
          LO.FirstOrder.Semiterm.func Language.Mul.mul ![#4, #3], #0]) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![
        (Rew.embSubsts
          (fixedWidthBodyTerms table width index value)).q
          (LO.FirstOrder.Semiterm.func Language.Mul.mul ![#4, #3]),
        (Rew.embSubsts
          (fixedWidthBodyTerms table width index value)).q #0] :=
      rewrite_binaryFunctionTerm _ _ _ _
    _ = LO.FirstOrder.Semiterm.func Language.Add.add ![
          Rew.bShift.q
            (Rew.bShift
              (LO.FirstOrder.Semiterm.func Language.Mul.mul ![
                shortBinaryNumeralTerm index,
                shortBinaryNumeralTerm width])),
          Rew.bShift.q
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)] := by
      rw [hmul, fixedWidthBodyQ_bvarZero]
    _ = Rew.bShift.q
          (LO.FirstOrder.Semiterm.func Language.Add.add ![
            Rew.bShift
              (LO.FirstOrder.Semiterm.func Language.Mul.mul ![
                shortBinaryNumeralTerm index,
                shortBinaryNumeralTerm width]),
            #0]) :=
      (rewrite_binaryFunctionTerm _ _ _ _).symm

private theorem fixedWidthSourceLeftBitValueTerm_rewrite
    (table width index value : Nat) :
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm table)) := by
  exact fixedWidthBodyQ_table table width index value

private theorem fixedWidthSourceRightBitIndexTerm_rewrite
    (table width index value : Nat) :
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#0 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
  exact fixedWidthBodyQ_bvarZero table width index value

private theorem fixedWidthSourceRightBitValueTerm_rewrite
    (table width index value : Nat) :
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q
        (#5 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (Rew.bShift (shortBinaryNumeralTerm value)) := by
  exact fixedWidthBodyQ_value table width index value

private theorem fixedWidthSourceBitBody_rewrite
    (table width index value : Nat) :
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q ▹
        fixedWidthSourceBitBody =
      Rew.bShift.q ▹
        fixedWidthBitBody table width index value := by
  unfold fixedWidthSourceBitBody fixedWidthBitBody
  calc
    (Rew.embSubsts
        (fixedWidthBodyTerms table width index value)).q ▹
        (LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
            ![fixedWidthSourceLeftBitIndexTerm,
              (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 6)] 🡘
          LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
            ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 6), #5]) =
        (((Rew.embSubsts
            (fixedWidthBodyTerms table width index value)).q ▹
              LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
                ![fixedWidthSourceLeftBitIndexTerm,
                  (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 6)]) 🡘
          ((Rew.embSubsts
            (fixedWidthBodyTerms table width index value)).q ▹
              LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
                ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 6), #5])) :=
      rewriting_iff _ _ _
    _ = (binaryBitAtomAtTerms
            ((Rew.embSubsts
              (fixedWidthBodyTerms table width index value)).q
                fixedWidthSourceLeftBitIndexTerm)
            ((Rew.embSubsts
              (fixedWidthBodyTerms table width index value)).q
                (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 6)) 🡘
          binaryBitAtomAtTerms
            ((Rew.embSubsts
              (fixedWidthBodyTerms table width index value)).q
                (#0 : LO.FirstOrder.ArithmeticSemiterm Empty 6))
            ((Rew.embSubsts
              (fixedWidthBodyTerms table width index value)).q
                (#5 : LO.FirstOrder.ArithmeticSemiterm Empty 6))) := by
      rw [rewrite_membershipOperator,
        rewrite_membershipOperator]
    _ = (binaryBitAtomAtTerms
            (Rew.bShift.q
              (.func .add ![
                Rew.bShift (fixedWidthIndexWidthTerm width index), #0] :
                LO.FirstOrder.ArithmeticSemiterm Nat 1))
            (Rew.bShift.q
              (Rew.bShift (shortBinaryNumeralTerm table))) 🡘
          binaryBitAtomAtTerms
            (Rew.bShift.q
              (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1))
            (Rew.bShift.q
              (Rew.bShift (shortBinaryNumeralTerm value)))) := by
      rw [fixedWidthSourceLeftBitIndexTerm_rewrite,
        fixedWidthSourceLeftBitValueTerm_rewrite,
        fixedWidthSourceRightBitIndexTerm_rewrite,
        fixedWidthSourceRightBitValueTerm_rewrite]
    _ = ((Rew.bShift.q ▹
            binaryBitAtomAtTerms
              (.func .add ![
                Rew.bShift (fixedWidthIndexWidthTerm width index), #0])
              (Rew.bShift (shortBinaryNumeralTerm table))) 🡘
          (Rew.bShift.q ▹
            binaryBitAtomAtTerms
              (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)
              (Rew.bShift (shortBinaryNumeralTerm value)))) := by
      rw [rewrite_binaryBitAtomAtTerms,
        rewrite_binaryBitAtomAtTerms]
    _ = Rew.bShift.q ▹
        (binaryBitAtomAtTerms
            (.func .add ![
              Rew.bShift (fixedWidthIndexWidthTerm width index), #0])
            (Rew.bShift (shortBinaryNumeralTerm table)) 🡘
          binaryBitAtomAtTerms #0
            (Rew.bShift (shortBinaryNumeralTerm value))) :=
      (rewriting_iff _ _ _).symm

private theorem fixedWidthSourceUniversalBody_rewrite
    (table width index value : Nat) :
    Rew.embSubsts (fixedWidthBodyTerms table width index value) ▹
        fixedWidthSourceUniversalBody =
      liftClosedFormula
        (fixedWidthUniversalFormula table width index value) := by
  have hbound :
      Rew.embSubsts (fixedWidthBodyTerms table width index value)
          (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 5) =
        Rew.bShift (shortBinaryNumeralTerm width) := by
    simp [fixedWidthBodyTerms]
  unfold fixedWidthSourceUniversalBody liftClosedFormula
  unfold fixedWidthUniversalFormula
  calc
    Rew.embSubsts (fixedWidthBodyTerms table width index value) ▹
        fixedWidthSourceBitBody.ballLT
          (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 5) =
      ((Rew.embSubsts
          (fixedWidthBodyTerms table width index value)).q ▹
          fixedWidthSourceBitBody).ballLT
        (Rew.embSubsts
          (fixedWidthBodyTerms table width index value) #2) :=
      rewriting_ballLT _ _ _
    _ = (Rew.bShift.q ▹
          fixedWidthBitBody table width index value).ballLT
        (Rew.bShift (shortBinaryNumeralTerm width)) := by
      rw [fixedWidthSourceBitBody_rewrite, hbound]
    _ = Rew.bShift ▹
        (fixedWidthBitBody table width index value).ballLT
          (shortBinaryNumeralTerm width) :=
      (rewriting_ballLT _ _ _).symm

private theorem fixedWidthSourceExistentialBody_rewrite
    (table width index value : Nat) :
    Rew.embSubsts (fixedWidthBodyTerms table width index value) ▹
        fixedWidthSourceExistentialBody =
      fixedWidthExistentialBody table width index value := by
  unfold fixedWidthSourceExistentialBody fixedWidthExistentialBody
  simp only [LogicalConnective.HomClass.map_and]
  rw [fixedWidthSourceWitnessGuardBody_rewrite,
    fixedWidthSourceLengthBody_rewrite,
    fixedWidthSourceSizeGuardBody_rewrite,
    fixedWidthSourceUniversalBody_rewrite]

private theorem fixedWidthEmbeddedSourceBody_rewrite
    (table width index value : Nat) :
    (Rew.subst (fixedWidthOuterTerms table width index value)).q ▹
        (Rewriting.emb (ξ := Nat)
          fixedWidthSourceExistentialBody) =
      fixedWidthExistentialBody table width index value := by
  rw [← TransitiveRewriting.comp_app,
    fixedWidthBodyRewriting_eq_embSubsts,
    fixedWidthSourceExistentialBody_rewrite]

private theorem compactFixedWidthEntryClosedFormula_eq_exists
    (table width index value : Nat) :
    compactFixedWidthEntryClosedFormula table width index value =
      ∃⁰ fixedWidthExistentialBody table width index value := by
  unfold compactFixedWidthEntryClosedFormula
  rw [compactFixedWidthEntryDef_val_eq_sourceExists]
  change
    Rew.subst (fixedWidthOuterTerms table width index value) ▹
        (Rewriting.emb (ξ := Nat)
          (∃⁰ fixedWidthSourceExistentialBody)) =
      ∃⁰ fixedWidthExistentialBody table width index value
  simp only [Rewriting.app_exs, Rew.q_emb]
  rw [fixedWidthEmbeddedSourceBody_rewrite]

private def fixedWidthBitBranchContext
    (bitIndex : Nat) : Finset ArithmeticProposition :=
  insert
    (∼finiteCaseEqualityFormula
      (iteratedSuccessorTerm 0 bitIndex) (&0))
    ((∅ : Finset ArithmeticProposition).image Rewriting.shift)

private theorem valuationContext_singleton_eq_branchContext
    (bitIndex : Nat) :
    valuationContext {0}
        (extendValuation bitIndex zeroValuation) =
      fixedWidthBitBranchContext bitIndex := by
  simp [valuationContext, valuationEqualityAssumption,
    fixedWidthBitBranchContext, zeroValuation]

private noncomputable def compileFixedWidthBitBranch
    (table width index value bitIndex : Nat)
    (hbit : table.testBit (index * width + bitIndex) =
      value.testBit bitIndex) :
    CertifiedPAContextProof
      (fixedWidthBitBranchContext bitIndex)
      (Rewriting.free (fixedWidthBitBody table width index value)) := by
  let valuation := extendValuation bitIndex zeroValuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm width index
  let leftValueTerm := fixedWidthLeftBitValueTerm table
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm value
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
  let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
  let expected := value.testBit bitIndex

  have hleftValue :
      (termValue valuation leftValueTerm).testBit
          (termValue valuation leftIndexTerm) = expected := by
    change
      (termValue (extendValuation bitIndex zeroValuation)
          (fixedWidthLeftBitValueTerm table)).testBit
        (termValue (extendValuation bitIndex zeroValuation)
          (fixedWidthLeftBitIndexTerm width index)) =
        value.testBit bitIndex
    rw [termValue_fixedWidthLeftBitValueTerm,
      termValue_fixedWidthLeftBitIndexTerm]
    exact hbit
  have hrightValue :
      (termValue valuation rightValueTerm).testBit
          (termValue valuation rightIndexTerm) = expected := by
    change
      (termValue (extendValuation bitIndex zeroValuation)
          (fixedWidthRightBitValueTerm value)).testBit
        (termValue (extendValuation bitIndex zeroValuation)
          fixedWidthRightBitIndexTerm) = value.testBit bitIndex
    rw [termValue_fixedWidthRightBitValueTerm,
      termValue_fixedWidthRightBitIndexTerm]

  have hleftVariables :
      leftIndexTerm.freeVariables ∪ leftValueTerm.freeVariables = {0} := by
    simp [leftIndexTerm, leftValueTerm,
      fixedWidthLeftBitIndexTerm_freeVariables,
      fixedWidthLeftBitValueTerm_freeVariables_eq_empty]
  have hrightVariables :
      rightIndexTerm.freeVariables ∪ rightValueTerm.freeVariables = {0} := by
    simp [rightIndexTerm, rightValueTerm, fixedWidthRightBitIndexTerm,
      fixedWidthRightBitValueTerm_freeVariables_eq_empty]
  have hleftContext :
      binaryBitValuationContext valuation leftIndexTerm leftValueTerm =
        fixedWidthBitBranchContext bitIndex := by
    unfold binaryBitValuationContext
    rw [hleftVariables]
    exact valuationContext_singleton_eq_branchContext bitIndex
  have hrightContext :
      binaryBitValuationContext valuation rightIndexTerm rightValueTerm =
        fixedWidthBitBranchContext bitIndex := by
    unfold binaryBitValuationContext
    rw [hrightVariables]
    exact valuationContext_singleton_eq_branchContext bitIndex

  cases hexpected : expected with
  | false =>
      let leftRaw := compileBinaryBitLiteralAtValuation false valuation
        leftIndexTerm leftValueTerm (by simpa [hexpected] using hleftValue)
      let rightRaw := compileBinaryBitLiteralAtValuation false valuation
        rightIndexTerm rightValueTerm (by simpa [hexpected] using hrightValue)
      let leftProof := CertifiedPAContextProof.castContext
        hleftContext leftRaw
      let rightProof := CertifiedPAContextProof.castContext
        hrightContext rightRaw
      let forward : CertifiedPAContextProof
          (fixedWidthBitBranchContext bitIndex) (∼leftAtom ⋎ rightAtom) :=
        CertifiedPAContextProof.disjunctionLeft leftProof
      let backward : CertifiedPAContextProof
          (fixedWidthBitBranchContext bitIndex) (∼rightAtom ⋎ leftAtom) :=
        CertifiedPAContextProof.disjunctionLeft rightProof
      let iffProof := CertifiedPAContextProof.conjunction forward backward
      have hformula :
          ((∼leftAtom ⋎ rightAtom) ⋏ (∼rightAtom ⋎ leftAtom)) =
            Rewriting.free
              (fixedWidthBitBody table width index value) := by
        rw [← LO.FirstOrder.Semiformula.iff_eq]
        exact (fixedWidthBitBody_free table width index value).symm
      exact CertifiedPAContextProof.cast hformula iffProof
  | true =>
      let leftRaw := compileBinaryBitLiteralAtValuation true valuation
        leftIndexTerm leftValueTerm (by simpa [hexpected] using hleftValue)
      let rightRaw := compileBinaryBitLiteralAtValuation true valuation
        rightIndexTerm rightValueTerm (by simpa [hexpected] using hrightValue)
      let leftProof := CertifiedPAContextProof.castContext
        hleftContext leftRaw
      let rightProof := CertifiedPAContextProof.castContext
        hrightContext rightRaw
      let forward : CertifiedPAContextProof
          (fixedWidthBitBranchContext bitIndex) (∼leftAtom ⋎ rightAtom) :=
        CertifiedPAContextProof.disjunctionRight rightProof
      let backward : CertifiedPAContextProof
          (fixedWidthBitBranchContext bitIndex) (∼rightAtom ⋎ leftAtom) :=
        CertifiedPAContextProof.disjunctionRight leftProof
      let iffProof := CertifiedPAContextProof.conjunction forward backward
      have hformula :
          ((∼leftAtom ⋎ rightAtom) ⋏ (∼rightAtom ⋎ leftAtom)) =
            Rewriting.free
              (fixedWidthBitBody table width index value) := by
        rw [← LO.FirstOrder.Semiformula.iff_eq]
        exact (fixedWidthBitBody_free table width index value).symm
      exact CertifiedPAContextProof.cast hformula iffProof

private noncomputable def compileFixedWidthBitBranches
    (table width index value bitCount : Nat)
    (hbits : ∀ bitIndex < bitCount,
      table.testBit (index * width + bitIndex) =
        value.testBit bitIndex) :
    CertifiedContextFiniteUniversalBranches
      ((∅ : Finset ArithmeticProposition).image Rewriting.shift)
      (Rewriting.free (fixedWidthBitBody table width index value))
      bitCount := by
  induction bitCount with
  | zero => exact .nil
  | succ previous inductionHypothesis =>
      let initial := inductionHypothesis (fun bitIndex hindex =>
        hbits bitIndex
          (Nat.lt_trans hindex (Nat.lt_succ_self previous)))
      let last := compileFixedWidthBitBranch
        table width index value previous
        (hbits previous (Nat.lt_succ_self previous))
      exact .snoc initial last

private noncomputable def compileFixedWidthUniversal
    (table width index value : Nat)
    (hbits : ∀ bitIndex < width,
      table.testBit (index * width + bitIndex) =
        value.testBit bitIndex) :
    CertifiedPAContextProof ∅
      (fixedWidthUniversalFormula table width index value) := by
  let boundSource : ValuationTerm := shortBinaryNumeralTerm width
  let body := fixedWidthBitBody table width index value
  let boundRaw := compileShiftedBoundEquality
    zeroValuation ∅ boundSource (by
      simp [boundSource, shortBinaryNumeralTerm_freeVariables_eq_empty])
  have hboundContext :
      (valuationContext ∅ zeroValuation).image Rewriting.shift =
        (∅ : Finset ArithmeticProposition).image Rewriting.shift := by
    simp [valuationContext]
  let boundInEmpty := CertifiedPAContextProof.castContext
    hboundContext boundRaw
  let boundEquality : CertifiedPAContextProof
      ((∅ : Finset ArithmeticProposition).image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0 width) =
        !!(Rew.free (Rew.bShift boundSource))” :
        ArithmeticProposition) := by
    have hformula :
        (“!!(iteratedSuccessorTerm 0
              (termValue zeroValuation boundSource)) =
            !!(Rew.shift boundSource)” : ArithmeticProposition) =
          (“!!(iteratedSuccessorTerm 0 width) =
            !!(Rew.free (Rew.bShift boundSource))” :
            ArithmeticProposition) := by
      rw [termValue_shortBinaryNumeralTerm, free_bShift_term]
    exact CertifiedPAContextProof.cast hformula boundInEmpty
  let branches := compileFixedWidthBitBranches
    table width index value width hbits
  let raw := compileContextualTermBoundedUniversal
    width (Rew.bShift boundSource) body boundEquality branches
  have hformula :
      (∀⁰ termBoundedUniversalBody (Rew.bShift boundSource) body) =
        fixedWidthUniversalFormula table width index value := by
    rw [termBoundedUniversal_eq_ball]
    rfl
  exact CertifiedPAContextProof.cast hformula raw

private theorem fixedWidthWitnessGuard_freeVariables_eq_empty
    (value : Nat) :
    (fixedWidthWitnessGuard value).freeVariables = ∅ := by
  unfold fixedWidthWitnessGuard
  rw [lessThanFormula_freeVariables,
    arithmeticAddTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    arithmeticOneTerm_freeVariables_eq_empty]
  rfl

private theorem fixedWidthSizeGuard_freeVariables_eq_empty
    (width value : Nat) :
    (fixedWidthSizeGuard width value).freeVariables = ∅ := by
  unfold fixedWidthSizeGuard
  rw [lessEqualFormula_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  rfl

private theorem formulaValue_lessThan
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    formulaValue valuation
        (“!!left < !!right” : ValuationFormula) ↔
      termValue valuation left < termValue valuation right := by
  simp [formulaValue, termValue]

private theorem formulaValue_lessEqual
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    formulaValue valuation
        (“!!left ≤ !!right” : ValuationFormula) ↔
      @LE.le Nat LO.FirstOrder.Arithmetic.instLE_foundation
        (termValue valuation left) (termValue valuation right) := by
  simp [formulaValue, termValue]

private theorem termValue_shortBinaryNumeralAddOne
    (value : Nat) :
    termValue zeroValuation
        (‘!!(shortBinaryNumeralTerm value) + 1’ : ValuationTerm) =
      value + 1 := by
  change termValue zeroValuation
      (paAddTerm (shortBinaryNumeralTerm value) paOneTerm) = value + 1
  have hone : termValue zeroValuation paOneTerm = 1 := by
    unfold paOneTerm FoundationCompactBinaryNumeralTerm.arithmeticOneTerm
    exact termValue_one zeroValuation ![]
  rw [termValue_paAddTerm, termValue_shortBinaryNumeralTerm, hone]

private theorem formulaValue_fixedWidthWitnessGuard_iff
    (value : Nat) :
    formulaValue zeroValuation (fixedWidthWitnessGuard value) ↔
      Nat.size value < value + 1 := by
  unfold fixedWidthWitnessGuard
  rw [formulaValue_lessThan,
    termValue_shortBinaryNumeralTerm,
    termValue_shortBinaryNumeralAddOne]

private theorem formulaValue_fixedWidthSizeGuard_iff
    (width value : Nat) :
    formulaValue zeroValuation (fixedWidthSizeGuard width value) ↔
      @LE.le Nat LO.FirstOrder.Arithmetic.instLE_foundation
        (Nat.size value) width := by
  unfold fixedWidthSizeGuard
  rw [formulaValue_lessEqual,
    termValue_shortBinaryNumeralTerm,
    termValue_shortBinaryNumeralTerm]

private noncomputable def compileClosedSigmaZeroTruth
    (formula : ArithmeticProposition)
    (hhierarchy : Hierarchy Polarity.sigma 0 formula)
    (htruth : formulaValue zeroValuation formula)
    (hclosed : formula.freeVariables = ∅) :
    CertifiedPAContextProof ∅ formula := by
  let raw := compileSigmaZeroTruth
    formula hhierarchy zeroValuation htruth
  have hcontext :
      valuationContext formula.freeVariables zeroValuation = ∅ := by
    rw [hclosed]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

private noncomputable def compileFixedWidthWitnessGuard
    (value : Nat) :
    CertifiedPAContextProof ∅ (fixedWidthWitnessGuard value) := by
  have hwitnessBound :
      @LE.le Nat instLENat (Nat.size value) value := by
    have hlength := LO.FirstOrder.Arithmetic.length_le (V := Nat) value
    have hlengthEq : (‖value‖ : Nat) =
        LO.FirstOrder.Arithmetic.binaryLength value := rfl
    rw [hlengthEq, binaryLength_nat_eq_size] at hlength
    exact (foundationNatLE_iff_standard
      (Nat.size value) value).mp hlength
  apply compileClosedSigmaZeroTruth
  · simp [fixedWidthWitnessGuard]
  · exact (formulaValue_fixedWidthWitnessGuard_iff value).mpr
      (Nat.lt_succ_of_le hwitnessBound)
  · exact fixedWidthWitnessGuard_freeVariables_eq_empty value

private noncomputable def compileFixedWidthSizeGuard
    (width value : Nat)
    (hsize : @LE.le Nat instLENat (Nat.size value) width) :
    CertifiedPAContextProof ∅ (fixedWidthSizeGuard width value) := by
  have hsizeFoundation :
      @LE.le Nat LO.FirstOrder.Arithmetic.instLE_foundation
        (Nat.size value) width :=
    (foundationNatLE_iff_standard
      (Nat.size value) width).mpr hsize
  apply compileClosedSigmaZeroTruth
  · simp [fixedWidthSizeGuard]
  · exact (formulaValue_fixedWidthSizeGuard_iff width value).mpr
      hsizeFoundation
  · exact fixedWidthSizeGuard_freeVariables_eq_empty width value

private noncomputable def compileFixedWidthLength
    (value : Nat) :
    CertifiedPAContextProof ∅ (fixedWidthLengthFormula value) := by
  let sizeTerm : ValuationTerm :=
    shortBinaryNumeralTerm (Nat.size value)
  let valueTerm : ValuationTerm := shortBinaryNumeralTerm value
  let raw := compileBinaryLengthAtValuation
    zeroValuation sizeTerm valueTerm (by
      simp [sizeTerm, valueTerm, termValue_shortBinaryNumeralTerm])
  have hcontext :
      binaryLengthValuationContext zeroValuation sizeTerm valueTerm = ∅ := by
    simp [binaryLengthValuationContext, valuationContext,
      sizeTerm, valueTerm,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
  exact CertifiedPAContextProof.castContext hcontext raw

private def certifiedProofOfEmptyContext
    {formula : ArithmeticProposition}
    (proof : CertifiedPAContextProof ∅ formula) :
    CertifiedPAProof formula where
  derivation := by simpa using proof.derivation
  certificate := proof.certificate
  certificate_valid := by simpa using proof.certificate_valid

noncomputable def compileCompactFixedWidthEntryClosed
    (table width index value : Nat)
    (hentry : CompactFixedWidthEntry table width index value) :
    CertifiedPAProof
      (compactFixedWidthEntryClosedFormula table width index value) := by
  let witnessGuard := compileFixedWidthWitnessGuard value
  let lengthProof := compileFixedWidthLength value
  let sizeGuard := compileFixedWidthSizeGuard width value hentry.1
  let universal := compileFixedWidthUniversal
    table width index value hentry.2
  let lengthAndTail := CertifiedPAContextProof.conjunction lengthProof
    (CertifiedPAContextProof.conjunction sizeGuard universal)
  let postWitness := CertifiedPAContextProof.conjunction
    witnessGuard lengthAndTail
  let instantiatedBody : CertifiedPAContextProof ∅
      ((fixedWidthExistentialBody table width index value)/[
        shortBinaryNumeralTerm (Nat.size value)]) :=
    CertifiedPAContextProof.cast
      (fixedWidthExistentialBody_subst table width index value).symm
      postWitness
  let existential := CertifiedPAContextProof.existsIntro
    (shortBinaryNumeralTerm (Nat.size value)) instantiatedBody
  let closedExistential := certifiedProofOfEmptyContext existential
  exact CertifiedPAProof.cast
    (compactFixedWidthEntryClosedFormula_eq_exists
      table width index value).symm
    closedExistential

#print axioms compileCompactFixedWidthEntryClosed

/-! ## Explicit hybrid certificate

The direct compiler above already constructs a checked PA proof.  The
certificate below exposes the same construction to the structural-resource
recursor: the size witness is `Nat.size value`, and every bit branch is built
by the `nil`/`snoc` constructors rather than selected from truth.
-/

private abbrev FixedWidthHybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

private abbrev FixedWidthHybridBranches
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bound : Nat) :=
  CheckedHybridValuationUniversalBranches valuation body bound

private noncomputable def fixedWidthWitnessGuardHybridCertificate
    (value : Nat) :
    FixedWidthHybridCertificate zeroValuation
      (fixedWidthWitnessGuard value) := by
  have hsizeValue : Nat.size value ≤ value := by
    have hlength := LO.FirstOrder.Arithmetic.length_le (V := Nat) value
    have hlengthEq : (‖value‖ : Nat) =
        LO.FirstOrder.Arithmetic.binaryLength value := rfl
    rw [hlengthEq, binaryLength_nat_eq_size] at hlength
    exact (foundationNatLE_iff_standard
      (Nat.size value) value).mp hlength
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm (Nat.size value),
        (‘!!(shortBinaryNumeralTerm value) + 1’ : ValuationTerm)] (by
          change termValue zeroValuation
              (shortBinaryNumeralTerm (Nat.size value)) <
            termValue zeroValuation
              (‘!!(shortBinaryNumeralTerm value) + 1’ : ValuationTerm)
          rw [termValue_shortBinaryNumeralTerm,
            termValue_shortBinaryNumeralAddOne]
          exact Nat.lt_succ_of_le hsizeValue)
  exact .cast (by
    unfold fixedWidthWitnessGuard
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

private noncomputable def fixedWidthLengthHybridCertificate
    (value : Nat) :
    FixedWidthHybridCertificate zeroValuation
      (fixedWidthLengthFormula value) := by
  let sizeTerm : ValuationTerm :=
    shortBinaryNumeralTerm (Nat.size value)
  let valueTerm : ValuationTerm := shortBinaryNumeralTerm value
  let direct := CheckedHybridValuationBoundedFormulaCertificate.binaryLength
    zeroValuation sizeTerm valueTerm (by
      simp [sizeTerm, valueTerm, termValue_shortBinaryNumeralTerm])
  simpa [fixedWidthLengthFormula, sizeTerm, valueTerm] using direct

private noncomputable def fixedWidthSizeGuardHybridCertificate
    (width value : Nat)
    (hsize : Nat.size value ≤ width) :
    FixedWidthHybridCertificate zeroValuation
      (fixedWidthSizeGuard width value) := by
  let sizeTerm : ValuationTerm := shortBinaryNumeralTerm (Nat.size value)
  let widthTerm : ValuationTerm := shortBinaryNumeralTerm width
  if hequal : Nat.size value = width then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.Eq.eq ![sizeTerm, widthTerm] (by
          change termValue zeroValuation sizeTerm =
            termValue zeroValuation widthTerm
          simpa [sizeTerm, widthTerm, termValue_shortBinaryNumeralTerm]
            using hequal)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
          ![sizeTerm, widthTerm]) equality
    exact .cast (by
      unfold fixedWidthSizeGuard sizeTerm widthTerm
      exact (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm) direct
  else
    let hstrict := Nat.lt_of_le_of_ne hsize hequal
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.ORing.Rel.lt ![sizeTerm, widthTerm] (by
          change termValue zeroValuation sizeTerm <
            termValue zeroValuation widthTerm
          simpa [sizeTerm, widthTerm, termValue_shortBinaryNumeralTerm]
            using hstrict)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![sizeTerm, widthTerm]) strict
    exact .cast (by
      unfold fixedWidthSizeGuard sizeTerm widthTerm
      exact (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm) direct

private theorem fixedWidthLeftBitHybridVariables
    (table width index value bitIndex : Nat) :
    let valuation := extendValuation bitIndex zeroValuation
    let indexTerm := fixedWidthLeftBitIndexTerm width index
    let valueTerm := fixedWidthLeftBitValueTerm table
    indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
      (binaryBitAtValuationFormula true indexTerm valueTerm).freeVariables := by
  simpa [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
    binaryBitAtomAtTerms,
    FoundationCompactPAFastArithmeticLeafRecognizer.bitInstance] using
      bitInstance_argument_freeVariables_union_subset
        (fixedWidthLeftBitIndexTerm width index)
        (fixedWidthLeftBitValueTerm table)

private theorem fixedWidthRightBitHybridVariables
    (value bitIndex : Nat) :
    let valuation := extendValuation bitIndex zeroValuation
    let indexTerm := fixedWidthRightBitIndexTerm
    let valueTerm := fixedWidthRightBitValueTerm value
    indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
      (binaryBitAtValuationFormula true indexTerm valueTerm).freeVariables := by
  simpa [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
    binaryBitAtomAtTerms,
    FoundationCompactPAFastArithmeticLeafRecognizer.bitInstance] using
      bitInstance_argument_freeVariables_union_subset
        fixedWidthRightBitIndexTerm
        (fixedWidthRightBitValueTerm value)

private theorem binaryBitFalse_freeVariables_eq_true
    (indexTerm valueTerm : ValuationTerm) :
    (binaryBitAtValuationFormula false indexTerm valueTerm).freeVariables =
      (binaryBitAtValuationFormula true indexTerm valueTerm).freeVariables := by
  simp [binaryBitAtValuationFormula, binaryBitLiteralAtTerms]

private noncomputable def fixedWidthBitHybridCertificate
    (table width index value bitIndex : Nat)
    (hbit : table.testBit (index * width + bitIndex) =
      value.testBit bitIndex) :
    FixedWidthHybridCertificate
      (extendValuation bitIndex zeroValuation)
      (Rewriting.free (fixedWidthBitBody table width index value)) := by
  let valuation := extendValuation bitIndex zeroValuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm width index
  let leftValueTerm := fixedWidthLeftBitValueTerm table
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm value
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
  let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
  let expected := value.testBit bitIndex
  have hleftValue :
      (termValue valuation leftValueTerm).testBit
          (termValue valuation leftIndexTerm) = expected := by
    simpa [valuation, leftValueTerm, leftIndexTerm, expected,
      termValue_fixedWidthLeftBitValueTerm,
      termValue_fixedWidthLeftBitIndexTerm] using hbit
  have hrightValue :
      (termValue valuation rightValueTerm).testBit
          (termValue valuation rightIndexTerm) = expected := by
    simp [valuation, rightValueTerm, rightIndexTerm, expected,
      termValue_fixedWidthRightBitValueTerm,
      termValue_fixedWidthRightBitIndexTerm]
  have hleftVariablesTrue :
      leftIndexTerm.freeVariables ∪ leftValueTerm.freeVariables ⊆
        (binaryBitAtValuationFormula true
          leftIndexTerm leftValueTerm).freeVariables := by
    simpa [leftIndexTerm, leftValueTerm] using
      fixedWidthLeftBitHybridVariables table width index value bitIndex
  have hrightVariablesTrue :
      rightIndexTerm.freeVariables ∪ rightValueTerm.freeVariables ⊆
        (binaryBitAtValuationFormula true
          rightIndexTerm rightValueTerm).freeVariables := by
    simpa [rightIndexTerm, rightValueTerm] using
      fixedWidthRightBitHybridVariables value bitIndex
  cases hexpected : expected with
  | false =>
      have hleftVariablesFalse :
          leftIndexTerm.freeVariables ∪ leftValueTerm.freeVariables ⊆
            (binaryBitAtValuationFormula false
              leftIndexTerm leftValueTerm).freeVariables := by
        rw [binaryBitFalse_freeVariables_eq_true]
        exact hleftVariablesTrue
      have hrightVariablesFalse :
          rightIndexTerm.freeVariables ∪ rightValueTerm.freeVariables ⊆
            (binaryBitAtValuationFormula false
              rightIndexTerm rightValueTerm).freeVariables := by
        rw [binaryBitFalse_freeVariables_eq_true]
        exact hrightVariablesTrue
      let leftFalse :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
          valuation leftIndexTerm leftValueTerm
          (by simpa [hexpected] using hleftValue) hleftVariablesFalse
      let rightFalse :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
          valuation rightIndexTerm rightValueTerm
          (by simpa [hexpected] using hrightValue) hrightVariablesFalse
      let forward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := rightAtom) leftFalse
      let backward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := leftAtom) rightFalse
      let source :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          forward backward
      exact .cast (by
        change ((∼leftAtom ⋎ rightAtom) ⋏ (∼rightAtom ⋎ leftAtom)) = _
        rw [← LO.FirstOrder.Semiformula.iff_eq]
        exact (fixedWidthBitBody_free table width index value).symm) source
  | true =>
      let leftTrue :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
          valuation leftIndexTerm leftValueTerm
          (by simpa [hexpected] using hleftValue) hleftVariablesTrue
      let rightTrue :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
          valuation rightIndexTerm rightValueTerm
          (by simpa [hexpected] using hrightValue) hrightVariablesTrue
      let forward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼leftAtom) rightTrue
      let backward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼rightAtom) leftTrue
      let source :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          forward backward
      exact .cast (by
        change ((∼leftAtom ⋎ rightAtom) ⋏ (∼rightAtom ⋎ leftAtom)) = _
        rw [← LO.FirstOrder.Semiformula.iff_eq]
        exact (fixedWidthBitBody_free table width index value).symm) source

private noncomputable def fixedWidthBitHybridBranches
    (table width index value bitCount : Nat)
    (hbits : ∀ bitIndex < bitCount,
      table.testBit (index * width + bitIndex) =
        value.testBit bitIndex) :
    FixedWidthHybridBranches zeroValuation
      (fixedWidthBitBody table width index value) bitCount := by
  induction bitCount with
  | zero => exact .nil zeroValuation _
  | succ previous inductionHypothesis =>
      let initial := inductionHypothesis (fun bitIndex hindex =>
        hbits bitIndex (Nat.lt_trans hindex (Nat.lt_succ_self previous)))
      let last := fixedWidthBitHybridCertificate
        table width index value previous
        (hbits previous (Nat.lt_succ_self previous))
      exact .snoc initial last

private noncomputable def fixedWidthUniversalHybridCertificate
    (table width index value : Nat)
    (hbits : ∀ bitIndex < width,
      table.testBit (index * width + bitIndex) =
        value.testBit bitIndex) :
    FixedWidthHybridCertificate zeroValuation
      (fixedWidthUniversalFormula table width index value) := by
  let boundSource : ValuationTerm := shortBinaryNumeralTerm width
  let branches := fixedWidthBitHybridBranches
    table width index value width hbits
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      boundSource (fixedWidthBitBody table width index value) (by
        simpa [boundSource, termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody (Rew.bShift boundSource)
        (fixedWidthBitBody table width index value)) =
        fixedWidthUniversalFormula table width index value
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- Explicit certificate for one fixed-width row.  No existential or universal
branch is recovered from a truth theorem. -/
noncomputable def compactFixedWidthEntryExplicitHybridCertificate
    (table width index value : Nat)
    (hentry : CompactFixedWidthEntry table width index value) :
    FixedWidthHybridCertificate zeroValuation
      (compactFixedWidthEntryClosedFormula table width index value) := by
  rw [compactFixedWidthEntryClosedFormula_eq_exists]
  refine .existsWitness
    (fixedWidthExistentialBody table width index value)
    (Nat.size value) ?_
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (fixedWidthWitnessGuardHybridCertificate value)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (fixedWidthLengthHybridCertificate value)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (fixedWidthSizeGuardHybridCertificate width value hentry.1)
        (fixedWidthUniversalHybridCertificate
          table width index value hentry.2)))
  exact .cast
    (fixedWidthExistentialBody_subst table width index value).symm post

theorem compactFixedWidthEntryClosedFormula_freeVariables_eq_empty
    (table width index value : Nat) :
    (compactFixedWidthEntryClosedFormula
      table width index value).freeVariables = ∅ := by
  unfold compactFixedWidthEntryClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  cases coordinate using Fin.cases with
  | zero => exact shortBinaryNumeralTerm_freeVariables_eq_empty table
  | succ coordinate =>
      cases coordinate using Fin.cases with
      | zero => exact shortBinaryNumeralTerm_freeVariables_eq_empty width
      | succ coordinate =>
          cases coordinate using Fin.cases with
          | zero => exact shortBinaryNumeralTerm_freeVariables_eq_empty index
          | succ coordinate =>
              cases coordinate using Fin.cases with
              | zero =>
                  exact shortBinaryNumeralTerm_freeVariables_eq_empty value
              | succ coordinate => exact Fin.elim0 coordinate

/-- Checked PA context proof compiled from the explicit hybrid certificate. -/
noncomputable def compileCompactFixedWidthEntryExplicitHybridContext
    (table width index value : Nat)
    (hentry : CompactFixedWidthEntry table width index value) :
    CertifiedPAContextProof ∅
      (compactFixedWidthEntryClosedFormula table width index value) := by
  let raw :=
    (compactFixedWidthEntryExplicitHybridCertificate
      table width index value hentry).compile
  have hcontext :
      valuationContext
          (compactFixedWidthEntryClosedFormula
            table width index value).freeVariables zeroValuation = ∅ := by
    rw [compactFixedWidthEntryClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

/-- Proof-free recursive resource for the explicit row certificate. -/
noncomputable def compactFixedWidthEntryExplicitHybridStructuralResource
    (table width index value : Nat)
    (hentry : CompactFixedWidthEntry table width index value) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactFixedWidthEntryExplicitHybridCertificate
      table width index value hentry)

theorem compileCompactFixedWidthEntryExplicitHybridContext_payloadLength_le
    (table width index value : Nat)
    (hentry : CompactFixedWidthEntry table width index value) :
    (compileCompactFixedWidthEntryExplicitHybridContext
      table width index value hentry).payloadLength ≤
      compactFixedWidthEntryExplicitHybridStructuralResource
        table width index value hentry := by
  unfold compileCompactFixedWidthEntryExplicitHybridContext
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactFixedWidthEntryExplicitHybridCertificate
        table width index value hentry)

#print axioms compactFixedWidthEntryExplicitHybridCertificate
#print axioms compileCompactFixedWidthEntryExplicitHybridContext
#print axioms compileCompactFixedWidthEntryExplicitHybridContext_payloadLength_le

end FoundationCompactPAFixedWidthEntryHybridCompiler
