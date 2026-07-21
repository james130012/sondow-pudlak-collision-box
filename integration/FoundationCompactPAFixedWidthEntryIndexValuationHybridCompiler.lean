import integration.FoundationCompactPAFixedWidthEntryHybridCompiler

/-!
# Valuation-term fixed-width entry hybrid compiler

This is the open-term counterpart of the closed fixed-width row compiler.
All four row coordinates are valuation terms.  The size witness is still the
explicit numeral `Nat.size (termValue valuation valueTerm)`, while every bit
of the bounded universal is certified by a `binaryBit` leaf.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactPAQuantitativeCompilerCore
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
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFastArithmeticLeafRecognizer
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

private abbrev FixedWidthHybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

private abbrev FixedWidthHybridBranches
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bound : Nat) :=
  CheckedHybridValuationUniversalBranches valuation body bound

/-- The quoted fixed-width-entry predicate at four arbitrary valuation terms. -/
def compactFixedWidthEntryAtValuationFormula
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
    ![tableTerm, widthTerm, indexTerm, valueTerm]

def fixedWidthIndexWidthTerm
    (widthTerm indexTerm : ValuationTerm) : ValuationTerm :=
  paMulTerm indexTerm widthTerm

def fixedWidthLeftBitIndexTerm
    (widthTerm indexTerm : ValuationTerm) : ValuationTerm :=
  paAddTerm (Rew.shift (fixedWidthIndexWidthTerm widthTerm indexTerm)) (&0)

def fixedWidthLeftBitValueTerm
    (tableTerm : ValuationTerm) : ValuationTerm :=
  Rew.shift tableTerm

def fixedWidthRightBitIndexTerm : ValuationTerm := &0

def fixedWidthRightBitValueTerm
    (valueTerm : ValuationTerm) : ValuationTerm :=
  Rew.shift valueTerm

def fixedWidthBitBody
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  binaryBitAtomAtTerms
      (.func .add ![
        Rew.bShift (fixedWidthIndexWidthTerm widthTerm indexTerm), #0])
      (Rew.bShift tableTerm) 🡘
    binaryBitAtomAtTerms #0 (Rew.bShift valueTerm)

def fixedWidthUniversalFormula
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    ValuationFormula :=
  (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm).ballLT widthTerm

def fixedWidthWitnessGuard
    (size : Nat) (valueTerm : ValuationTerm) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm size) < !!valueTerm + 1”

def fixedWidthLengthFormula
    (size : Nat) (valueTerm : ValuationTerm) : ValuationFormula :=
  binaryLengthAtValuationFormula (shortBinaryNumeralTerm size) valueTerm

def fixedWidthSizeGuard
    (size : Nat) (widthTerm : ValuationTerm) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm size) ≤ !!widthTerm”

/-- The explicit formula after installing the numeral size witness. -/
def compactFixedWidthEntryAtValuationPostWitnessFormula
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (size : Nat) : ValuationFormula :=
  fixedWidthWitnessGuard size valueTerm ⋏
    (fixedWidthLengthFormula size valueTerm ⋏
      (fixedWidthSizeGuard size widthTerm ⋏
        fixedWidthUniversalFormula tableTerm widthTerm indexTerm valueTerm))

private def liftValuationFormula
    (formula : ValuationFormula) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  Rew.bShift ▹ formula

private def fixedWidthWitnessGuardBody
    (valueTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift valueTerm) + 1”

private def fixedWidthLengthBody
    (valueTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “!lengthDef #0 !!(Rew.bShift valueTerm)”

private def fixedWidthSizeGuardBody
    (widthTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 ≤ !!(Rew.bShift widthTerm)”

/-- The explicit body under the size existential. -/
def compactFixedWidthEntryAtValuationWitnessBody
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  fixedWidthWitnessGuardBody valueTerm ⋏
    (fixedWidthLengthBody valueTerm ⋏
      (fixedWidthSizeGuardBody widthTerm ⋏
        liftValuationFormula
          (fixedWidthUniversalFormula
            tableTerm widthTerm indexTerm valueTerm)))

private theorem subst_bShiftTerm
    (term witness : ValuationTerm) :
    Rew.subst ![witness] (Rew.bShift term) = term := by
  calc
    Rew.subst ![witness] (Rew.bShift term) =
        ((Rew.subst ![witness]).comp Rew.bShift) term := by
      rw [Rew.comp_app]
    _ = Rew.id term := by rw [Rew.subst_comp_bShift_eq_id]
    _ = term := Rew.id_app term

private theorem liftValuationFormula_subst
    (formula : ValuationFormula) (witness : ValuationTerm) :
    (liftValuationFormula formula)/[witness] = formula := by
  unfold liftValuationFormula
  calc
    Rew.subst ![witness] ▹ (Rew.bShift ▹ formula) =
        ((Rew.subst ![witness]).comp Rew.bShift) ▹ formula :=
      (TransitiveRewriting.comp_app _ _ _).symm
    _ = Rew.id ▹ formula := by rw [Rew.subst_comp_bShift_eq_id]
    _ = formula := ReflectiveRewriting.id_app formula

/-- Substituting the explicit size numeral into the existential body gives
exactly the advertised post-witness conjunction. -/
theorem compactFixedWidthEntryAtValuationWitnessBody_subst
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (size : Nat) :
    (compactFixedWidthEntryAtValuationWitnessBody
      tableTerm widthTerm indexTerm valueTerm)/[
        shortBinaryNumeralTerm size] =
      compactFixedWidthEntryAtValuationPostWitnessFormula
        tableTerm widthTerm indexTerm valueTerm size := by
  simp [compactFixedWidthEntryAtValuationWitnessBody,
    compactFixedWidthEntryAtValuationPostWitnessFormula,
    fixedWidthWitnessGuardBody, fixedWidthLengthBody,
    fixedWidthSizeGuardBody, fixedWidthWitnessGuard,
    fixedWidthLengthFormula, fixedWidthSizeGuard,
    binaryLengthAtValuationFormula, subst_lengthDef_instance,
    liftValuationFormula_subst,
    LO.FirstOrder.Semiformula.Operator.le_def]

private def fixedWidthSourceWitnessGuardBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “#0 < #4 + 1”

private def fixedWidthSourceLengthBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “!lengthDef #0 #4”

private def fixedWidthSourceSizeGuardBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  “#0 ≤ #2”

private def fixedWidthSourceBitBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 6 :=
  “((#4 * #3 + #0) ∈ #2 ↔ #0 ∈ #5)”

private def fixedWidthSourceUniversalBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  fixedWidthSourceBitBody.ballLT
    (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 5)

private def fixedWidthSourceExistentialBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 5 :=
  fixedWidthSourceWitnessGuardBody ⋏
    (fixedWidthSourceLengthBody ⋏
      (fixedWidthSourceSizeGuardBody ⋏ fixedWidthSourceUniversalBody))

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
    compactFixedWidthEntryDef.val = ∃⁰ fixedWidthSourceExistentialBody := by
  unfold compactFixedWidthEntryDef compactNatSizeDef
  change
    (fixedWidthSourceLengthBody ⋏
        (fixedWidthSourceSizeGuardBody ⋏ fixedWidthSourceUniversalBody)).bexsLTSucc
        (#3 : LO.FirstOrder.ArithmeticSemiterm Empty 4) =
      ∃⁰ fixedWidthSourceExistentialBody
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
  unfold LO.FirstOrder.Semiformula.bexsLT
  unfold fixedWidthSourceExistentialBody fixedWidthSourceWitnessGuardBody
  rw [bShift_fixedWidthSourceWitnessBound]
  rfl

private def fixedWidthOuterTerms
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    Fin 4 -> ValuationTerm :=
  ![tableTerm, widthTerm, indexTerm, valueTerm]

private def fixedWidthBodyTerms
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    Fin 5 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
    Rew.bShift tableTerm, Rew.bShift widthTerm,
    Rew.bShift indexTerm, Rew.bShift valueTerm]

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
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
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_formulaOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : LO.FirstOrder.Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms =
      operator.operator (rewriting ∘ terms) := by
  unfold LO.FirstOrder.Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution
    rewriting operator.sentence terms

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : LO.FirstOrder.ArithmeticSemiformula sourceVariables
      (sourceArity + 1))
    (bound : LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm sourceVariables
              (sourceArity + 1)), Rew.bShift bound] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm targetVariables
              (targetArity + 1)), Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold LO.FirstOrder.Semiformula.ballLT
  rw [Rewriting.smul_ball, rewriting_formulaOperator, hguardTerms]

private theorem fixedWidthBodyRewriting_eq_embSubsts
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    (Rew.subst (fixedWidthOuterTerms
      tableTerm widthTerm indexTerm valueTerm)).q.comp
        (Rew.emb : Rew ℒₒᵣ Empty 5 Nat 5) =
      Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar]
        exact Rew.q_bvar_zero _
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar,
              Rew.q_bvar_succ, Rew.subst_bvar]
            rfl
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero =>
                rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar,
                  Rew.q_bvar_succ, Rew.subst_bvar]
                rfl
            | succ coordinate =>
                cases coordinate using Fin.cases with
                | zero =>
                    rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar,
                      Rew.q_bvar_succ, Rew.subst_bvar]
                    rfl
                | succ coordinate =>
                    cases coordinate using Fin.cases with
                    | zero =>
                        rw [Rew.comp_app, Rew.emb_bvar, Rew.embSubsts_bvar,
                          Rew.q_bvar_succ, Rew.subst_bvar]
                        rfl
                    | succ coordinate => exact Fin.elim0 coordinate
  · exact Empty.elim coordinate

private theorem rewriting_emb_empty
    {boundArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty boundArity) :
    (Rewriting.emb (ξ := Empty) formula) = formula := by
  change
    (Rew.emb : Rew ℒₒᵣ Empty boundArity Empty boundArity) ▹ formula = formula
  rw [Rew.emb_eq_id]
  exact ReflectiveRewriting.id_app formula

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
    (left right : LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Mul.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

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
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity Nat targetArity)
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
        LO.FirstOrder.Semiformula.Operator.Mem.mem _
    _ = LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
          ![rewriting indexTerm, rewriting valueTerm] := by rw [hterms]
    _ = binaryBitAtomAtTerms (rewriting indexTerm)
          (rewriting valueTerm) :=
      membershipOperator_eq_binaryBitAtomAtTerms _ _

private theorem rewrite_binaryBitAtomAtTerms
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
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

private theorem fixedWidthBodyQ_bvarZero
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
        (#0 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
  rw [Rew.q_bvar_zero, Rew.q_bvar_zero]

private theorem fixedWidthBodyQ_table
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
        (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q (Rew.bShift tableTerm) := by
  change
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
        (#((1 : Fin 5).succ)) = Rew.bShift.q (Rew.bShift tableTerm)
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar, Rew.q_comp_bShift_app]
  rfl

private theorem fixedWidthBodyQ_width
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
        (#3 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q (Rew.bShift widthTerm) := by
  change
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
        (#((2 : Fin 5).succ)) = Rew.bShift.q (Rew.bShift widthTerm)
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar, Rew.q_comp_bShift_app]
  rfl

private theorem fixedWidthBodyQ_index
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
        (#4 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q (Rew.bShift indexTerm) := by
  change
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
        (#((3 : Fin 5).succ)) = Rew.bShift.q (Rew.bShift indexTerm)
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar, Rew.q_comp_bShift_app]
  rfl

private theorem fixedWidthBodyQ_value
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
        (#5 : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q (Rew.bShift valueTerm) := by
  change
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
        (#((4 : Fin 5).succ)) = Rew.bShift.q (Rew.bShift valueTerm)
  rw [Rew.q_bvar_succ, Rew.embSubsts_bvar, Rew.q_comp_bShift_app]
  rfl

private theorem fixedWidthSourceWitnessGuardBody_rewrite
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) ▹
        fixedWidthSourceWitnessGuardBody =
      fixedWidthWitnessGuardBody valueTerm := by
  have hterms :
      Rew.embSubsts
          (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5),
            (‘#4 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 5)] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          (‘!!(Rew.bShift valueTerm) + 1’ :
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
    Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) ▹
        LO.FirstOrder.Semiformula.Operator.LT.lt.operator
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5),
            (‘#4 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 5)] =
      LO.FirstOrder.Semiformula.Operator.LT.lt.operator
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          (‘!!(Rew.bShift valueTerm) + 1’ :
            LO.FirstOrder.ArithmeticSemiterm Nat 1)]
  rw [rewriting_formulaOperator, hterms]

private theorem fixedWidthSourceLengthBody_rewrite
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) ▹
        fixedWidthSourceLengthBody = fixedWidthLengthBody valueTerm := by
  have hterms :
      Rew.embSubsts
          (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5),
            (#4 : LO.FirstOrder.ArithmeticSemiterm Empty 5)] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          Rew.bShift valueTerm] := by
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
      fixedWidthLengthBody valueTerm =
        (Rewriting.emb (ξ := Nat) lengthDef.val) ⇜
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
            Rew.bShift valueTerm] := by
    unfold fixedWidthLengthBody
    rfl
  rw [hsource, htarget, rewriting_embeddedFormulaSubstitution, hterms]

private theorem fixedWidthSourceSizeGuardBody_rewrite
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) ▹
        fixedWidthSourceSizeGuardBody =
      fixedWidthSizeGuardBody widthTerm := by
  have hterms :
      Rew.embSubsts
          (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5),
            (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 5)] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          Rew.bShift widthTerm] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => simp [fixedWidthBodyTerms]
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => simp [fixedWidthBodyTerms]
        | succ coordinate => exact Fin.elim0 coordinate
  change
    Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) ▹
        LO.FirstOrder.Semiformula.Operator.LE.le.operator
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 5), #2] =
      LO.FirstOrder.Semiformula.Operator.LE.le.operator
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
          Rew.bShift widthTerm]
  rw [rewriting_formulaOperator, hterms]

private theorem fixedWidthSourceLeftBitIndexTerm_rewrite
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
        (‘#4 * #3 + #0’ : LO.FirstOrder.ArithmeticSemiterm Empty 6) =
      Rew.bShift.q
        (.func .add ![
          Rew.bShift (fixedWidthIndexWidthTerm widthTerm indexTerm), #0] :
          LO.FirstOrder.ArithmeticSemiterm Nat 1) := by
  rw [arithmeticAddTerm_eq_func, arithmeticMulTerm_eq_func]
  unfold fixedWidthIndexWidthTerm
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  have hmul :
      (Rew.embSubsts
          (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
          (LO.FirstOrder.Semiterm.func Language.Mul.mul ![#4, #3]) =
        Rew.bShift.q
          (Rew.bShift
            (LO.FirstOrder.Semiterm.func Language.Mul.mul
              ![indexTerm, widthTerm])) := by
    calc
      _ = LO.FirstOrder.Semiterm.func Language.Mul.mul ![
          (Rew.embSubsts
            (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q #4,
          (Rew.embSubsts
            (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q #3] :=
        rewrite_binaryFunctionTerm _ _ _ _
      _ = LO.FirstOrder.Semiterm.func Language.Mul.mul ![
            Rew.bShift.q (Rew.bShift indexTerm),
            Rew.bShift.q (Rew.bShift widthTerm)] := by
        rw [fixedWidthBodyQ_index, fixedWidthBodyQ_width]
      _ = Rew.bShift.q
            (LO.FirstOrder.Semiterm.func Language.Mul.mul ![
              Rew.bShift indexTerm, Rew.bShift widthTerm]) :=
        (rewrite_binaryFunctionTerm _ _ _ _).symm
      _ = Rew.bShift.q
            (Rew.bShift
              (LO.FirstOrder.Semiterm.func Language.Mul.mul
                ![indexTerm, widthTerm])) := by
        exact congrArg (fun term => Rew.bShift.q term)
          (rewrite_binaryFunctionTerm Rew.bShift Language.Mul.mul
            indexTerm widthTerm).symm
  calc
    _ = LO.FirstOrder.Semiterm.func Language.Add.add ![
        (Rew.embSubsts
          (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q
          (LO.FirstOrder.Semiterm.func Language.Mul.mul ![#4, #3]),
        (Rew.embSubsts
          (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q #0] :=
      rewrite_binaryFunctionTerm _ _ _ _
    _ = LO.FirstOrder.Semiterm.func Language.Add.add ![
          Rew.bShift.q
            (Rew.bShift
              (LO.FirstOrder.Semiterm.func Language.Mul.mul
                ![indexTerm, widthTerm])),
          Rew.bShift.q (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)] := by
      rw [hmul, fixedWidthBodyQ_bvarZero]
    _ = Rew.bShift.q
          (LO.FirstOrder.Semiterm.func Language.Add.add ![
            Rew.bShift
              (LO.FirstOrder.Semiterm.func Language.Mul.mul
                ![indexTerm, widthTerm]), #0]) :=
      (rewrite_binaryFunctionTerm _ _ _ _).symm

private theorem fixedWidthSourceBitBody_rewrite
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q ▹
        fixedWidthSourceBitBody =
      Rew.bShift.q ▹
        fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm := by
  unfold fixedWidthSourceBitBody fixedWidthBitBody
  change
    (Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q ▹
        (LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
            ![(‘#4 * #3 + #0’ :
                LO.FirstOrder.ArithmeticSemiterm Empty 6), #2] 🡘
          LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
            ![(#0 : LO.FirstOrder.ArithmeticSemiterm Empty 6), #5]) = _
  rw [rewriting_iff, rewrite_membershipOperator,
    rewrite_membershipOperator,
    fixedWidthSourceLeftBitIndexTerm_rewrite,
    fixedWidthBodyQ_table, fixedWidthBodyQ_bvarZero, fixedWidthBodyQ_value,
    ← rewrite_binaryBitAtomAtTerms, ← rewrite_binaryBitAtomAtTerms,
    ← rewriting_iff]

private theorem fixedWidthSourceUniversalBody_rewrite
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) ▹
        fixedWidthSourceUniversalBody =
      liftValuationFormula
        (fixedWidthUniversalFormula
          tableTerm widthTerm indexTerm valueTerm) := by
  have hbound :
      Rew.embSubsts
          (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)
          (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 5) =
        Rew.bShift widthTerm := by
    simp [fixedWidthBodyTerms]
  unfold fixedWidthSourceUniversalBody liftValuationFormula
  unfold fixedWidthUniversalFormula
  calc
    _ = ((Rew.embSubsts
          (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm)).q ▹
          fixedWidthSourceBitBody).ballLT
        (Rew.embSubsts
          (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) #2) :=
      rewriting_ballLT _ _ _
    _ = (Rew.bShift.q ▹
          fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm).ballLT
        (Rew.bShift widthTerm) := by
      rw [fixedWidthSourceBitBody_rewrite, hbound]
    _ = Rew.bShift ▹
        (fixedWidthBitBody
          tableTerm widthTerm indexTerm valueTerm).ballLT widthTerm :=
      (rewriting_ballLT _ _ _).symm

private theorem fixedWidthSourceExistentialBody_rewrite
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    Rew.embSubsts
        (fixedWidthBodyTerms tableTerm widthTerm indexTerm valueTerm) ▹
        fixedWidthSourceExistentialBody =
      compactFixedWidthEntryAtValuationWitnessBody
        tableTerm widthTerm indexTerm valueTerm := by
  unfold fixedWidthSourceExistentialBody
  unfold compactFixedWidthEntryAtValuationWitnessBody
  simp only [LogicalConnective.HomClass.map_and]
  rw [fixedWidthSourceWitnessGuardBody_rewrite,
    fixedWidthSourceLengthBody_rewrite,
    fixedWidthSourceSizeGuardBody_rewrite,
    fixedWidthSourceUniversalBody_rewrite]

/-- The quoted predicate instance and the explicit existential body are
syntactically identical for arbitrary valuation terms. -/
theorem compactFixedWidthEntryAtValuationFormula_alignment
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    compactFixedWidthEntryAtValuationFormula
        tableTerm widthTerm indexTerm valueTerm =
      ∃⁰ compactFixedWidthEntryAtValuationWitnessBody
        tableTerm widthTerm indexTerm valueTerm := by
  unfold compactFixedWidthEntryAtValuationFormula
  rw [compactFixedWidthEntryDef_val_eq_sourceExists]
  change
    Rew.subst (fixedWidthOuterTerms
      tableTerm widthTerm indexTerm valueTerm) ▹
        (Rewriting.emb (ξ := Nat)
          (∃⁰ fixedWidthSourceExistentialBody)) =
      ∃⁰ compactFixedWidthEntryAtValuationWitnessBody
        tableTerm widthTerm indexTerm valueTerm
  simp only [Rewriting.app_exs, Rew.q_emb]
  rw [← TransitiveRewriting.comp_app,
    fixedWidthBodyRewriting_eq_embSubsts,
    fixedWidthSourceExistentialBody_rewrite]

private theorem termValue_paAddTerm
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (paAddTerm left right) =
      termValue valuation left + termValue valuation right := by
  rw [← finiteCaseAddTerm_eq_paAddTerm]
  change
    termValue valuation
        (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]) = _
  exact termValue_add valuation ![left, right]

private theorem termValue_paMulTerm
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (paMulTerm left right) =
      termValue valuation left * termValue valuation right := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  exact termValue_mul valuation ![left, right]

private theorem termValue_paOneTerm (valuation : Nat -> Nat) :
    termValue valuation paOneTerm = 1 := by
  unfold paOneTerm FoundationCompactBinaryNumeralTerm.arithmeticOneTerm
  exact termValue_one valuation ![]

theorem termValue_fixedWidthLeftBitIndexTerm
    (valuation : Nat -> Nat) (widthTerm indexTerm : ValuationTerm)
    (bitIndex : Nat) :
    termValue (extendValuation bitIndex valuation)
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm) =
      termValue valuation indexTerm * termValue valuation widthTerm +
        bitIndex := by
  rw [fixedWidthLeftBitIndexTerm, termValue_paAddTerm,
    termValue_shift, fixedWidthIndexWidthTerm, termValue_paMulTerm]
  rfl

theorem termValue_fixedWidthLeftBitValueTerm
    (valuation : Nat -> Nat) (tableTerm : ValuationTerm)
    (bitIndex : Nat) :
    termValue (extendValuation bitIndex valuation)
        (fixedWidthLeftBitValueTerm tableTerm) =
      termValue valuation tableTerm := by
  rw [fixedWidthLeftBitValueTerm, termValue_shift]

theorem termValue_fixedWidthRightBitIndexTerm
    (valuation : Nat -> Nat) (bitIndex : Nat) :
    termValue (extendValuation bitIndex valuation)
        fixedWidthRightBitIndexTerm = bitIndex := by
  rfl

theorem termValue_fixedWidthRightBitValueTerm
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm)
    (bitIndex : Nat) :
    termValue (extendValuation bitIndex valuation)
        (fixedWidthRightBitValueTerm valueTerm) =
      termValue valuation valueTerm := by
  rw [fixedWidthRightBitValueTerm, termValue_shift]

private theorem free_binaryBitAtomAtTerms
    (indexTerm valueTerm :
      LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    Rewriting.free (binaryBitAtomAtTerms indexTerm valueTerm) =
      binaryBitAtomAtTerms (Rew.free indexTerm)
        (Rew.free valueTerm) :=
  rewrite_binaryBitAtomAtTerms Rew.free indexTerm valueTerm

private theorem free_fixedWidthBitBodyLeftIndex
    (widthTerm indexTerm : ValuationTerm) :
    Rew.free
        (.func .add ![
          Rew.bShift (fixedWidthIndexWidthTerm widthTerm indexTerm), #0] :
          LO.FirstOrder.ArithmeticSemiterm Nat 1) =
      fixedWidthLeftBitIndexTerm widthTerm indexTerm := by
  change
    Rew.free
        (LO.FirstOrder.Semiterm.func Language.Add.add ![
          Rew.bShift (fixedWidthIndexWidthTerm widthTerm indexTerm), #0]) = _
  calc
    _ = finiteCaseAddTerm
          (Rew.free
            (Rew.bShift (fixedWidthIndexWidthTerm widthTerm indexTerm)))
          (Rew.free (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)) := by
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
          (Rew.shift (fixedWidthIndexWidthTerm widthTerm indexTerm)) (&0) := by
      rw [free_bShift_term]
      rfl
    _ = paAddTerm
          (Rew.shift (fixedWidthIndexWidthTerm widthTerm indexTerm)) (&0) :=
      finiteCaseAddTerm_eq_paAddTerm _ _
    _ = fixedWidthLeftBitIndexTerm widthTerm indexTerm := rfl

private theorem fixedWidthBitBody_free
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    Rewriting.free
        (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm) =
      (binaryBitAtomAtTerms
          (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
          (fixedWidthLeftBitValueTerm tableTerm) 🡘
        binaryBitAtomAtTerms fixedWidthRightBitIndexTerm
          (fixedWidthRightBitValueTerm valueTerm)) := by
  unfold fixedWidthBitBody
  rw [rewriting_iff, free_binaryBitAtomAtTerms,
    free_binaryBitAtomAtTerms, free_fixedWidthBitBodyLeftIndex,
    free_bShift_term, free_bShift_term]
  rfl

theorem fixedWidthWitnessGuard_size_le_value
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    Nat.size (termValue valuation valueTerm) ≤
      termValue valuation valueTerm := by
  let value := termValue valuation valueTerm
  have hlength := LO.FirstOrder.Arithmetic.length_le (V := Nat) value
  have hlengthEq : (‖value‖ : Nat) =
      LO.FirstOrder.Arithmetic.binaryLength value := rfl
  rw [hlengthEq, binaryLength_nat_eq_size] at hlength
  exact (foundationNatLE_iff_standard (Nat.size value) value).mp hlength

noncomputable def fixedWidthWitnessGuardHybridCertificate
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    let size := Nat.size (termValue valuation valueTerm)
    FixedWidthHybridCertificate valuation
      (fixedWidthWitnessGuard size valueTerm) := by
  let value := termValue valuation valueTerm
  let size := Nat.size value
  have hsizeValue : size ≤ value :=
    fixedWidthWitnessGuard_size_le_value valuation valueTerm
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm size,
        (‘!!valueTerm + 1’ : ValuationTerm)] (by
        change termValue valuation (shortBinaryNumeralTerm size) <
          termValue valuation (paAddTerm valueTerm paOneTerm)
        rw [termValue_shortBinaryNumeralTerm, termValue_paAddTerm,
          termValue_paOneTerm]
        exact Nat.lt_succ_of_le hsizeValue)
  exact .cast (by
    unfold fixedWidthWitnessGuard size
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

noncomputable def fixedWidthLengthHybridCertificate
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    let size := Nat.size (termValue valuation valueTerm)
    FixedWidthHybridCertificate valuation
      (fixedWidthLengthFormula size valueTerm) := by
  let size := Nat.size (termValue valuation valueTerm)
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.binaryLength
      valuation (shortBinaryNumeralTerm size) valueTerm (by
        simp [size, termValue_shortBinaryNumeralTerm])
  simpa [fixedWidthLengthFormula] using direct

noncomputable def fixedWidthSizeGuardHybridCertificate
    (valuation : Nat -> Nat) (widthTerm valueTerm : ValuationTerm)
    (hsize : Nat.size (termValue valuation valueTerm) ≤
      termValue valuation widthTerm) :
    let size := Nat.size (termValue valuation valueTerm)
    FixedWidthHybridCertificate valuation
      (fixedWidthSizeGuard size widthTerm) := by
  let size := Nat.size (termValue valuation valueTerm)
  let sizeTerm : ValuationTerm := shortBinaryNumeralTerm size
  if hequal : size = termValue valuation widthTerm then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        valuation Language.Eq.eq ![sizeTerm, widthTerm] (by
          change termValue valuation sizeTerm = termValue valuation widthTerm
          simpa [sizeTerm, size, termValue_shortBinaryNumeralTerm]
            using hequal)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
          ![sizeTerm, widthTerm]) equality
    exact .cast (by
      unfold fixedWidthSizeGuard sizeTerm
      exact (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm) direct
  else
    let hstrict := Nat.lt_of_le_of_ne hsize hequal
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        valuation Language.ORing.Rel.lt ![sizeTerm, widthTerm] (by
          change termValue valuation sizeTerm < termValue valuation widthTerm
          simpa [sizeTerm, size, termValue_shortBinaryNumeralTerm]
            using hstrict)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![sizeTerm, widthTerm]) strict
    exact .cast (by
      unfold fixedWidthSizeGuard sizeTerm
      exact (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm) direct

private theorem fixedWidthLeftBitHybridVariables
    (widthTerm indexTerm tableTerm : ValuationTerm) :
    let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
    let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
    leftIndexTerm.freeVariables ∪ leftValueTerm.freeVariables ⊆
      (binaryBitAtValuationFormula true
        leftIndexTerm leftValueTerm).freeVariables := by
  simpa [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
    binaryBitAtomAtTerms,
    FoundationCompactPAFastArithmeticLeafRecognizer.bitInstance] using
      bitInstance_argument_freeVariables_union_subset
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
        (fixedWidthLeftBitValueTerm tableTerm)

private theorem fixedWidthRightBitHybridVariables
    (valueTerm : ValuationTerm) :
    fixedWidthRightBitIndexTerm.freeVariables ∪
        (fixedWidthRightBitValueTerm valueTerm).freeVariables ⊆
      (binaryBitAtValuationFormula true fixedWidthRightBitIndexTerm
        (fixedWidthRightBitValueTerm valueTerm)).freeVariables := by
  simpa [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
    binaryBitAtomAtTerms,
    FoundationCompactPAFastArithmeticLeafRecognizer.bitInstance] using
      bitInstance_argument_freeVariables_union_subset
        fixedWidthRightBitIndexTerm
        (fixedWidthRightBitValueTerm valueTerm)

private theorem binaryBitFalse_freeVariables_eq_true
    (indexTerm valueTerm : ValuationTerm) :
    (binaryBitAtValuationFormula false indexTerm valueTerm).freeVariables =
      (binaryBitAtValuationFormula true indexTerm valueTerm).freeVariables := by
  simp [binaryBitAtValuationFormula, binaryBitLiteralAtTerms]

noncomputable def fixedWidthBitHybridCertificate
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (hbit : (termValue valuation tableTerm).testBit
        (termValue valuation indexTerm * termValue valuation widthTerm +
          bitIndex) =
      (termValue valuation valueTerm).testBit bitIndex) :
    FixedWidthHybridCertificate (extendValuation bitIndex valuation)
      (Rewriting.free
        (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm)) := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
  let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
  let expected := (termValue valuation valueTerm).testBit bitIndex
  have hleftValue :
      (termValue branchValuation leftValueTerm).testBit
          (termValue branchValuation leftIndexTerm) = expected := by
    simpa [branchValuation, leftValueTerm, leftIndexTerm, expected,
      termValue_fixedWidthLeftBitValueTerm,
      termValue_fixedWidthLeftBitIndexTerm] using hbit
  have hrightValue :
      (termValue branchValuation rightValueTerm).testBit
          (termValue branchValuation rightIndexTerm) = expected := by
    simp [branchValuation, rightValueTerm, rightIndexTerm, expected,
      termValue_fixedWidthRightBitValueTerm,
      termValue_fixedWidthRightBitIndexTerm]
  have hleftVariablesTrue :
      leftIndexTerm.freeVariables ∪ leftValueTerm.freeVariables ⊆
        (binaryBitAtValuationFormula true
          leftIndexTerm leftValueTerm).freeVariables := by
    simpa [leftIndexTerm, leftValueTerm] using
      fixedWidthLeftBitHybridVariables widthTerm indexTerm tableTerm
  have hrightVariablesTrue :
      rightIndexTerm.freeVariables ∪ rightValueTerm.freeVariables ⊆
        (binaryBitAtValuationFormula true
          rightIndexTerm rightValueTerm).freeVariables := by
    simpa [rightIndexTerm, rightValueTerm] using
      fixedWidthRightBitHybridVariables valueTerm
  if hexpected : expected = true then
      let leftTrue :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
          branchValuation leftIndexTerm leftValueTerm
          (by simpa [hexpected] using hleftValue) hleftVariablesTrue
      let rightTrue :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
          branchValuation rightIndexTerm rightValueTerm
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
        exact (fixedWidthBitBody_free
          tableTerm widthTerm indexTerm valueTerm).symm) source
  else
      have hexpectedFalse : expected = false := by
        cases h : expected <;> simp_all
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
          branchValuation leftIndexTerm leftValueTerm
          (by simpa [hexpectedFalse] using hleftValue) hleftVariablesFalse
      let rightFalse :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
          branchValuation rightIndexTerm rightValueTerm
          (by simpa [hexpectedFalse] using hrightValue) hrightVariablesFalse
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
        exact (fixedWidthBitBody_free
          tableTerm widthTerm indexTerm valueTerm).symm) source

noncomputable def fixedWidthBitHybridBranches
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitCount : Nat)
    (hbits : ∀ bitIndex < bitCount,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    FixedWidthHybridBranches valuation
      (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm)
      bitCount := by
  induction bitCount with
  | zero => exact .nil valuation _
  | succ previous inductionHypothesis =>
      let initial := inductionHypothesis (fun bitIndex hindex =>
        hbits bitIndex (Nat.lt_trans hindex (Nat.lt_succ_self previous)))
      let last := fixedWidthBitHybridCertificate valuation
        tableTerm widthTerm indexTerm valueTerm previous
        (hbits previous (Nat.lt_succ_self previous))
      exact .snoc initial last

noncomputable def fixedWidthUniversalHybridCertificate
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    FixedWidthHybridCertificate valuation
      (fixedWidthUniversalFormula
        tableTerm widthTerm indexTerm valueTerm) := by
  let branches := fixedWidthBitHybridBranches valuation
    tableTerm widthTerm indexTerm valueTerm
    (termValue valuation widthTerm) hbits
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      widthTerm (fixedWidthBitBody
        tableTerm widthTerm indexTerm valueTerm) branches
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm)
        (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm)) =
        fixedWidthUniversalFormula
          tableTerm widthTerm indexTerm valueTerm
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- The four checked components after installing the binary-size witness. -/
noncomputable def compactFixedWidthEntryAtValuationPostWitnessHybridCertificate
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) :
    let size := Nat.size (termValue valuation valueTerm)
    FixedWidthHybridCertificate valuation
      (compactFixedWidthEntryAtValuationPostWitnessFormula
        tableTerm widthTerm indexTerm valueTerm size) := by
  let size := Nat.size (termValue valuation valueTerm)
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (fixedWidthWitnessGuardHybridCertificate valuation valueTerm)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (fixedWidthLengthHybridCertificate valuation valueTerm)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (fixedWidthSizeGuardHybridCertificate
          valuation widthTerm valueTerm hentry.1)
        (fixedWidthUniversalHybridCertificate valuation
          tableTerm widthTerm indexTerm valueTerm hentry.2)))

/-- Explicit hybrid certificate for a quoted fixed-width entry at arbitrary
valuation terms.  The installed witness is
`Nat.size (termValue valuation valueTerm)`. -/
noncomputable def compactFixedWidthEntryAtValuationExplicitHybridCertificate
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) :
    FixedWidthHybridCertificate valuation
      (compactFixedWidthEntryAtValuationFormula
        tableTerm widthTerm indexTerm valueTerm) := by
  let size := Nat.size (termValue valuation valueTerm)
  let body := compactFixedWidthEntryAtValuationWitnessBody
    tableTerm widthTerm indexTerm valueTerm
  let post := compactFixedWidthEntryAtValuationPostWitnessHybridCertificate
    valuation tableTerm widthTerm indexTerm valueTerm hentry
  let instantiated :=
    CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactFixedWidthEntryAtValuationWitnessBody_subst
      tableTerm widthTerm indexTerm valueTerm size).symm post
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.existsWitness
      body size instantiated
  exact .cast
    (compactFixedWidthEntryAtValuationFormula_alignment
      tableTerm widthTerm indexTerm valueTerm).symm direct

/-- Compile the explicit certificate in its exact valuation context. -/
noncomputable def compileCompactFixedWidthEntryAtValuationExplicitHybridContext
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) :
    CertifiedPAContextProof
      (valuationContext
        (compactFixedWidthEntryAtValuationFormula
          tableTerm widthTerm indexTerm valueTerm).freeVariables valuation)
      (compactFixedWidthEntryAtValuationFormula
        tableTerm widthTerm indexTerm valueTerm) :=
  (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
    tableTerm widthTerm indexTerm valueTerm hentry).compile

/-- Proof-free structural payload resource for the open-term certificate. -/
noncomputable def compactFixedWidthEntryAtValuationExplicitHybridFormulaStructuralPayloadBound
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm indexTerm valueTerm hentry)

theorem compileCompactFixedWidthEntryAtValuationExplicitHybridContext_payloadLength_le
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (hentry : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm)) :
    (compileCompactFixedWidthEntryAtValuationExplicitHybridContext valuation
      tableTerm widthTerm indexTerm valueTerm hentry).payloadLength ≤
      compactFixedWidthEntryAtValuationExplicitHybridFormulaStructuralPayloadBound
        valuation tableTerm widthTerm indexTerm valueTerm hentry := by
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
        tableTerm widthTerm indexTerm valueTerm hentry)

/-- The zero valuation used by the token-stream index specializations. -/
def zeroValuation : Nat -> Nat := fun _ => 0

@[simp] theorem termValue_indexTerm_bvarZero_under_extendValuation
    (index : Nat) :
    termValue (extendValuation index zeroValuation) (&0 : ValuationTerm) =
      index := by
  rfl

@[simp] theorem termValue_indexTerm_bvarZeroAddOne_under_extendValuation
    (index : Nat) :
    termValue (extendValuation index zeroValuation)
        (‘&0 + 1’ : ValuationTerm) = index + 1 := by
  change termValue (extendValuation index zeroValuation)
      (paAddTerm (&0) paOneTerm) = index + 1
  rw [termValue_paAddTerm, termValue_paOneTerm]
  rfl

#check compactFixedWidthEntryAtValuationExplicitHybridCertificate
#check termValue_indexTerm_bvarZero_under_extendValuation
#check termValue_indexTerm_bvarZeroAddOne_under_extendValuation

#print axioms compactFixedWidthEntryAtValuationExplicitHybridCertificate
#print axioms compileCompactFixedWidthEntryAtValuationExplicitHybridContext
#print axioms compileCompactFixedWidthEntryAtValuationExplicitHybridContext_payloadLength_le

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
