import integration.FoundationCompactNumericListedDirectNatListAtRows
import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for one natural-list row lookup

The two boundary cursors remain explicit bounded witnesses.  Their fixed-width
entries and the intervening token cell are certified directly from the
semantic lookup graph; no bounded-formula truth selector is used.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

abbrev zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      (Rewriting.app right :
        ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
          ArithmeticSemiformula targetVariables targetArity) := by
  cases h
  rfl

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
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

private theorem rewriting_emptyFormulaSubstitution
    {targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Empty sourceArity targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity -> ArithmeticSemiterm Empty sourceArity) :
    rewriting ▹ (formula ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      rewriting.comp (Rew.subst terms) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ (formula ⇜ terms) =
        (rewriting.comp (Rew.subst terms)) ▹ formula := by
      rw [TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

@[simp] private theorem rewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

private def natListAtSuccessorTerm (index : Nat) : ValuationTerm :=
  ‘!!(shortBinaryNumeralTerm index) + 1’

private def natListAtOuterTerms
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm boundaryTable,
    shortBinaryNumeralTerm count,
    shortBinaryNumeralTerm index,
    shortBinaryNumeralTerm value]

private def natListAtDepthOneTerms
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    Fin 8 -> ArithmeticSemiterm Nat 1 :=
  ![#0,
    closedShift 1 (shortBinaryNumeralTerm tokenTable),
    closedShift 1 (shortBinaryNumeralTerm width),
    closedShift 1 (shortBinaryNumeralTerm tokenCount),
    closedShift 1 (shortBinaryNumeralTerm boundaryTable),
    closedShift 1 (shortBinaryNumeralTerm count),
    closedShift 1 (shortBinaryNumeralTerm index),
    closedShift 1 (shortBinaryNumeralTerm value)]

private def natListAtDepthTwoTerms
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    Fin 9 -> ArithmeticSemiterm Nat 2 :=
  ![#0, #1,
    closedShift 2 (shortBinaryNumeralTerm tokenTable),
    closedShift 2 (shortBinaryNumeralTerm width),
    closedShift 2 (shortBinaryNumeralTerm tokenCount),
    closedShift 2 (shortBinaryNumeralTerm boundaryTable),
    closedShift 2 (shortBinaryNumeralTerm count),
    closedShift 2 (shortBinaryNumeralTerm index),
    closedShift 2 (shortBinaryNumeralTerm value)]

private theorem natListAtOuterRewriting_eq_embSubsts
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    (Rew.subst (natListAtOuterTerms tokenTable width tokenCount boundaryTable
      count index value)).comp
        (Rew.emb : Rew ℒₒᵣ Empty 7 Nat 7) =
      Rew.embSubsts (natListAtOuterTerms tokenTable width tokenCount
        boundaryTable count index value) := by
  ext coordinate
  · simp [Rew.comp_app]
  · exact Empty.elim coordinate

private theorem natListAtOuterQ1_eq_embSubsts
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    (Rew.embSubsts (natListAtOuterTerms tokenTable width tokenCount
      boundaryTable count index value)).q =
      Rew.embSubsts (natListAtDepthOneTerms tokenTable width tokenCount
        boundaryTable count index value) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListAtOuterTerms, natListAtDepthOneTerms, closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListAtOuterQ2_eq_embSubsts
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    (Rew.embSubsts (natListAtOuterTerms tokenTable width tokenCount
      boundaryTable count index value)).q.q =
      Rew.embSubsts (natListAtDepthTwoTerms tokenTable width tokenCount
        boundaryTable count index value) := by
  rw [natListAtOuterQ1_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListAtDepthOneTerms, natListAtDepthTwoTerms, closedShift, Rew.q]
  · exact Empty.elim coordinate

/-- The original seven-coordinate lookup formula closed by short numerals. -/
def compactAdditiveNatListAtRowsClosedFormula
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListAtRowsDef.val) ⇜
    natListAtOuterTerms tokenTable width tokenCount boundaryTable count index
      value

/-- The conjunction before the two bounded cursor witnesses close. -/
def compactAdditiveNatListAtRowsTerminal
    (tokenTable width tokenCount boundaryTable index value : Nat) :
    ArithmeticSemiformula Nat 2 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm boundaryTable),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (shortBinaryNumeralTerm index),
        (#1 : ArithmeticSemiterm Nat 2)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm boundaryTable),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          closedShift 2 (natListAtSuccessorTerm index),
          (#0 : ArithmeticSemiterm Nat 2)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
          closedShift 2 (shortBinaryNumeralTerm width),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          (#1 : ArithmeticSemiterm Nat 2),
          closedShift 2 (shortBinaryNumeralTerm value),
          (#0 : ArithmeticSemiterm Nat 2)]))

def compactAdditiveNatListAtRowsWitnessBody
    (tokenTable width tokenCount boundaryTable index value : Nat) :
    ValuationFormula :=
  ((compactAdditiveNatListAtRowsTerminal tokenTable width tokenCount
      boundaryTable index value).bexsLTSucc
        (closedShift 1 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (shortBinaryNumeralTerm tokenCount)

def compactAdditiveNatListAtRowsExplicitFormula
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm index) <
      !!(shortBinaryNumeralTerm count)” ⋏
    compactAdditiveNatListAtRowsWitnessBody tokenTable width tokenCount
      boundaryTable index value

private def natListAtSourceTerminal : ArithmeticSemiformula Empty 9 :=
  (compactFixedWidthEntryDef.val ⇜
      ![(#5 : ArithmeticSemiterm Empty 9), #4, #7, #1]) ⋏
    ((compactFixedWidthEntryDef.val ⇜
        ![(#5 : ArithmeticSemiterm Empty 9), #4, ‘#7 + 1’, #0]) ⋏
      (compactAdditiveTokenCellDef.val ⇜
        ![(#2 : ArithmeticSemiterm Empty 9), #3, #4, #1, #8, #0]))

private def natListAtSourceWitnessBody : ArithmeticSemiformula Empty 7 :=
  (natListAtSourceTerminal.bexsLTSucc
      (#3 : ArithmeticSemiterm Empty 8)).bexsLTSucc
    (#2 : ArithmeticSemiterm Empty 7)

private def natListAtSourceDecomposedFormula : ArithmeticSemiformula Empty 7 :=
  (“#5 < #4” : ArithmeticSemiformula Empty 7) ⋏
    natListAtSourceWitnessBody

private theorem compactAdditiveNatListAtRowsDef_val_eq_sourceDecomposed :
    compactAdditiveNatListAtRowsDef.val =
      natListAtSourceDecomposedFormula := by
  unfold compactAdditiveNatListAtRowsDef
  unfold natListAtSourceDecomposedFormula natListAtSourceWitnessBody
    natListAtSourceTerminal
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

private theorem natListAtSourceGuard_rewrite
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    Rew.embSubsts (natListAtOuterTerms tokenTable width tokenCount
        boundaryTable count index value) ▹
        (“#5 < #4” : ArithmeticSemiformula Empty 7) =
      “!!(shortBinaryNumeralTerm index) <
        !!(shortBinaryNumeralTerm count)” := by
  simp [natListAtOuterTerms]

private theorem natListAtSourceTerminal_rewrite
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    Rew.embSubsts (natListAtDepthTwoTerms tokenTable width tokenCount
        boundaryTable count index value) ▹ natListAtSourceTerminal =
      compactAdditiveNatListAtRowsTerminal tokenTable width tokenCount
        boundaryTable index value := by
  unfold natListAtSourceTerminal compactAdditiveNatListAtRowsTerminal
  simp [rewriting_emptyFormulaSubstitution,
    natListAtDepthTwoTerms, natListAtSuccessorTerm, closedShift,
    Function.comp_def]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;> simp

private theorem natListAtSourceWitnessBody_rewrite
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    Rew.embSubsts (natListAtOuterTerms tokenTable width tokenCount
        boundaryTable count index value) ▹ natListAtSourceWitnessBody =
      compactAdditiveNatListAtRowsWitnessBody tokenTable width tokenCount
        boundaryTable index value := by
  unfold natListAtSourceWitnessBody
  unfold compactAdditiveNatListAtRowsWitnessBody
  rw [rewriting_bexsLTSucc, rewriting_bexsLTSucc]
  rw [natListAtOuterQ2_eq_embSubsts, natListAtSourceTerminal_rewrite,
    natListAtOuterQ1_eq_embSubsts]
  simp [natListAtOuterTerms, natListAtDepthOneTerms, closedShift]

/-- Exact syntax alignment with the original quoted lookup graph. -/
theorem compactAdditiveNatListAtRowsClosedFormula_alignment
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    compactAdditiveNatListAtRowsClosedFormula tokenTable width tokenCount
        boundaryTable count index value =
      compactAdditiveNatListAtRowsExplicitFormula tokenTable width tokenCount
        boundaryTable count index value := by
  unfold compactAdditiveNatListAtRowsClosedFormula
  change Rew.subst
      (natListAtOuterTerms tokenTable width tokenCount boundaryTable count
        index value) ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 7 Nat 7) ▹
        compactAdditiveNatListAtRowsDef.val) = _
  rw [← TransitiveRewriting.comp_app,
    natListAtOuterRewriting_eq_embSubsts]
  rw [compactAdditiveNatListAtRowsDef_val_eq_sourceDecomposed]
  unfold natListAtSourceDecomposedFormula
  unfold compactAdditiveNatListAtRowsExplicitFormula
  simp only [LogicalConnective.HomClass.map_and]
  rw [natListAtSourceGuard_rewrite,
    natListAtSourceWitnessBody_rewrite]

private theorem substitute_closedShift
    {k : Nat} (values : Fin k -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
        apply Rew.ext
        · intro coordinate
          exact Fin.elim0 coordinate
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ k ih =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun coordinate : Fin k => values coordinate.succ) := by
        apply Rew.ext
        · intro coordinate
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (closedShift (k + 1) term) =
            ((Rew.subst values).comp Rew.bShift) (closedShift k term) := by
              simp [closedShift, Rew.comp_app]
        _ = Rew.subst (fun coordinate : Fin k => values coordinate.succ)
              (closedShift k term) := by rw [hrew]
        _ = term := ih _

theorem explicitBoundedWitnessFormula_two_eq
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 2) :
    explicitBoundedWitnessFormula bound 2 body =
      (body.bexsLTSucc (closedShift 1 bound)).bexsLTSucc bound := by
  rfl

theorem compactAdditiveNatListAtRowsTerminal_substitution_alignment
    (tokenTable width tokenCount boundaryTable index value left right : Nat) :
    (compactAdditiveNatListAtRowsTerminal tokenTable width tokenCount
        boundaryTable index value) ⇜
        ![shortBinaryNumeralTerm right, shortBinaryNumeralTerm left] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm index)
          (shortBinaryNumeralTerm left) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (natListAtSuccessorTerm index)
            (shortBinaryNumeralTerm right) ⋏
          compactAdditiveTokenCellClosedFormula
            tokenTable width tokenCount left value right)) := by
  unfold compactAdditiveNatListAtRowsTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactAdditiveTokenCellClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def strictCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hstrict : termValue zeroValuation leftTerm <
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm < !!rightTerm” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hstrict
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

/-- Build the exact closed lookup certificate from its semantic graph. -/
noncomputable def compactAdditiveNatListAtRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (hrows : CompactAdditiveNatListAtRows tokenTable width tokenCount
      boundaryTable count index value) :
    HybridCertificate
      (compactAdditiveNatListAtRowsClosedFormula tokenTable width tokenCount
        boundaryTable count index value) := by
  let leftExists := hrows.2
  let left := Classical.choose leftExists
  have hleftData := Classical.choose_spec leftExists
  let rightExists := hleftData.2
  let right := Classical.choose rightExists
  have hrightData := Classical.choose_spec rightExists
  have hindex := hrows.1
  have hleft := hleftData.1
  have hright := hrightData.1
  have hleftEntry := hrightData.2.1
  have hrightEntry := hrightData.2.2.1
  have hcell := hrightData.2.2.2
  let values : Fin 2 -> Nat := ![right, left]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm right,
          shortBinaryNumeralTerm left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm index)
        (shortBinaryNumeralTerm left) (by
          simpa [termValue_shortBinaryNumeralTerm] using hleftEntry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (natListAtSuccessorTerm index)
          (shortBinaryNumeralTerm right) (by
            simpa [natListAtSuccessorTerm,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne]
              using hrightEntry))
        (compactAdditiveTokenCellExplicitHybridCertificate
          tokenTable width tokenCount left value right hcell))
  let terminal : HybridCertificate
      ((compactAdditiveNatListAtRowsTerminal tokenTable width tokenCount
          boundaryTable index value) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListAtRowsTerminal_substitution_alignment
          tokenTable width tokenCount boundaryTable index value left right).symm)
      terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveNatListAtRowsTerminal tokenTable width tokenCount
      boundaryTable index value)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact hright
      · exact hleft) terminal
  let body : HybridCertificate
      (compactAdditiveNatListAtRowsWitnessBody tokenTable width tokenCount
        boundaryTable index value) :=
    .cast (by
      rw [explicitBoundedWitnessFormula_two_eq]
      rfl) installed
  let guard := strictCertificate
    (shortBinaryNumeralTerm index) (shortBinaryNumeralTerm count) (by
      simpa [termValue_shortBinaryNumeralTerm] using hindex)
  rw [compactAdditiveNatListAtRowsClosedFormula_alignment]
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction guard body

/-! ## Exact index-term endpoint

The source lookup graph accepts an arbitrary arithmetic term in its index
coordinate.  This endpoint preserves that term syntactically and relates it
to the semantic index only through its value under `zeroValuation`.
-/

def natListAtSuccessorTermAtValuationIndex
    (indexTerm : ValuationTerm) : ValuationTerm :=
  ‘!!indexTerm + 1’

private def natListAtOuterTermsAtValuationIndex
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) : Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm boundaryTable,
    shortBinaryNumeralTerm count,
    indexTerm,
    shortBinaryNumeralTerm value]

private def natListAtDepthOneTermsAtValuationIndex
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) :
    Fin 8 -> ArithmeticSemiterm Nat 1 :=
  ![#0,
    closedShift 1 (shortBinaryNumeralTerm tokenTable),
    closedShift 1 (shortBinaryNumeralTerm width),
    closedShift 1 (shortBinaryNumeralTerm tokenCount),
    closedShift 1 (shortBinaryNumeralTerm boundaryTable),
    closedShift 1 (shortBinaryNumeralTerm count),
    closedShift 1 indexTerm,
    closedShift 1 (shortBinaryNumeralTerm value)]

private def natListAtDepthTwoTermsAtValuationIndex
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) :
    Fin 9 -> ArithmeticSemiterm Nat 2 :=
  ![#0, #1,
    closedShift 2 (shortBinaryNumeralTerm tokenTable),
    closedShift 2 (shortBinaryNumeralTerm width),
    closedShift 2 (shortBinaryNumeralTerm tokenCount),
    closedShift 2 (shortBinaryNumeralTerm boundaryTable),
    closedShift 2 (shortBinaryNumeralTerm count),
    closedShift 2 indexTerm,
    closedShift 2 (shortBinaryNumeralTerm value)]

private theorem natListAtOuterAtValuationIndexRewriting_eq_embSubsts
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) :
    (Rew.subst (natListAtOuterTermsAtValuationIndex tokenTable width tokenCount
      boundaryTable count value indexTerm)).comp
        (Rew.emb : Rew ℒₒᵣ Empty 7 Nat 7) =
      Rew.embSubsts (natListAtOuterTermsAtValuationIndex tokenTable width
        tokenCount boundaryTable count value indexTerm) := by
  ext coordinate
  · simp [Rew.comp_app]
  · exact Empty.elim coordinate

private theorem natListAtOuterAtValuationIndexQ1_eq_embSubsts
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) :
    (Rew.embSubsts (natListAtOuterTermsAtValuationIndex tokenTable width
      tokenCount boundaryTable count value indexTerm)).q =
      Rew.embSubsts (natListAtDepthOneTermsAtValuationIndex tokenTable width
        tokenCount boundaryTable count value indexTerm) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListAtOuterTermsAtValuationIndex,
        natListAtDepthOneTermsAtValuationIndex, closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListAtOuterAtValuationIndexQ2_eq_embSubsts
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) :
    (Rew.embSubsts (natListAtOuterTermsAtValuationIndex tokenTable width
      tokenCount boundaryTable count value indexTerm)).q.q =
      Rew.embSubsts (natListAtDepthTwoTermsAtValuationIndex tokenTable width
        tokenCount boundaryTable count value indexTerm) := by
  rw [natListAtOuterAtValuationIndexQ1_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListAtDepthOneTermsAtValuationIndex,
        natListAtDepthTwoTermsAtValuationIndex, closedShift, Rew.q]
  · exact Empty.elim coordinate

/-- The original lookup graph with the caller's exact index term. -/
def compactAdditiveNatListAtRowsAtValuationIndexFormula
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListAtRowsDef.val) ⇜
    natListAtOuterTermsAtValuationIndex tokenTable width tokenCount
      boundaryTable count value indexTerm

theorem compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) :
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount boundaryTable count value indexTerm =
      (Rewriting.emb (ξ := Nat) compactAdditiveNatListAtRowsDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm boundaryTable,
          shortBinaryNumeralTerm count,
          indexTerm,
          shortBinaryNumeralTerm value] := by
  rfl

def compactAdditiveNatListAtRowsTerminalAtValuationIndex
    (tokenTable width tokenCount boundaryTable value : Nat)
    (indexTerm : ValuationTerm) : ArithmeticSemiformula Nat 2 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm boundaryTable),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 indexTerm,
        (#1 : ArithmeticSemiterm Nat 2)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm boundaryTable),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          closedShift 2
            (natListAtSuccessorTermAtValuationIndex indexTerm),
          (#0 : ArithmeticSemiterm Nat 2)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
          closedShift 2 (shortBinaryNumeralTerm width),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          (#1 : ArithmeticSemiterm Nat 2),
          closedShift 2 (shortBinaryNumeralTerm value),
          (#0 : ArithmeticSemiterm Nat 2)]))

def compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex
    (tokenTable width tokenCount boundaryTable value : Nat)
    (indexTerm : ValuationTerm) : ValuationFormula :=
  ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value indexTerm).bexsLTSucc
        (closedShift 1 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (shortBinaryNumeralTerm tokenCount)

def compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndex
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) : ValuationFormula :=
  “!!indexTerm < !!(shortBinaryNumeralTerm count)” ⋏
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
      tokenCount boundaryTable value indexTerm

private theorem natListAtSourceGuardAtValuationIndex_rewrite
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) :
    Rew.embSubsts (natListAtOuterTermsAtValuationIndex tokenTable width
        tokenCount boundaryTable count value indexTerm) ▹
        (“#5 < #4” : ArithmeticSemiformula Empty 7) =
      “!!indexTerm < !!(shortBinaryNumeralTerm count)” := by
  simp [natListAtOuterTermsAtValuationIndex]

private theorem natListAtSourceTerminalAtValuationIndex_rewrite
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) :
    Rew.embSubsts (natListAtDepthTwoTermsAtValuationIndex tokenTable width
        tokenCount boundaryTable count value indexTerm) ▹
        natListAtSourceTerminal =
      compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm := by
  unfold natListAtSourceTerminal
    compactAdditiveNatListAtRowsTerminalAtValuationIndex
  simp [rewriting_emptyFormulaSubstitution,
    natListAtDepthTwoTermsAtValuationIndex,
    natListAtSuccessorTermAtValuationIndex, closedShift,
    Function.comp_def]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;> simp

private theorem natListAtSourceWitnessBodyAtValuationIndex_rewrite
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) :
    Rew.embSubsts (natListAtOuterTermsAtValuationIndex tokenTable width
        tokenCount boundaryTable count value indexTerm) ▹
        natListAtSourceWitnessBody =
      compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm := by
  unfold natListAtSourceWitnessBody
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex
  rw [rewriting_bexsLTSucc, rewriting_bexsLTSucc]
  rw [natListAtOuterAtValuationIndexQ2_eq_embSubsts,
    natListAtSourceTerminalAtValuationIndex_rewrite,
    natListAtOuterAtValuationIndexQ1_eq_embSubsts]
  simp [natListAtOuterTermsAtValuationIndex,
    natListAtDepthOneTermsAtValuationIndex, closedShift]

theorem compactAdditiveNatListAtRowsAtValuationIndexFormula_alignment
    (tokenTable width tokenCount boundaryTable count value : Nat)
    (indexTerm : ValuationTerm) :
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount boundaryTable count value indexTerm =
      compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndex tokenTable
        width tokenCount boundaryTable count value indexTerm := by
  unfold compactAdditiveNatListAtRowsAtValuationIndexFormula
  change Rew.subst
      (natListAtOuterTermsAtValuationIndex tokenTable width tokenCount
        boundaryTable count value indexTerm) ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 7 Nat 7) ▹
        compactAdditiveNatListAtRowsDef.val) = _
  rw [← TransitiveRewriting.comp_app,
    natListAtOuterAtValuationIndexRewriting_eq_embSubsts]
  rw [compactAdditiveNatListAtRowsDef_val_eq_sourceDecomposed]
  unfold natListAtSourceDecomposedFormula
    compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndex
  simp only [LogicalConnective.HomClass.map_and]
  rw [natListAtSourceGuardAtValuationIndex_rewrite,
    natListAtSourceWitnessBodyAtValuationIndex_rewrite]

theorem
    compactAdditiveNatListAtRowsTerminalAtValuationIndex_substitution_alignment
    (tokenTable width tokenCount boundaryTable value left right : Nat)
    (indexTerm : ValuationTerm) :
    (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm) ⇜
        ![shortBinaryNumeralTerm right, shortBinaryNumeralTerm left] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          indexTerm
          (shortBinaryNumeralTerm left) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (natListAtSuccessorTermAtValuationIndex indexTerm)
            (shortBinaryNumeralTerm right) ⋏
          compactAdditiveTokenCellClosedFormula
            tokenTable width tokenCount left value right)) := by
  unfold compactAdditiveNatListAtRowsTerminalAtValuationIndex
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactAdditiveTokenCellClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate

/-- Build the exact lookup certificate while preserving the caller's index
term in the checked syntax tree. -/
structure CompactAdditiveNatListAtRowData
    (tokenTable width tokenCount boundaryTable index value : Nat) where
  left : Nat
  right : Nat
  left_le : left ≤ tokenCount
  right_le : right ≤ tokenCount
  left_entry : CompactFixedWidthEntry boundaryTable tokenCount index left
  right_entry : CompactFixedWidthEntry boundaryTable tokenCount (index + 1)
    right
  cell : CompactAdditiveTokenCell tokenTable width tokenCount left value right

noncomputable def compactAdditiveNatListAtRowDataOfGraph
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (hrows : CompactAdditiveNatListAtRows tokenTable width tokenCount
      boundaryTable count index value) :
    CompactAdditiveNatListAtRowData tokenTable width tokenCount boundaryTable
      index value := by
  let leftExists := hrows.2
  let left := Classical.choose leftExists
  have hleftData := Classical.choose_spec leftExists
  let rightExists := hleftData.2
  let right := Classical.choose rightExists
  have hrightData := Classical.choose_spec rightExists
  exact
    { left := left
      right := right
      left_le := hleftData.1
      right_le := hrightData.1
      left_entry := hrightData.2.1
      right_entry := hrightData.2.2.1
      cell := hrightData.2.2.2 }

noncomputable def
    compactAdditiveNatListAtRowsAtValuationIndexExplicitFormulaCertificateFromRowData
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (indexTerm : ValuationTerm)
    (hindexValue : termValue zeroValuation indexTerm = index)
    (hindex : index < count)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value) :
    HybridCertificate
      (compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndex tokenTable
        width tokenCount boundaryTable count value indexTerm) := by
  let values : Fin 2 -> Nat := ![data.right, data.left]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount)
        indexTerm
        (shortBinaryNumeralTerm data.left) (by
          simpa [termValue_shortBinaryNumeralTerm, hindexValue]
            using data.left_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (natListAtSuccessorTermAtValuationIndex indexTerm)
          (shortBinaryNumeralTerm data.right) (by
            simpa [natListAtSuccessorTermAtValuationIndex,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              hindexValue] using data.right_entry))
        (compactAdditiveTokenCellExplicitHybridCertificate
          tokenTable width tokenCount data.left value data.right data.cell))
  let terminal : HybridCertificate
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
          tokenCount boundaryTable value indexTerm) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListAtRowsTerminalAtValuationIndex_substitution_alignment
          tokenTable width tokenCount boundaryTable value data.left data.right
            indexTerm).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value indexTerm)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact data.right_le
      · exact data.left_le) terminal
  let body : HybridCertificate
      (compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
        tokenCount boundaryTable value indexTerm) :=
    .cast (by
      rw [explicitBoundedWitnessFormula_two_eq]
      rfl) installed
  let guard := strictCertificate indexTerm
    (shortBinaryNumeralTerm count) (by
      simpa [termValue_shortBinaryNumeralTerm, hindexValue] using hindex)
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction guard body

noncomputable def
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateFromRowData
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (indexTerm : ValuationTerm)
    (hindexValue : termValue zeroValuation indexTerm = index)
    (hindex : index < count)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value) :
    HybridCertificate
      (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount boundaryTable count value indexTerm) :=
  .cast
    (compactAdditiveNatListAtRowsAtValuationIndexFormula_alignment tokenTable
      width tokenCount boundaryTable count value indexTerm).symm
    (compactAdditiveNatListAtRowsAtValuationIndexExplicitFormulaCertificateFromRowData
      tokenTable width tokenCount boundaryTable count index value indexTerm
      hindexValue hindex data)

noncomputable def
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (indexTerm : ValuationTerm)
    (hindexValue : termValue zeroValuation indexTerm = index)
    (hrows : CompactAdditiveNatListAtRows tokenTable width tokenCount
      boundaryTable count index value) :
    HybridCertificate
      (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount boundaryTable count value indexTerm) :=
  compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateFromRowData
    tokenTable width tokenCount boundaryTable count index value indexTerm
    hindexValue hrows.1
    (compactAdditiveNatListAtRowDataOfGraph tokenTable width tokenCount
      boundaryTable count index value hrows)

/-! ## Exact index-and-value-term endpoint

The append combinators call the lookup graph with arithmetic expressions in
both the index and value coordinates.  This endpoint keeps both expressions in
the checked syntax tree and uses their values only to connect to the semantic
row graph.
-/

noncomputable def
    compactAdditiveTokenCellAtValuationExplicitHybridCertificateLocal
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm)
    (hcell : CompactAdditiveTokenCell
      (termValue valuation tokenTableTerm)
      (termValue valuation widthTerm)
      (termValue valuation tokenCountTerm)
      (termValue valuation cursorTerm)
      (termValue valuation valueTerm)
      (termValue valuation nextTerm)) :
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (compactAdditiveTokenCellAtValuationFormula tokenTableTerm widthTerm
        tokenCountTerm cursorTerm valueTerm nextTerm) := by
  let successorTerm : ValuationTerm := ‘!!cursorTerm + 1’
  let cursorLt := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    valuation Language.ORing.Rel.lt ![cursorTerm, tokenCountTerm] hcell.1
  let successor := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    valuation Language.Eq.eq ![nextTerm, successorTerm] (by
      change termValue valuation nextTerm =
        termValue valuation successorTerm
      simpa [successorTerm, termValue_arithmeticAdd,
        termValue_arithmeticOne] using hcell.2.1)
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (.cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm cursorLt)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (.cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm successor)
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        valuation tokenTableTerm widthTerm cursorTerm valueTerm hcell.2.2))
  exact .cast
    (compactAdditiveTokenCellAtValuationFormula_alignment tokenTableTerm
      widthTerm tokenCountTerm cursorTerm valueTerm nextTerm).symm parts

private def natListAtOuterTermsAtValuationIndexValue
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) : Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm boundaryTable,
    shortBinaryNumeralTerm count,
    indexTerm,
    valueTerm]

private def natListAtDepthOneTermsAtValuationIndexValue
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    Fin 8 -> ArithmeticSemiterm Nat 1 :=
  ![#0,
    closedShift 1 (shortBinaryNumeralTerm tokenTable),
    closedShift 1 (shortBinaryNumeralTerm width),
    closedShift 1 (shortBinaryNumeralTerm tokenCount),
    closedShift 1 (shortBinaryNumeralTerm boundaryTable),
    closedShift 1 (shortBinaryNumeralTerm count),
    closedShift 1 indexTerm,
    closedShift 1 valueTerm]

private def natListAtDepthTwoTermsAtValuationIndexValue
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    Fin 9 -> ArithmeticSemiterm Nat 2 :=
  ![#0, #1,
    closedShift 2 (shortBinaryNumeralTerm tokenTable),
    closedShift 2 (shortBinaryNumeralTerm width),
    closedShift 2 (shortBinaryNumeralTerm tokenCount),
    closedShift 2 (shortBinaryNumeralTerm boundaryTable),
    closedShift 2 (shortBinaryNumeralTerm count),
    closedShift 2 indexTerm,
    closedShift 2 valueTerm]

private theorem
    natListAtOuterAtValuationIndexValueRewriting_eq_embSubsts
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    (Rew.subst (natListAtOuterTermsAtValuationIndexValue tokenTable width
      tokenCount boundaryTable count indexTerm valueTerm)).comp
        (Rew.emb : Rew ℒₒᵣ Empty 7 Nat 7) =
      Rew.embSubsts (natListAtOuterTermsAtValuationIndexValue tokenTable width
        tokenCount boundaryTable count indexTerm valueTerm) := by
  ext coordinate
  · simp [Rew.comp_app]
  · exact Empty.elim coordinate

private theorem natListAtOuterAtValuationIndexValueQ1_eq_embSubsts
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    (Rew.embSubsts (natListAtOuterTermsAtValuationIndexValue tokenTable width
      tokenCount boundaryTable count indexTerm valueTerm)).q =
      Rew.embSubsts (natListAtDepthOneTermsAtValuationIndexValue tokenTable
        width tokenCount boundaryTable count indexTerm valueTerm) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListAtOuterTermsAtValuationIndexValue,
        natListAtDepthOneTermsAtValuationIndexValue, closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListAtOuterAtValuationIndexValueQ2_eq_embSubsts
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    (Rew.embSubsts (natListAtOuterTermsAtValuationIndexValue tokenTable width
      tokenCount boundaryTable count indexTerm valueTerm)).q.q =
      Rew.embSubsts (natListAtDepthTwoTermsAtValuationIndexValue tokenTable
        width tokenCount boundaryTable count indexTerm valueTerm) := by
  rw [natListAtOuterAtValuationIndexValueQ1_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListAtDepthOneTermsAtValuationIndexValue,
        natListAtDepthTwoTermsAtValuationIndexValue, closedShift, Rew.q]
  · exact Empty.elim coordinate

/-- The original lookup graph with the caller's exact index and value terms. -/
def compactAdditiveNatListAtRowsAtValuationIndexValueFormula
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListAtRowsDef.val) ⇜
    natListAtOuterTermsAtValuationIndexValue tokenTable width tokenCount
      boundaryTable count indexTerm valueTerm

theorem
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_eq_explicitSubstitution
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula tokenTable width
        tokenCount boundaryTable count indexTerm valueTerm =
      (Rewriting.emb (ξ := Nat) compactAdditiveNatListAtRowsDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm boundaryTable,
          shortBinaryNumeralTerm count,
          indexTerm,
          valueTerm] := by
  rfl

def compactAdditiveNatListAtRowsTerminalAtValuationIndexValue
    (tokenTable width tokenCount boundaryTable : Nat)
    (indexTerm valueTerm : ValuationTerm) : ArithmeticSemiformula Nat 2 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm boundaryTable),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 indexTerm,
        (#1 : ArithmeticSemiterm Nat 2)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm boundaryTable),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          closedShift 2
            (natListAtSuccessorTermAtValuationIndex indexTerm),
          (#0 : ArithmeticSemiterm Nat 2)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
          closedShift 2 (shortBinaryNumeralTerm width),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          (#1 : ArithmeticSemiterm Nat 2),
          closedShift 2 valueTerm,
          (#0 : ArithmeticSemiterm Nat 2)]))

def compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue
    (tokenTable width tokenCount boundaryTable : Nat)
    (indexTerm valueTerm : ValuationTerm) : ValuationFormula :=
  ((compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable width
      tokenCount boundaryTable indexTerm valueTerm).bexsLTSucc
        (closedShift 1 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (shortBinaryNumeralTerm tokenCount)

def compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndexValue
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) : ValuationFormula :=
  “!!indexTerm < !!(shortBinaryNumeralTerm count)” ⋏
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue tokenTable
      width tokenCount boundaryTable indexTerm valueTerm

private theorem natListAtSourceGuardAtValuationIndexValue_rewrite
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    Rew.embSubsts (natListAtOuterTermsAtValuationIndexValue tokenTable width
      tokenCount boundaryTable count indexTerm valueTerm) ▹
        (“#5 < #4” : ArithmeticSemiformula Empty 7) =
      “!!indexTerm < !!(shortBinaryNumeralTerm count)” := by
  simp [natListAtOuterTermsAtValuationIndexValue]

private theorem natListAtSourceTerminalAtValuationIndexValue_rewrite
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    Rew.embSubsts (natListAtDepthTwoTermsAtValuationIndexValue tokenTable width
      tokenCount boundaryTable count indexTerm valueTerm) ▹
        natListAtSourceTerminal =
      compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable width
        tokenCount boundaryTable indexTerm valueTerm := by
  unfold natListAtSourceTerminal
    compactAdditiveNatListAtRowsTerminalAtValuationIndexValue
  simp [rewriting_emptyFormulaSubstitution,
    natListAtDepthTwoTermsAtValuationIndexValue,
    natListAtSuccessorTermAtValuationIndex, closedShift,
    Function.comp_def]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;> simp

private theorem natListAtSourceWitnessBodyAtValuationIndexValue_rewrite
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    Rew.embSubsts (natListAtOuterTermsAtValuationIndexValue tokenTable width
      tokenCount boundaryTable count indexTerm valueTerm) ▹
        natListAtSourceWitnessBody =
      compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue tokenTable
        width tokenCount boundaryTable indexTerm valueTerm := by
  unfold natListAtSourceWitnessBody
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue
  rw [rewriting_bexsLTSucc, rewriting_bexsLTSucc]
  rw [natListAtOuterAtValuationIndexValueQ2_eq_embSubsts,
    natListAtSourceTerminalAtValuationIndexValue_rewrite,
    natListAtOuterAtValuationIndexValueQ1_eq_embSubsts]
  simp [natListAtOuterTermsAtValuationIndexValue,
    natListAtDepthOneTermsAtValuationIndexValue, closedShift]

theorem compactAdditiveNatListAtRowsAtValuationIndexValueFormula_alignment
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula tokenTable width
        tokenCount boundaryTable count indexTerm valueTerm =
      compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndexValue
        tokenTable width tokenCount boundaryTable count indexTerm valueTerm := by
  unfold compactAdditiveNatListAtRowsAtValuationIndexValueFormula
  change Rew.subst
      (natListAtOuterTermsAtValuationIndexValue tokenTable width tokenCount
        boundaryTable count indexTerm valueTerm) ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 7 Nat 7) ▹
        compactAdditiveNatListAtRowsDef.val) = _
  rw [← TransitiveRewriting.comp_app,
    natListAtOuterAtValuationIndexValueRewriting_eq_embSubsts]
  rw [compactAdditiveNatListAtRowsDef_val_eq_sourceDecomposed]
  unfold natListAtSourceDecomposedFormula
    compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndexValue
  simp only [LogicalConnective.HomClass.map_and]
  rw [natListAtSourceGuardAtValuationIndexValue_rewrite,
    natListAtSourceWitnessBodyAtValuationIndexValue_rewrite]

theorem
    compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_substitution_alignment
    (tokenTable width tokenCount boundaryTable left right : Nat)
    (indexTerm valueTerm : ValuationTerm) :
    (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable width
        tokenCount boundaryTable indexTerm valueTerm) ⇜
        ![shortBinaryNumeralTerm right, shortBinaryNumeralTerm left] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          indexTerm
          (shortBinaryNumeralTerm left) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (natListAtSuccessorTermAtValuationIndex indexTerm)
            (shortBinaryNumeralTerm right) ⋏
          compactAdditiveTokenCellAtValuationFormula
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm left) valueTerm
            (shortBinaryNumeralTerm right))) := by
  unfold compactAdditiveNatListAtRowsTerminalAtValuationIndexValue
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactAdditiveTokenCellAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate

/-- Build the explicit-form certificate from concrete row data while preserving
the caller's index and value terms in the checked syntax tree. -/
noncomputable def
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitFormulaCertificateFromRowData
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hindexValue : termValue valuation indexTerm = index)
    (hvalueValue : termValue valuation valueTerm = value)
    (hindex : index < count)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value) :
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndexValue
        tokenTable width tokenCount boundaryTable count indexTerm valueTerm) := by
  let values : Fin 2 -> Nat := ![data.right, data.left]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.right,
          shortBinaryNumeralTerm data.left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        valuation
        (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount)
        indexTerm
        (shortBinaryNumeralTerm data.left) (by
          simpa [termValue_shortBinaryNumeralTerm, hindexValue]
            using data.left_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          valuation
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (natListAtSuccessorTermAtValuationIndex indexTerm)
          (shortBinaryNumeralTerm data.right) (by
            simpa [natListAtSuccessorTermAtValuationIndex,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              hindexValue] using data.right_entry))
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificateLocal
          valuation
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm data.left) valueTerm
          (shortBinaryNumeralTerm data.right) (by
            simpa [termValue_shortBinaryNumeralTerm, hvalueValue]
              using data.cell)))
  let terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable
          width tokenCount boundaryTable indexTerm valueTerm) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_substitution_alignment
          tokenTable width tokenCount boundaryTable data.left data.right indexTerm
            valueTerm).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable width
      tokenCount boundaryTable indexTerm valueTerm)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact data.right_le
      · exact data.left_le) terminal
  let body : CheckedHybridValuationBoundedFormulaCertificate valuation
      (compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue tokenTable
        width tokenCount boundaryTable indexTerm valueTerm) :=
    .cast (by
      rw [explicitBoundedWitnessFormula_two_eq]
      rfl) installed
  have hguard :
      termValue valuation indexTerm <
        termValue valuation (shortBinaryNumeralTerm count) := by
    simpa [termValue_shortBinaryNumeralTerm, hindexValue] using hindex
  let guardDirect :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic valuation
      Language.ORing.Rel.lt ![indexTerm, shortBinaryNumeralTerm count] hguard
  let guard : CheckedHybridValuationBoundedFormulaCertificate valuation
      “!!indexTerm < !!(shortBinaryNumeralTerm count)” :=
    .cast (Semiformula.Operator.lt_def _ _).symm guardDirect
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction guard body

/-- Transport the transparent row-data certificate to the original lookup
formula. -/
noncomputable def
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateFromRowData
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hindexValue : termValue valuation indexTerm = index)
    (hvalueValue : termValue valuation valueTerm = value)
    (hindex : index < count)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value) :
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (compactAdditiveNatListAtRowsAtValuationIndexValueFormula tokenTable width
        tokenCount boundaryTable count indexTerm valueTerm) :=
  .cast
    (compactAdditiveNatListAtRowsAtValuationIndexValueFormula_alignment
      tokenTable width tokenCount boundaryTable count indexTerm valueTerm).symm
    (compactAdditiveNatListAtRowsAtValuationIndexValueExplicitFormulaCertificateFromRowData
      valuation tokenTable width tokenCount boundaryTable count index value
      indexTerm valueTerm hindexValue hvalueValue hindex data)

/-- Build the exact lookup certificate while preserving the caller's index and
value terms in the checked syntax tree. -/
noncomputable def
    compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hindexValue : termValue valuation indexTerm = index)
    (hvalueValue : termValue valuation valueTerm = value)
    (hrows : CompactAdditiveNatListAtRows tokenTable width tokenCount
      boundaryTable count index value) :
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (compactAdditiveNatListAtRowsAtValuationIndexValueFormula tokenTable width
        tokenCount boundaryTable count indexTerm valueTerm) :=
  compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateFromRowData
    valuation tokenTable width tokenCount boundaryTable count index value
    indexTerm valueTerm hindexValue hvalueValue hrows.1
    (compactAdditiveNatListAtRowDataOfGraph tokenTable width tokenCount
      boundaryTable count index value hrows)

#print axioms compactAdditiveNatListAtRowsClosedFormula_alignment
#print axioms compactAdditiveNatListAtRowsTerminal_substitution_alignment
#print axioms compactAdditiveNatListAtRowsExplicitHybridCertificateOfGraph
#print axioms compactAdditiveNatListAtRowsAtValuationIndexFormula_alignment
#print axioms compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
#print axioms compactAdditiveNatListAtRowsAtValuationIndexValueFormula_alignment
#print axioms
  compactAdditiveNatListAtRowsAtValuationIndexValueExplicitFormulaCertificateFromRowData
#print axioms compactAdditiveNatListAtRowsAtValuationIndexValueExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
