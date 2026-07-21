import integration.FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRows
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches

/-!
# Explicit hybrid certificate for additive natural-list cons rows

The certificate keeps the head token-cell witnesses and every tail-row
atomic-row-equality witness explicit.  The tail is assembled as a genuine
bounded universal whose branches are selected from the semantic graph.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

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

private theorem rewriting_formulaOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms =
      operator.operator (rewriting ∘ terms) := by
  unfold Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution rewriting operator.sentence terms

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1))
    (bound : ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : ArithmeticSemiterm sourceVariables (sourceArity + 1)),
            Rew.bShift bound] =
        ![(#0 : ArithmeticSemiterm targetVariables (targetArity + 1)),
          Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold Semiformula.ballLT
  rw [Rewriting.smul_ball, rewriting_formulaOperator, hguardTerms]

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

def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

private def unaryNumeralTerm (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

@[simp] private theorem termValue_unaryNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (unaryNumeralTerm value) = value := by
  unfold termValue unaryNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  simp

private def natListConsOuterTerms
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) : Fin 8 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm sourceBoundary,
    shortBinaryNumeralTerm sourceCount,
    shortBinaryNumeralTerm targetBoundary,
    shortBinaryNumeralTerm targetCount,
    shortBinaryNumeralTerm head]

private def natListConsDepthOneTerms
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    Fin 9 -> ArithmeticSemiterm Nat 1 :=
  ![#0,
    closedShift 1 (shortBinaryNumeralTerm tokenTable),
    closedShift 1 (shortBinaryNumeralTerm width),
    closedShift 1 (shortBinaryNumeralTerm tokenCount),
    closedShift 1 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 1 (shortBinaryNumeralTerm sourceCount),
    closedShift 1 (shortBinaryNumeralTerm targetBoundary),
    closedShift 1 (shortBinaryNumeralTerm targetCount),
    closedShift 1 (shortBinaryNumeralTerm head)]

private def natListConsDepthTwoTerms
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    Fin 10 -> ArithmeticSemiterm Nat 2 :=
  ![#0, #1,
    closedShift 2 (shortBinaryNumeralTerm tokenTable),
    closedShift 2 (shortBinaryNumeralTerm width),
    closedShift 2 (shortBinaryNumeralTerm tokenCount),
    closedShift 2 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 2 (shortBinaryNumeralTerm sourceCount),
    closedShift 2 (shortBinaryNumeralTerm targetBoundary),
    closedShift 2 (shortBinaryNumeralTerm targetCount),
    closedShift 2 (shortBinaryNumeralTerm head)]

private def natListConsDepthThreeTerms
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    Fin 11 -> ArithmeticSemiterm Nat 3 :=
  ![#0, #1, #2,
    closedShift 3 (shortBinaryNumeralTerm tokenTable),
    closedShift 3 (shortBinaryNumeralTerm width),
    closedShift 3 (shortBinaryNumeralTerm tokenCount),
    closedShift 3 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 3 (shortBinaryNumeralTerm sourceCount),
    closedShift 3 (shortBinaryNumeralTerm targetBoundary),
    closedShift 3 (shortBinaryNumeralTerm targetCount),
    closedShift 3 (shortBinaryNumeralTerm head)]

private def natListConsDepthFourTerms
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    Fin 12 -> ArithmeticSemiterm Nat 4 :=
  ![#0, #1, #2, #3,
    closedShift 4 (shortBinaryNumeralTerm tokenTable),
    closedShift 4 (shortBinaryNumeralTerm width),
    closedShift 4 (shortBinaryNumeralTerm tokenCount),
    closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 4 (shortBinaryNumeralTerm sourceCount),
    closedShift 4 (shortBinaryNumeralTerm targetBoundary),
    closedShift 4 (shortBinaryNumeralTerm targetCount),
    closedShift 4 (shortBinaryNumeralTerm head)]

private def natListConsDepthFiveTerms
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    Fin 13 -> ArithmeticSemiterm Nat 5 :=
  ![#0, #1, #2, #3, #4,
    closedShift 5 (shortBinaryNumeralTerm tokenTable),
    closedShift 5 (shortBinaryNumeralTerm width),
    closedShift 5 (shortBinaryNumeralTerm tokenCount),
    closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 5 (shortBinaryNumeralTerm sourceCount),
    closedShift 5 (shortBinaryNumeralTerm targetBoundary),
    closedShift 5 (shortBinaryNumeralTerm targetCount),
    closedShift 5 (shortBinaryNumeralTerm head)]

private theorem natListConsOuterRewriting_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    (Rew.subst (natListConsOuterTerms tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head)).comp
        (Rew.emb : Rew ℒₒᵣ Empty 8 Nat 8) =
      Rew.embSubsts (natListConsOuterTerms tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount head) := by
  ext coordinate
  · simp [Rew.comp_app]
  · exact Empty.elim coordinate

private theorem natListConsOuterQ1_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    (Rew.embSubsts (natListConsOuterTerms tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head)).q =
      Rew.embSubsts (natListConsDepthOneTerms tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount head) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListConsOuterTerms, natListConsDepthOneTerms,
        closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListConsOuterQ2_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    (Rew.embSubsts (natListConsOuterTerms tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head)).q.q =
      Rew.embSubsts (natListConsDepthTwoTerms tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount head) := by
  rw [natListConsOuterQ1_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListConsDepthOneTerms, natListConsDepthTwoTerms,
        closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListConsOuterQ3_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    (Rew.embSubsts (natListConsOuterTerms tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head)).q.q.q =
      Rew.embSubsts (natListConsDepthThreeTerms tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount head) := by
  rw [natListConsOuterQ2_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListConsDepthTwoTerms, natListConsDepthThreeTerms,
        closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListConsOuterQ4_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    (Rew.embSubsts (natListConsOuterTerms tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head)).q.q.q.q =
      Rew.embSubsts (natListConsDepthFourTerms tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount head) := by
  rw [natListConsOuterQ3_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListConsDepthThreeTerms, natListConsDepthFourTerms,
        closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListConsOuterQ5_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    (Rew.embSubsts (natListConsOuterTerms tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head)).q.q.q.q.q =
      Rew.embSubsts (natListConsDepthFiveTerms tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount head) := by
  rw [natListConsOuterQ4_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListConsDepthFourTerms, natListConsDepthFiveTerms,
        closedShift, Rew.q]
  · exact Empty.elim coordinate

/-- The original eight-coordinate graph closed by short binary numerals. -/
def compactAdditiveNatListConsRowsClosedFormula
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListConsRowsDef.val) ⇜
    natListConsOuterTerms tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head

/-- Public expansion of the private coordinate table used by the closed
formula.  Downstream graph assemblers can align the original predicate without
depending on the private table name. -/
theorem compactAdditiveNatListConsRowsClosedFormula_eq_explicitSubstitution
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    compactAdditiveNatListConsRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount head =
      (Rewriting.emb (ξ := Nat) compactAdditiveNatListConsRowsDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm sourceBoundary,
          shortBinaryNumeralTerm sourceCount,
          shortBinaryNumeralTerm targetBoundary,
          shortBinaryNumeralTerm targetCount,
          shortBinaryNumeralTerm head] := by
  rfl

/-- The head conjunction before its two bounded cursor witnesses close. -/
def compactAdditiveNatListConsRowsHeadTerminal
    (tokenTable width tokenCount targetBoundary head : Nat) :
    ArithmeticSemiformula Nat 2 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (unaryNumeralTerm 0),
        (#1 : ArithmeticSemiterm Nat 2)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          closedShift 2 (unaryNumeralTerm 1),
          (#0 : ArithmeticSemiterm Nat 2)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
          closedShift 2 (shortBinaryNumeralTerm width),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          (#1 : ArithmeticSemiterm Nat 2),
          closedShift 2 (shortBinaryNumeralTerm head),
          (#0 : ArithmeticSemiterm Nat 2)]))

def compactAdditiveNatListConsRowsHeadBody
    (tokenTable width tokenCount targetBoundary head : Nat) :
    ValuationFormula :=
  ((compactAdditiveNatListConsRowsHeadTerminal
      tokenTable width tokenCount targetBoundary head).bexsLTSucc
        (closedShift 1 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (shortBinaryNumeralTerm tokenCount)

/-- The tail conjunction before four bounded row witnesses close. -/
def compactAdditiveNatListConsRowsTailTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 5 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 5 (shortBinaryNumeralTerm tokenCount),
        (#4 : ArithmeticSemiterm Nat 5),
        (#3 : ArithmeticSemiterm Nat 5)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 5 (shortBinaryNumeralTerm tokenCount),
          ‘#4 + 1’,
          (#2 : ArithmeticSemiterm Nat 5)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
            closedShift 5 (shortBinaryNumeralTerm tokenCount),
            ‘#4 + 1’,
            (#1 : ArithmeticSemiterm Nat 5)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
              closedShift 5 (shortBinaryNumeralTerm tokenCount),
              ‘#4 + 2’,
              (#0 : ArithmeticSemiterm Nat 5)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜
            ![closedShift 5 (shortBinaryNumeralTerm tokenTable),
              closedShift 5 (shortBinaryNumeralTerm width),
              closedShift 5 (shortBinaryNumeralTerm tokenCount),
              (#3 : ArithmeticSemiterm Nat 5),
              (#2 : ArithmeticSemiterm Nat 5),
              (#1 : ArithmeticSemiterm Nat 5),
              (#0 : ArithmeticSemiterm Nat 5)]))))

def compactAdditiveNatListConsRowsTailBody
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 1 :=
  ((((compactAdditiveNatListConsRowsTailTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary).bexsLTSucc
        (closedShift 4 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 2 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (closedShift 1 (shortBinaryNumeralTerm tokenCount))

def compactAdditiveNatListConsRowsExplicitFormula
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1” ⋏
    (compactAdditiveNatListConsRowsHeadBody
      tokenTable width tokenCount targetBoundary head ⋏
      (compactAdditiveNatListConsRowsTailBody
        tokenTable width tokenCount sourceBoundary targetBoundary).ballLT
          (shortBinaryNumeralTerm sourceCount))

private def natListConsSourceHeadTerminal :
    ArithmeticSemiformula Empty 10 :=
  (compactFixedWidthEntryDef.val ⇜
      ![(#7 : ArithmeticSemiterm Empty 10), #4, ‘0’, #1]) ⋏
    ((compactFixedWidthEntryDef.val ⇜
        ![(#7 : ArithmeticSemiterm Empty 10), #4, ‘1’, #0]) ⋏
      ((“#1 < #4” : ArithmeticSemiformula Empty 10) ⋏
        ((“#0 = #1 + 1” : ArithmeticSemiformula Empty 10) ⋏
          (compactFixedWidthEntryDef.val ⇜
            ![(#2 : ArithmeticSemiterm Empty 10), #3, #1, #9]))))

private def natListConsSourceHeadBody : ArithmeticSemiformula Empty 8 :=
  (natListConsSourceHeadTerminal.bexsLTSucc
      (#3 : ArithmeticSemiterm Empty 9)).bexsLTSucc
    (#2 : ArithmeticSemiterm Empty 8)

private def natListConsSourceTailBitBody :
    ArithmeticSemiformula Empty 14 :=
  “(((#4 * #7) + #0) ∈ #6 ↔ ((#2 * #7) + #0) ∈ #6)”

private def natListConsSourceTailTerminal :
    ArithmeticSemiformula Empty 13 :=
  (compactFixedWidthEntryDef.val ⇜
      ![(#8 : ArithmeticSemiterm Empty 13), #7, #4, #3]) ⋏
    ((compactFixedWidthEntryDef.val ⇜
        ![(#8 : ArithmeticSemiterm Empty 13), #7, ‘#4 + 1’, #2]) ⋏
      ((compactFixedWidthEntryDef.val ⇜
          ![(#10 : ArithmeticSemiterm Empty 13), #7, ‘#4 + 1’, #1]) ⋏
        ((compactFixedWidthEntryDef.val ⇜
            ![(#10 : ArithmeticSemiterm Empty 13), #7, ‘#4 + 2’, #0]) ⋏
          ((“#3 < #7” : ArithmeticSemiformula Empty 13) ⋏
            ((“#2 = #3 + 1” : ArithmeticSemiformula Empty 13) ⋏
              ((“#1 < #7” : ArithmeticSemiformula Empty 13) ⋏
                ((“#0 = #1 + 1” : ArithmeticSemiformula Empty 13) ⋏
                  natListConsSourceTailBitBody.ballLT
                    (#6 : ArithmeticSemiterm Empty 13))))))))

private def natListConsSourceTailBody : ArithmeticSemiformula Empty 9 :=
  ((((natListConsSourceTailTerminal.bexsLTSucc
      (#6 : ArithmeticSemiterm Empty 12)).bexsLTSucc
        (#5 : ArithmeticSemiterm Empty 11)).bexsLTSucc
      (#4 : ArithmeticSemiterm Empty 10)).bexsLTSucc
    (#3 : ArithmeticSemiterm Empty 9))

private def natListConsSourceDecomposedFormula :
    ArithmeticSemiformula Empty 8 :=
  (“#6 = #4 + 1” : ArithmeticSemiformula Empty 8) ⋏
    (natListConsSourceHeadBody ⋏
      natListConsSourceTailBody.ballLT
        (#4 : ArithmeticSemiterm Empty 8))

private theorem compactAdditiveNatListConsRowsDef_val_eq_sourceDecomposed :
    compactAdditiveNatListConsRowsDef.val =
      natListConsSourceDecomposedFormula := by
  unfold compactAdditiveNatListConsRowsDef
  unfold natListConsSourceDecomposedFormula
  unfold natListConsSourceHeadBody natListConsSourceHeadTerminal
  unfold natListConsSourceTailBody natListConsSourceTailTerminal
    natListConsSourceTailBitBody
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

private theorem natListConsSourceCount_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    Rew.embSubsts
        (natListConsOuterTerms tokenTable width tokenCount sourceBoundary
          sourceCount targetBoundary targetCount head) ▹
        (“#6 = #4 + 1” : ArithmeticSemiformula Empty 8) =
      “!!(shortBinaryNumeralTerm targetCount) =
        !!(shortBinaryNumeralTerm sourceCount) + 1” := by
  simp [natListConsOuterTerms]

private theorem natListConsSourceHeadTerminal_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    Rew.embSubsts
        (natListConsDepthTwoTerms tokenTable width tokenCount sourceBoundary
          sourceCount targetBoundary targetCount head) ▹
        natListConsSourceHeadTerminal =
      compactAdditiveNatListConsRowsHeadTerminal
        tokenTable width tokenCount targetBoundary head := by
  unfold natListConsSourceHeadTerminal
  unfold compactAdditiveNatListConsRowsHeadTerminal
  unfold compactAdditiveTokenCellDef
  simp [rewriting_emptyFormulaSubstitution,
    rewriting_embeddedFormulaSubstitution,
    natListConsDepthTwoTerms, unaryNumeralTerm, closedShift,
    Function.comp_def, Rew.subst_bvar]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Rew.subst_bvar]

private theorem natListConsSourceHeadBody_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    Rew.embSubsts
        (natListConsOuterTerms tokenTable width tokenCount sourceBoundary
          sourceCount targetBoundary targetCount head) ▹
        natListConsSourceHeadBody =
      compactAdditiveNatListConsRowsHeadBody
        tokenTable width tokenCount targetBoundary head := by
  unfold natListConsSourceHeadBody
  unfold compactAdditiveNatListConsRowsHeadBody
  rw [rewriting_bexsLTSucc, rewriting_bexsLTSucc]
  rw [natListConsOuterQ2_eq_embSubsts,
    natListConsSourceHeadTerminal_rewrite,
    natListConsOuterQ1_eq_embSubsts]
  simp [natListConsOuterTerms, natListConsDepthOneTerms, closedShift]

private theorem natListConsSourceTailTerminal_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    Rew.embSubsts
        (natListConsDepthFiveTerms tokenTable width tokenCount sourceBoundary
          sourceCount targetBoundary targetCount head) ▹
        natListConsSourceTailTerminal =
      compactAdditiveNatListConsRowsTailTerminal
        tokenTable width tokenCount sourceBoundary targetBoundary := by
  unfold natListConsSourceTailTerminal natListConsSourceTailBitBody
  unfold compactAdditiveNatListConsRowsTailTerminal
  unfold compactAdditiveAtomicRowEqDef
  simp [rewriting_emptyFormulaSubstitution,
    rewriting_ballLT,
    natListConsDepthFiveTerms, closedShift, Function.comp_def,
    Rew.subst_bvar, Rew.q]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;> simp

private theorem natListConsSourceTailBody_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    (Rew.embSubsts
        (natListConsOuterTerms tokenTable width tokenCount sourceBoundary
          sourceCount targetBoundary targetCount head)).q ▹
        natListConsSourceTailBody =
      compactAdditiveNatListConsRowsTailBody
        tokenTable width tokenCount sourceBoundary targetBoundary := by
  unfold natListConsSourceTailBody
  unfold compactAdditiveNatListConsRowsTailBody
  rw [rewriting_bexsLTSucc, rewriting_bexsLTSucc,
    rewriting_bexsLTSucc, rewriting_bexsLTSucc]
  rw [natListConsOuterQ5_eq_embSubsts,
    natListConsSourceTailTerminal_rewrite,
    natListConsOuterQ4_eq_embSubsts,
    natListConsOuterQ3_eq_embSubsts,
    natListConsOuterQ2_eq_embSubsts,
    natListConsOuterQ1_eq_embSubsts]
  simp [natListConsDepthOneTerms, natListConsDepthTwoTerms,
    natListConsDepthThreeTerms, natListConsDepthFourTerms, closedShift]

/-- Exact alignment with the original eight-coordinate graph formula. -/
theorem compactAdditiveNatListConsRowsClosedFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat) :
    compactAdditiveNatListConsRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount head =
      compactAdditiveNatListConsRowsExplicitFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount head := by
  unfold compactAdditiveNatListConsRowsClosedFormula
  change Rew.subst
      (natListConsOuterTerms tokenTable width tokenCount sourceBoundary
        sourceCount targetBoundary targetCount head) ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 8 Nat 8) ▹
        compactAdditiveNatListConsRowsDef.val) = _
  rw [← TransitiveRewriting.comp_app,
    natListConsOuterRewriting_eq_embSubsts]
  rw [compactAdditiveNatListConsRowsDef_val_eq_sourceDecomposed]
  let rewriting := Rew.embSubsts
    (natListConsOuterTerms tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount head)
  change rewriting ▹ natListConsSourceDecomposedFormula =
    compactAdditiveNatListConsRowsExplicitFormula tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head
  unfold natListConsSourceDecomposedFormula
  unfold compactAdditiveNatListConsRowsExplicitFormula
  simp only [LogicalConnective.HomClass.map_and]
  rw [show rewriting ▹
      (“#6 = #4 + 1” : ArithmeticSemiformula Empty 8) =
        “!!(shortBinaryNumeralTerm targetCount) =
          !!(shortBinaryNumeralTerm sourceCount) + 1” by
        exact natListConsSourceCount_rewrite tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount head]
  rw [show rewriting ▹ natListConsSourceHeadBody =
      compactAdditiveNatListConsRowsHeadBody tokenTable width tokenCount
        targetBoundary head by
        exact natListConsSourceHeadBody_rewrite tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount head]
  rw [rewriting_ballLT]
  rw [show rewriting.q ▹ natListConsSourceTailBody =
      compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary by
        exact natListConsSourceTailBody_rewrite tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount head]
  simp [rewriting, natListConsOuterTerms]

structure CompactAdditiveNatListConsHeadData
    (tokenTable width tokenCount targetBoundary head : Nat) where
  targetLeft : Nat
  targetRight : Nat
  targetLeft_le : targetLeft ≤ tokenCount
  targetRight_le : targetRight ≤ tokenCount
  targetLeft_entry : CompactFixedWidthEntry
    targetBoundary tokenCount 0 targetLeft
  targetRight_entry : CompactFixedWidthEntry
    targetBoundary tokenCount 1 targetRight
  token_cell : CompactAdditiveTokenCell
    tokenTable width tokenCount targetLeft head targetRight

structure CompactAdditiveNatListConsTailRowData
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat) where
  sourceLeft : Nat
  sourceRight : Nat
  targetLeft : Nat
  targetRight : Nat
  sourceLeft_le : sourceLeft ≤ tokenCount
  sourceRight_le : sourceRight ≤ tokenCount
  targetLeft_le : targetLeft ≤ tokenCount
  targetRight_le : targetRight ≤ tokenCount
  sourceLeft_entry : CompactFixedWidthEntry
    sourceBoundary tokenCount index sourceLeft
  sourceRight_entry : CompactFixedWidthEntry
    sourceBoundary tokenCount (index + 1) sourceRight
  targetLeft_entry : CompactFixedWidthEntry
    targetBoundary tokenCount (index + 1) targetLeft
  targetRight_entry : CompactFixedWidthEntry
    targetBoundary tokenCount (index + 2) targetRight
  atomic_row_eq : CompactAdditiveAtomicRowEq
    tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight

private theorem substitute_closedShift
    {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
        apply Rew.ext
        · intro index
          exact Fin.elim0 index
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ k ih =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun index : Fin k => values index.succ) := by
        apply Rew.ext
        · intro index
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (closedShift (k + 1) term) =
            ((Rew.subst values).comp Rew.bShift) (closedShift k term) := by
              simp [closedShift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin k => values index.succ)
              (closedShift k term) := by rw [hrew]
        _ = term := ih _

private def closedShiftRewriting :
    (k : Nat) -> Rew ℒₒᵣ Nat 0 Nat k
  | 0 => Rew.id
  | k + 1 => Rew.bShift.comp (closedShiftRewriting k)

@[simp] private theorem closedShiftRewriting_apply
    (k : Nat) (term : ValuationTerm) :
    closedShiftRewriting k term = closedShift k term := by
  induction k with
  | zero => exact Rew.id_app term
  | succ k ih =>
      simp [closedShiftRewriting, closedShift, Rew.comp_app, ih]

@[simp] private theorem free_closedShift_shortBinaryNumeralTerm
    (k value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := k))
        (closedShift (k + 1) (shortBinaryNumeralTerm value)) =
      closedShift k (shortBinaryNumeralTerm value) := by
  let leftRewriting : Rew ℒₒᵣ Nat 0 Nat k :=
    (Rew.free (L := ℒₒᵣ) (n := k)).comp (closedShiftRewriting (k + 1))
  let rightRewriting : Rew ℒₒᵣ Nat 0 Nat k := closedShiftRewriting k
  have h := Semiterm.rew_eq_of_funEqOn
    leftRewriting rightRewriting (shortBinaryNumeralTerm value)
    (fun coordinate => Fin.elim0 coordinate)
    (fun coordinate hcoordinate => by
      have : coordinate ∈
          (shortBinaryNumeralTerm value).freeVariables := hcoordinate
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa [leftRewriting, rightRewriting, Rew.comp_app] using h

@[simp] private theorem shift_shortBinaryNumeralTerm (value : Nat) :
    Rew.shift (shortBinaryNumeralTerm value) =
      shortBinaryNumeralTerm value := by
  rw [← free_bShift_term]
  exact free_closedShift_shortBinaryNumeralTerm 0 value

@[simp] private theorem free_bShift2_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value))) =
      Rew.bShift (shortBinaryNumeralTerm value) := by
  change (Rew.free (L := ℒₒᵣ) (n := 1))
      (closedShift 2 (shortBinaryNumeralTerm value)) =
    closedShift 1 (shortBinaryNumeralTerm value)
  exact free_closedShift_shortBinaryNumeralTerm 1 value

@[simp] private theorem free_bShift3_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value)))) =
      Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value)) := by
  change (Rew.free (L := ℒₒᵣ) (n := 2))
      (closedShift 3 (shortBinaryNumeralTerm value)) =
    closedShift 2 (shortBinaryNumeralTerm value)
  exact free_closedShift_shortBinaryNumeralTerm 2 value

@[simp] private theorem free_bShift4_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value))))) =
      Rew.bShift (Rew.bShift
        (Rew.bShift (shortBinaryNumeralTerm value))) := by
  change (Rew.free (L := ℒₒᵣ) (n := 3))
      (closedShift 4 (shortBinaryNumeralTerm value)) =
    closedShift 3 (shortBinaryNumeralTerm value)
  exact free_closedShift_shortBinaryNumeralTerm 3 value

@[simp] private theorem free_bShift5_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value)))))) =
      Rew.bShift (Rew.bShift (Rew.bShift
        (Rew.bShift (shortBinaryNumeralTerm value)))) := by
  change (Rew.free (L := ℒₒᵣ) (n := 4))
      (closedShift 5 (shortBinaryNumeralTerm value)) =
    closedShift 4 (shortBinaryNumeralTerm value)
  exact free_closedShift_shortBinaryNumeralTerm 4 value

@[simp] private theorem free_bvar_four_fin5 :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (#4 : ArithmeticSemiterm Nat 5) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 4)) (#(Fin.last 4)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem free_bvar_three_fin5 :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (#3 : ArithmeticSemiterm Nat 5) = #3 := by
  exact Rew.free_bvar_castSucc (3 : Fin 4)

@[simp] private theorem free_bvar_two_fin5 :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (#2 : ArithmeticSemiterm Nat 5) = #2 := by
  exact Rew.free_bvar_castSucc (2 : Fin 4)

@[simp] private theorem free_bvar_one_fin5 :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (#1 : ArithmeticSemiterm Nat 5) = #1 := by
  exact Rew.free_bvar_castSucc (1 : Fin 4)

def compactAdditiveNatListConsRowsTailBranchTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        closedShift 4 (&0 : ValuationTerm),
        (#3 : ArithmeticSemiterm Nat 4)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          closedShift 4 (‘&0 + 1’ : ValuationTerm),
          (#2 : ArithmeticSemiterm Nat 4)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
            closedShift 4 (shortBinaryNumeralTerm tokenCount),
            closedShift 4 (‘&0 + 1’ : ValuationTerm),
            (#1 : ArithmeticSemiterm Nat 4)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
              closedShift 4 (shortBinaryNumeralTerm tokenCount),
              closedShift 4 (‘&0 + 2’ : ValuationTerm),
              (#0 : ArithmeticSemiterm Nat 4)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
              closedShift 4 (shortBinaryNumeralTerm width),
              closedShift 4 (shortBinaryNumeralTerm tokenCount),
              (#3 : ArithmeticSemiterm Nat 4),
              (#2 : ArithmeticSemiterm Nat 4),
              (#1 : ArithmeticSemiterm Nat 4),
              (#0 : ArithmeticSemiterm Nat 4)]))))

private theorem compactAdditiveNatListConsRowsTailTerminal_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    Rewriting.free
        (compactAdditiveNatListConsRowsTailTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary) =
      compactAdditiveNatListConsRowsTailBranchTerminal
        tokenTable width tokenCount sourceBoundary targetBoundary := by
  unfold compactAdditiveNatListConsRowsTailTerminal
  unfold compactAdditiveNatListConsRowsTailBranchTerminal
  simp [closedShift, ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private theorem explicitBoundedWitnessFormula_two_eq
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 2) :
    explicitBoundedWitnessFormula bound 2 body =
      (body.bexsLTSucc (closedShift 1 bound)).bexsLTSucc bound := by
  rfl

private theorem explicitBoundedWitnessFormula_four_eq
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 4) :
    explicitBoundedWitnessFormula bound 4 body =
      ((((body.bexsLTSucc (closedShift 3 bound)).bexsLTSucc
        (closedShift 2 bound)).bexsLTSucc
          (closedShift 1 bound)).bexsLTSucc bound) := by
  rfl

theorem compactAdditiveNatListConsRowsTailBody_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    Rewriting.free
        (compactAdditiveNatListConsRowsTailBody
          tokenTable width tokenCount sourceBoundary targetBoundary) =
      explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm tokenCount) 4
        (compactAdditiveNatListConsRowsTailBranchTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary) := by
  rw [explicitBoundedWitnessFormula_four_eq]
  unfold compactAdditiveNatListConsRowsTailBody
  simp [Rew.q_free, closedShift,
    compactAdditiveNatListConsRowsTailTerminal_free_alignment]

theorem compactAdditiveNatListConsRowsHeadTerminal_substitution_alignment
    (tokenTable width tokenCount targetBoundary head targetLeft targetRight : Nat) :
    (compactAdditiveNatListConsRowsHeadTerminal
        tokenTable width tokenCount targetBoundary head) ⇜
        ![shortBinaryNumeralTerm targetRight,
          shortBinaryNumeralTerm targetLeft] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (unaryNumeralTerm 0)
          (shortBinaryNumeralTerm targetLeft) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (unaryNumeralTerm 1)
            (shortBinaryNumeralTerm targetRight) ⋏
          compactAdditiveTokenCellClosedFormula
            tokenTable width tokenCount targetLeft head targetRight)) := by
  unfold compactAdditiveNatListConsRowsHeadTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactAdditiveTokenCellClosedFormula
  simp [← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate
  · constructor
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
      · intro coordinate
        exact Empty.elim coordinate

theorem compactAdditiveNatListConsRowsTailBranchTerminal_substitution_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      sourceLeft sourceRight targetLeft targetRight : Nat) :
    (compactAdditiveNatListConsRowsTailBranchTerminal
        tokenTable width tokenCount sourceBoundary targetBoundary) ⇜
        ![shortBinaryNumeralTerm targetRight,
          shortBinaryNumeralTerm targetLeft,
          shortBinaryNumeralTerm sourceRight,
          shortBinaryNumeralTerm sourceLeft] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (&0 : ValuationTerm)
          (shortBinaryNumeralTerm sourceLeft) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (‘&0 + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm sourceRight) ⋏
          (compactFixedWidthEntryAtValuationFormula
              (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount)
              (‘&0 + 1’ : ValuationTerm)
              (shortBinaryNumeralTerm targetLeft) ⋏
            (compactFixedWidthEntryAtValuationFormula
                (shortBinaryNumeralTerm targetBoundary)
                (shortBinaryNumeralTerm tokenCount)
                (‘&0 + 2’ : ValuationTerm)
                (shortBinaryNumeralTerm targetRight) ⋏
              compactAdditiveAtomicRowEqAtValuationFormula
                (shortBinaryNumeralTerm tokenTable)
                (shortBinaryNumeralTerm width)
                (shortBinaryNumeralTerm tokenCount)
                (shortBinaryNumeralTerm sourceLeft)
                (shortBinaryNumeralTerm sourceRight)
                (shortBinaryNumeralTerm targetLeft)
                (shortBinaryNumeralTerm targetRight))))) := by
  unfold compactAdditiveNatListConsRowsTailBranchTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactAdditiveAtomicRowEqAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    congr 1
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

private theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  exact termValue_unaryNumeralTerm valuation 2

private noncomputable def countEqualityCertificate
    (sourceCount targetCount : Nat)
    (hcount : targetCount = sourceCount + 1) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm targetCount) =
        !!(shortBinaryNumeralTerm sourceCount) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm sourceCount) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm targetCount, rightTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm targetCount) =
        termValue zeroValuation rightTerm
      simp only [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne]
      exact hcount)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def compactAdditiveNatListConsRowsHeadCertificate
    (tokenTable width tokenCount targetBoundary head : Nat)
    (data : CompactAdditiveNatListConsHeadData
      tokenTable width tokenCount targetBoundary head) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListConsRowsHeadBody
        tokenTable width tokenCount targetBoundary head) := by
  let values : Fin 2 -> Nat := ![data.targetRight, data.targetLeft]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.targetRight,
          shortBinaryNumeralTerm data.targetLeft] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (unaryNumeralTerm 0)
        (shortBinaryNumeralTerm data.targetLeft) (by
          simpa [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetLeft_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (unaryNumeralTerm 1)
          (shortBinaryNumeralTerm data.targetRight) (by
            simpa [termValue_shortBinaryNumeralTerm,
              termValue_unaryNumeralTerm] using data.targetRight_entry))
        (compactAdditiveTokenCellExplicitHybridCertificate
          tokenTable width tokenCount data.targetLeft head data.targetRight
            data.token_cell))
  let terminal : HybridCertificate zeroValuation
      ((compactAdditiveNatListConsRowsHeadTerminal
          tokenTable width tokenCount targetBoundary head) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListConsRowsHeadTerminal_substitution_alignment
          tokenTable width tokenCount targetBoundary head data.targetLeft
            data.targetRight).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
      (compactAdditiveNatListConsRowsHeadTerminal
        tokenTable width tokenCount targetBoundary head)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le) terminal
  exact .cast (by
    rw [explicitBoundedWitnessFormula_two_eq]
    rfl) installed

private noncomputable def compactAdditiveNatListConsRowsTailBranchCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridCertificate (extendValuation index zeroValuation)
      (Rewriting.free
        (compactAdditiveNatListConsRowsTailBody
          tokenTable width tokenCount sourceBoundary targetBoundary)) := by
  let valuation := extendValuation index zeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]
  have hvalueTerms :
      (fun coordinate : Fin 4 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.targetRight,
          shortBinaryNumeralTerm data.targetLeft,
          shortBinaryNumeralTerm data.sourceRight,
          shortBinaryNumeralTerm data.sourceLeft] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        valuation
        (shortBinaryNumeralTerm sourceBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (&0 : ValuationTerm)
        (shortBinaryNumeralTerm data.sourceLeft) (by
          simpa [valuation, zeroValuation,
            termValue_shortBinaryNumeralTerm,
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
            using data.sourceLeft_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          valuation
          (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (‘&0 + 1’ : ValuationTerm)
          (shortBinaryNumeralTerm data.sourceRight) (by
            simpa [valuation, zeroValuation,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using data.sourceRight_entry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            valuation
            (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (‘&0 + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm data.targetLeft) (by
              simpa [valuation, zeroValuation,
                termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd, termValue_arithmeticOne,
                FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                using data.targetLeft_entry))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactFixedWidthEntryAtValuationExplicitHybridCertificate
              valuation
              (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount)
              (‘&0 + 2’ : ValuationTerm)
              (shortBinaryNumeralTerm data.targetRight) (by
                simpa [valuation, zeroValuation,
                  termValue_shortBinaryNumeralTerm,
                  termValue_arithmeticAdd, termValue_arithmeticTwo,
                  FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                  using data.targetRight_entry))
            (compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate
              valuation
              (shortBinaryNumeralTerm tokenTable)
              (shortBinaryNumeralTerm width)
              (shortBinaryNumeralTerm tokenCount)
              (shortBinaryNumeralTerm data.sourceLeft)
              (shortBinaryNumeralTerm data.sourceRight)
              (shortBinaryNumeralTerm data.targetLeft)
              (shortBinaryNumeralTerm data.targetRight) (by
                simpa [valuation, zeroValuation,
                  termValue_shortBinaryNumeralTerm]
                  using data.atomic_row_eq)))))
  let terminal : HybridCertificate valuation
      ((compactAdditiveNatListConsRowsTailBranchTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListConsRowsTailBranchTerminal_substitution_alignment
          tokenTable width tokenCount sourceBoundary targetBoundary
            data.sourceLeft data.sourceRight data.targetLeft
            data.targetRight).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate
    tokenCount
    (compactAdditiveNatListConsRowsTailBranchTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact data.targetRight_le
      · exact data.targetLeft_le
      · exact data.sourceRight_le
      · exact data.sourceLeft_le) terminal
  exact .cast
    (compactAdditiveNatListConsRowsTailBody_free_alignment
      tokenTable width tokenCount sourceBoundary targetBoundary).symm installed

private noncomputable def compactAdditiveNatListConsRowsTailUniversalCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridCertificate zeroValuation
      ((compactAdditiveNatListConsRowsTailBody
        tokenTable width tokenCount sourceBoundary targetBoundary).ballLT
          (shortBinaryNumeralTerm sourceCount)) := by
  let body := compactAdditiveNatListConsRowsTailBody
    tokenTable width tokenCount sourceBoundary targetBoundary
  let branches := buildExplicitHybridUniversalBranches sourceCount
    (fun index hindex =>
      compactAdditiveNatListConsRowsTailBranchCertificate
        tokenTable width tokenCount sourceBoundary targetBoundary index
          (rows ⟨index, hindex⟩))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm sourceCount) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body) =
        body.ballLT (shortBinaryNumeralTerm sourceCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- Construct the closed certificate from fully explicit head and tail data. -/
noncomputable def compactAdditiveNatListConsRowsFromDataExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat)
    (hcount : targetCount = sourceCount + 1)
    (headData : CompactAdditiveNatListConsHeadData
      tokenTable width tokenCount targetBoundary head)
    (tailRows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListConsRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount head) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (countEqualityCertificate sourceCount targetCount hcount)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveNatListConsRowsHeadCertificate
        tokenTable width tokenCount targetBoundary head headData)
      (compactAdditiveNatListConsRowsTailUniversalCertificate
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          tailRows))
  exact .cast
    (compactAdditiveNatListConsRowsClosedFormula_alignment
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount head).symm parts

/-- Extract every head and tail witness from the semantic graph. -/
noncomputable def compactAdditiveNatListConsRowsOfGraphExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat)
    (hgraph : CompactAdditiveNatListConsRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount head) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListConsRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount head) :=
  compactAdditiveNatListConsRowsFromDataExplicitHybridCertificate
    tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head hgraph.1
    (by
      let targetLeftExists := hgraph.2.1
      let targetLeft := Classical.choose targetLeftExists
      have htargetLeft := Classical.choose_spec targetLeftExists
      let targetRightExists := htargetLeft.2
      let targetRight := Classical.choose targetRightExists
      have htargetRight := Classical.choose_spec targetRightExists
      exact
        { targetLeft := targetLeft
          targetRight := targetRight
          targetLeft_le := htargetLeft.1
          targetRight_le := htargetRight.1
          targetLeft_entry := htargetRight.2.1
          targetRight_entry := htargetRight.2.2.1
          token_cell := htargetRight.2.2.2 })
    (fun index => by
      let sourceLeftExists := hgraph.2.2 index index.isLt
      let sourceLeft := Classical.choose sourceLeftExists
      have hsourceLeft := Classical.choose_spec sourceLeftExists
      let sourceRightExists := hsourceLeft.2
      let sourceRight := Classical.choose sourceRightExists
      have hsourceRight := Classical.choose_spec sourceRightExists
      let targetLeftExists := hsourceRight.2
      let targetLeft := Classical.choose targetLeftExists
      have htargetLeft := Classical.choose_spec targetLeftExists
      let targetRightExists := htargetLeft.2
      let targetRight := Classical.choose targetRightExists
      have htargetRight := Classical.choose_spec targetRightExists
      exact
        { sourceLeft := sourceLeft
          sourceRight := sourceRight
          targetLeft := targetLeft
          targetRight := targetRight
          sourceLeft_le := hsourceLeft.1
          sourceRight_le := hsourceRight.1
          targetLeft_le := htargetLeft.1
          targetRight_le := htargetRight.1
          sourceLeft_entry := htargetRight.2.1
          sourceRight_entry := htargetRight.2.2.1
          targetLeft_entry := htargetRight.2.2.2.1
          targetRight_entry := htargetRight.2.2.2.2.1
          atomic_row_eq := htargetRight.2.2.2.2.2 })

/-! ## Exact head-term endpoint

The original graph accepts an arbitrary arithmetic term in its head coordinate.
The closed endpoint above intentionally uses a short binary numeral.  The
following parallel endpoint keeps the caller's head term syntactically exact;
only its value under `zeroValuation` is related to the semantic graph head.
-/

private def natListConsOuterTermsAtValuationHead
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) : Fin 8 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm sourceBoundary,
    shortBinaryNumeralTerm sourceCount,
    shortBinaryNumeralTerm targetBoundary,
    shortBinaryNumeralTerm targetCount,
    headTerm]

private def natListConsDepthOneTermsAtValuationHead
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    Fin 9 -> ArithmeticSemiterm Nat 1 :=
  ![#0,
    closedShift 1 (shortBinaryNumeralTerm tokenTable),
    closedShift 1 (shortBinaryNumeralTerm width),
    closedShift 1 (shortBinaryNumeralTerm tokenCount),
    closedShift 1 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 1 (shortBinaryNumeralTerm sourceCount),
    closedShift 1 (shortBinaryNumeralTerm targetBoundary),
    closedShift 1 (shortBinaryNumeralTerm targetCount),
    closedShift 1 headTerm]

private def natListConsDepthTwoTermsAtValuationHead
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    Fin 10 -> ArithmeticSemiterm Nat 2 :=
  ![#0, #1,
    closedShift 2 (shortBinaryNumeralTerm tokenTable),
    closedShift 2 (shortBinaryNumeralTerm width),
    closedShift 2 (shortBinaryNumeralTerm tokenCount),
    closedShift 2 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 2 (shortBinaryNumeralTerm sourceCount),
    closedShift 2 (shortBinaryNumeralTerm targetBoundary),
    closedShift 2 (shortBinaryNumeralTerm targetCount),
    closedShift 2 headTerm]

private def natListConsDepthThreeTermsAtValuationHead
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    Fin 11 -> ArithmeticSemiterm Nat 3 :=
  ![#0, #1, #2,
    closedShift 3 (shortBinaryNumeralTerm tokenTable),
    closedShift 3 (shortBinaryNumeralTerm width),
    closedShift 3 (shortBinaryNumeralTerm tokenCount),
    closedShift 3 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 3 (shortBinaryNumeralTerm sourceCount),
    closedShift 3 (shortBinaryNumeralTerm targetBoundary),
    closedShift 3 (shortBinaryNumeralTerm targetCount),
    closedShift 3 headTerm]

private def natListConsDepthFourTermsAtValuationHead
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    Fin 12 -> ArithmeticSemiterm Nat 4 :=
  ![#0, #1, #2, #3,
    closedShift 4 (shortBinaryNumeralTerm tokenTable),
    closedShift 4 (shortBinaryNumeralTerm width),
    closedShift 4 (shortBinaryNumeralTerm tokenCount),
    closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 4 (shortBinaryNumeralTerm sourceCount),
    closedShift 4 (shortBinaryNumeralTerm targetBoundary),
    closedShift 4 (shortBinaryNumeralTerm targetCount),
    closedShift 4 headTerm]

private def natListConsDepthFiveTermsAtValuationHead
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    Fin 13 -> ArithmeticSemiterm Nat 5 :=
  ![#0, #1, #2, #3, #4,
    closedShift 5 (shortBinaryNumeralTerm tokenTable),
    closedShift 5 (shortBinaryNumeralTerm width),
    closedShift 5 (shortBinaryNumeralTerm tokenCount),
    closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
    closedShift 5 (shortBinaryNumeralTerm sourceCount),
    closedShift 5 (shortBinaryNumeralTerm targetBoundary),
    closedShift 5 (shortBinaryNumeralTerm targetCount),
    closedShift 5 headTerm]

private theorem natListConsOuterAtValuationHeadRewriting_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    (Rew.subst (natListConsOuterTermsAtValuationHead tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headTerm)).comp
        (Rew.emb : Rew ℒₒᵣ Empty 8 Nat 8) =
      Rew.embSubsts (natListConsOuterTermsAtValuationHead tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm) := by
  ext coordinate
  · simp [Rew.comp_app]
  · exact Empty.elim coordinate

private theorem natListConsOuterAtValuationHeadQ1_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    (Rew.embSubsts (natListConsOuterTermsAtValuationHead tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headTerm)).q =
      Rew.embSubsts (natListConsDepthOneTermsAtValuationHead tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm) := by
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListConsOuterTermsAtValuationHead,
        natListConsDepthOneTermsAtValuationHead, closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListConsOuterAtValuationHeadQ2_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    (Rew.embSubsts (natListConsOuterTermsAtValuationHead tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headTerm)).q.q =
      Rew.embSubsts (natListConsDepthTwoTermsAtValuationHead tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm) := by
  rw [natListConsOuterAtValuationHeadQ1_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListConsDepthOneTermsAtValuationHead,
        natListConsDepthTwoTermsAtValuationHead, closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListConsOuterAtValuationHeadQ3_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    (Rew.embSubsts (natListConsOuterTermsAtValuationHead tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headTerm)).q.q.q =
      Rew.embSubsts (natListConsDepthThreeTermsAtValuationHead tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm) := by
  rw [natListConsOuterAtValuationHeadQ2_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListConsDepthTwoTermsAtValuationHead,
        natListConsDepthThreeTermsAtValuationHead, closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListConsOuterAtValuationHeadQ4_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    (Rew.embSubsts (natListConsOuterTermsAtValuationHead tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headTerm)).q.q.q.q =
      Rew.embSubsts (natListConsDepthFourTermsAtValuationHead tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm) := by
  rw [natListConsOuterAtValuationHeadQ3_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListConsDepthThreeTermsAtValuationHead,
        natListConsDepthFourTermsAtValuationHead, closedShift, Rew.q]
  · exact Empty.elim coordinate

private theorem natListConsOuterAtValuationHeadQ5_eq_embSubsts
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    (Rew.embSubsts (natListConsOuterTermsAtValuationHead tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headTerm)).q.q.q.q.q =
      Rew.embSubsts (natListConsDepthFiveTermsAtValuationHead tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm) := by
  rw [natListConsOuterAtValuationHeadQ4_eq_embSubsts]
  ext coordinate
  · fin_cases coordinate <;>
      simp [natListConsDepthFourTermsAtValuationHead,
        natListConsDepthFiveTermsAtValuationHead, closedShift, Rew.q]
  · exact Empty.elim coordinate

/-- The original graph formula with the caller's exact head term. -/
def compactAdditiveNatListConsRowsAtValuationHeadFormula
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListConsRowsDef.val) ⇜
    natListConsOuterTermsAtValuationHead tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headTerm

theorem compactAdditiveNatListConsRowsAtValuationHeadFormula_eq_explicitSubstitution
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    compactAdditiveNatListConsRowsAtValuationHeadFormula tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm =
      (Rewriting.emb (ξ := Nat) compactAdditiveNatListConsRowsDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm sourceBoundary,
          shortBinaryNumeralTerm sourceCount,
          shortBinaryNumeralTerm targetBoundary,
          shortBinaryNumeralTerm targetCount,
          headTerm] := by
  rfl

private def compactAdditiveNatListConsRowsHeadTerminalAtValuation
    (tokenTable width tokenCount targetBoundary : Nat)
    (headTerm : ValuationTerm) : ArithmeticSemiformula Nat 2 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
        closedShift 2 (shortBinaryNumeralTerm tokenCount),
        closedShift 2 (unaryNumeralTerm 0),
        (#1 : ArithmeticSemiterm Nat 2)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm targetBoundary),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          closedShift 2 (unaryNumeralTerm 1),
          (#0 : ArithmeticSemiterm Nat 2)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm tokenTable),
          closedShift 2 (shortBinaryNumeralTerm width),
          closedShift 2 (shortBinaryNumeralTerm tokenCount),
          (#1 : ArithmeticSemiterm Nat 2),
          closedShift 2 headTerm,
          (#0 : ArithmeticSemiterm Nat 2)]))

private def compactAdditiveNatListConsRowsHeadBodyAtValuation
    (tokenTable width tokenCount targetBoundary : Nat)
    (headTerm : ValuationTerm) : ValuationFormula :=
  ((compactAdditiveNatListConsRowsHeadTerminalAtValuation tokenTable width
      tokenCount targetBoundary headTerm).bexsLTSucc
        (closedShift 1 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (shortBinaryNumeralTerm tokenCount)

private def compactAdditiveNatListConsRowsExplicitFormulaAtValuationHead
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1” ⋏
    (compactAdditiveNatListConsRowsHeadBodyAtValuation tokenTable width
        tokenCount targetBoundary headTerm ⋏
      (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary).ballLT
          (shortBinaryNumeralTerm sourceCount))

private theorem natListConsSourceCountAtValuationHead_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    Rew.embSubsts
        (natListConsOuterTermsAtValuationHead tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount headTerm) ▹
        (“#6 = #4 + 1” : ArithmeticSemiformula Empty 8) =
      “!!(shortBinaryNumeralTerm targetCount) =
        !!(shortBinaryNumeralTerm sourceCount) + 1” := by
  simp [natListConsOuterTermsAtValuationHead]

private theorem natListConsSourceHeadTerminalAtValuation_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    Rew.embSubsts
        (natListConsDepthTwoTermsAtValuationHead tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount headTerm) ▹
        natListConsSourceHeadTerminal =
      compactAdditiveNatListConsRowsHeadTerminalAtValuation tokenTable width
        tokenCount targetBoundary headTerm := by
  unfold natListConsSourceHeadTerminal
  unfold compactAdditiveNatListConsRowsHeadTerminalAtValuation
  unfold compactAdditiveTokenCellDef
  simp [rewriting_emptyFormulaSubstitution,
    rewriting_embeddedFormulaSubstitution,
    natListConsDepthTwoTermsAtValuationHead, unaryNumeralTerm, closedShift,
    Function.comp_def, Rew.subst_bvar]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Rew.subst_bvar]

private theorem natListConsSourceHeadBodyAtValuation_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    Rew.embSubsts
        (natListConsOuterTermsAtValuationHead tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount headTerm) ▹
        natListConsSourceHeadBody =
      compactAdditiveNatListConsRowsHeadBodyAtValuation tokenTable width
        tokenCount targetBoundary headTerm := by
  unfold natListConsSourceHeadBody
  unfold compactAdditiveNatListConsRowsHeadBodyAtValuation
  rw [rewriting_bexsLTSucc, rewriting_bexsLTSucc]
  rw [natListConsOuterAtValuationHeadQ2_eq_embSubsts,
    natListConsSourceHeadTerminalAtValuation_rewrite,
    natListConsOuterAtValuationHeadQ1_eq_embSubsts]
  simp [natListConsOuterTermsAtValuationHead,
    natListConsDepthOneTermsAtValuationHead, closedShift]

private theorem natListConsSourceTailTerminalAtValuationHead_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    Rew.embSubsts
        (natListConsDepthFiveTermsAtValuationHead tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount headTerm) ▹
        natListConsSourceTailTerminal =
      compactAdditiveNatListConsRowsTailTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  unfold natListConsSourceTailTerminal natListConsSourceTailBitBody
  unfold compactAdditiveNatListConsRowsTailTerminal
  unfold compactAdditiveAtomicRowEqDef
  simp [rewriting_emptyFormulaSubstitution, rewriting_ballLT,
    natListConsDepthFiveTermsAtValuationHead, closedShift,
    Function.comp_def, Rew.subst_bvar, Rew.q]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;> simp

private theorem natListConsSourceTailBodyAtValuationHead_rewrite
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    (Rew.embSubsts
        (natListConsOuterTermsAtValuationHead tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount headTerm)).q ▹
        natListConsSourceTailBody =
      compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  unfold natListConsSourceTailBody
  unfold compactAdditiveNatListConsRowsTailBody
  rw [rewriting_bexsLTSucc, rewriting_bexsLTSucc,
    rewriting_bexsLTSucc, rewriting_bexsLTSucc]
  rw [natListConsOuterAtValuationHeadQ5_eq_embSubsts,
    natListConsSourceTailTerminalAtValuationHead_rewrite,
    natListConsOuterAtValuationHeadQ4_eq_embSubsts,
    natListConsOuterAtValuationHeadQ3_eq_embSubsts,
    natListConsOuterAtValuationHeadQ2_eq_embSubsts,
    natListConsOuterAtValuationHeadQ1_eq_embSubsts]
  simp [natListConsDepthOneTermsAtValuationHead,
    natListConsDepthTwoTermsAtValuationHead,
    natListConsDepthThreeTermsAtValuationHead,
    natListConsDepthFourTermsAtValuationHead, closedShift]

theorem compactAdditiveNatListConsRowsAtValuationHeadFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (headTerm : ValuationTerm) :
    compactAdditiveNatListConsRowsAtValuationHeadFormula tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm =
      compactAdditiveNatListConsRowsExplicitFormulaAtValuationHead tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm := by
  unfold compactAdditiveNatListConsRowsAtValuationHeadFormula
  change Rew.subst
      (natListConsOuterTermsAtValuationHead tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount headTerm) ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 8 Nat 8) ▹
        compactAdditiveNatListConsRowsDef.val) = _
  rw [← TransitiveRewriting.comp_app,
    natListConsOuterAtValuationHeadRewriting_eq_embSubsts]
  rw [compactAdditiveNatListConsRowsDef_val_eq_sourceDecomposed]
  let rewriting := Rew.embSubsts
    (natListConsOuterTermsAtValuationHead tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headTerm)
  change rewriting ▹ natListConsSourceDecomposedFormula =
    compactAdditiveNatListConsRowsExplicitFormulaAtValuationHead tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headTerm
  unfold natListConsSourceDecomposedFormula
  unfold compactAdditiveNatListConsRowsExplicitFormulaAtValuationHead
  simp only [LogicalConnective.HomClass.map_and]
  rw [show rewriting ▹
      (“#6 = #4 + 1” : ArithmeticSemiformula Empty 8) =
        “!!(shortBinaryNumeralTerm targetCount) =
          !!(shortBinaryNumeralTerm sourceCount) + 1” by
        exact natListConsSourceCountAtValuationHead_rewrite tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary targetCount
            headTerm]
  rw [show rewriting ▹ natListConsSourceHeadBody =
      compactAdditiveNatListConsRowsHeadBodyAtValuation tokenTable width
        tokenCount targetBoundary headTerm by
        exact natListConsSourceHeadBodyAtValuation_rewrite tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary targetCount
            headTerm]
  rw [rewriting_ballLT]
  rw [show rewriting.q ▹ natListConsSourceTailBody =
      compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
        sourceBoundary targetBoundary by
        exact natListConsSourceTailBodyAtValuationHead_rewrite tokenTable
          width tokenCount sourceBoundary sourceCount targetBoundary
            targetCount headTerm]
  simp [rewriting, natListConsOuterTermsAtValuationHead]

private theorem
    compactAdditiveNatListConsRowsHeadTerminalAtValuation_substitution_alignment
    (tokenTable width tokenCount targetBoundary targetLeft targetRight : Nat)
    (headTerm : ValuationTerm) :
    (compactAdditiveNatListConsRowsHeadTerminalAtValuation tokenTable width
        tokenCount targetBoundary headTerm) ⇜
        ![shortBinaryNumeralTerm targetRight,
          shortBinaryNumeralTerm targetLeft] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (unaryNumeralTerm 0)
          (shortBinaryNumeralTerm targetLeft) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (unaryNumeralTerm 1)
            (shortBinaryNumeralTerm targetRight) ⋏
          compactAdditiveTokenCellAtValuationFormula
            (shortBinaryNumeralTerm tokenTable)
            (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm targetLeft)
            headTerm
            (shortBinaryNumeralTerm targetRight))) := by
  unfold compactAdditiveNatListConsRowsHeadTerminalAtValuation
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactAdditiveTokenCellAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate
  · constructor
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
      · intro coordinate
        exact Empty.elim coordinate

private noncomputable def
    compactAdditiveNatListConsRowsHeadAtValuationCertificate
    (tokenTable width tokenCount targetBoundary head : Nat)
    (headTerm : ValuationTerm)
    (hheadValue : termValue zeroValuation headTerm = head)
    (data : CompactAdditiveNatListConsHeadData
      tokenTable width tokenCount targetBoundary head) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListConsRowsHeadBodyAtValuation tokenTable width
        tokenCount targetBoundary headTerm) := by
  let values : Fin 2 -> Nat := ![data.targetRight, data.targetLeft]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.targetRight,
          shortBinaryNumeralTerm data.targetLeft] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm targetBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (unaryNumeralTerm 0)
        (shortBinaryNumeralTerm data.targetLeft) (by
          simpa [termValue_shortBinaryNumeralTerm,
            termValue_unaryNumeralTerm] using data.targetLeft_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (unaryNumeralTerm 1)
          (shortBinaryNumeralTerm data.targetRight) (by
            simpa [termValue_shortBinaryNumeralTerm,
              termValue_unaryNumeralTerm] using data.targetRight_entry))
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm data.targetLeft)
          headTerm
          (shortBinaryNumeralTerm data.targetRight) (by
            have hheadValue' : termValue
                FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation
                headTerm = head := by
              rw [show
              FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation =
                zeroValuation by rfl]
              exact hheadValue
            simpa only [termValue_shortBinaryNumeralTerm, hheadValue']
              using data.token_cell)))
  let terminal : HybridCertificate zeroValuation
      ((compactAdditiveNatListConsRowsHeadTerminalAtValuation tokenTable width
          tokenCount targetBoundary headTerm) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveNatListConsRowsHeadTerminalAtValuation_substitution_alignment
          tokenTable width tokenCount targetBoundary data.targetLeft
            data.targetRight headTerm).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
      (compactAdditiveNatListConsRowsHeadTerminalAtValuation tokenTable width
        tokenCount targetBoundary headTerm)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le) terminal
  exact .cast (by
    rw [explicitBoundedWitnessFormula_two_eq]
    rfl) installed

/-- Construct the exact graph formula certificate while preserving the
caller's head term. -/
noncomputable def
    compactAdditiveNatListConsRowsAtValuationHeadFromDataExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat)
    (headTerm : ValuationTerm)
    (hheadValue : termValue zeroValuation headTerm = head)
    (hcount : targetCount = sourceCount + 1)
    (headData : CompactAdditiveNatListConsHeadData
      tokenTable width tokenCount targetBoundary head)
    (tailRows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData
        tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListConsRowsAtValuationHeadFormula tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (countEqualityCertificate sourceCount targetCount hcount)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveNatListConsRowsHeadAtValuationCertificate tokenTable
        width tokenCount targetBoundary head headTerm hheadValue headData)
      (compactAdditiveNatListConsRowsTailUniversalCertificate tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary tailRows))
  exact .cast
    (compactAdditiveNatListConsRowsAtValuationHeadFormula_alignment tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headTerm).symm parts

/-- Extract all row witnesses from the semantic graph and preserve the exact
syntactic head term in the certified formula. -/
noncomputable def
    compactAdditiveNatListConsRowsAtValuationHeadExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount head : Nat)
    (headTerm : ValuationTerm)
    (hheadValue : termValue zeroValuation headTerm = head)
    (hgraph : CompactAdditiveNatListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListConsRowsAtValuationHeadFormula tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
          headTerm) :=
  compactAdditiveNatListConsRowsAtValuationHeadFromDataExplicitHybridCertificate
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount head headTerm hheadValue hgraph.1
    (by
      let targetLeftExists := hgraph.2.1
      let targetLeft := Classical.choose targetLeftExists
      have htargetLeft := Classical.choose_spec targetLeftExists
      let targetRightExists := htargetLeft.2
      let targetRight := Classical.choose targetRightExists
      have htargetRight := Classical.choose_spec targetRightExists
      exact
        { targetLeft := targetLeft
          targetRight := targetRight
          targetLeft_le := htargetLeft.1
          targetRight_le := htargetRight.1
          targetLeft_entry := htargetRight.2.1
          targetRight_entry := htargetRight.2.2.1
          token_cell := htargetRight.2.2.2 })
    (fun index => by
      let sourceLeftExists := hgraph.2.2 index index.isLt
      let sourceLeft := Classical.choose sourceLeftExists
      have hsourceLeft := Classical.choose_spec sourceLeftExists
      let sourceRightExists := hsourceLeft.2
      let sourceRight := Classical.choose sourceRightExists
      have hsourceRight := Classical.choose_spec sourceRightExists
      let targetLeftExists := hsourceRight.2
      let targetLeft := Classical.choose targetLeftExists
      have htargetLeft := Classical.choose_spec targetLeftExists
      let targetRightExists := htargetLeft.2
      let targetRight := Classical.choose targetRightExists
      have htargetRight := Classical.choose_spec targetRightExists
      exact
        { sourceLeft := sourceLeft
          sourceRight := sourceRight
          targetLeft := targetLeft
          targetRight := targetRight
          sourceLeft_le := hsourceLeft.1
          sourceRight_le := hsourceRight.1
          targetLeft_le := htargetLeft.1
          targetRight_le := htargetRight.1
          sourceLeft_entry := htargetRight.2.1
          sourceRight_entry := htargetRight.2.2.1
          targetLeft_entry := htargetRight.2.2.2.1
          targetRight_entry := htargetRight.2.2.2.2.1
          atomic_row_eq := htargetRight.2.2.2.2.2 })

#print axioms compactAdditiveNatListConsRowsClosedFormula_alignment
#print axioms compactAdditiveNatListConsRowsClosedFormula_eq_explicitSubstitution
#print axioms compactAdditiveNatListConsRowsFromDataExplicitHybridCertificate
#print axioms compactAdditiveNatListConsRowsOfGraphExplicitHybridCertificate
#print axioms compactAdditiveNatListConsRowsAtValuationHeadFormula_alignment
#print axioms compactAdditiveNatListConsRowsAtValuationHeadFormula_eq_explicitSubstitution
#print axioms compactAdditiveNatListConsRowsAtValuationHeadFromDataExplicitHybridCertificate
#print axioms compactAdditiveNatListConsRowsAtValuationHeadExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
