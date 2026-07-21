import integration.FoundationCompactNumericListedDirectParserStateAtRows
import integration.FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryHybridCompiler
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

/-!
# Explicit hybrid certificate for one parser-state table row

The right boundary lookup retains the original `index + 1` valuation term;
it is not replaced by a computed numeral.  The final conjunct is the direct
thirteen-coordinate parser-state core certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate

def compactParserStateAtRowsZeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate
    compactParserStateAtRowsZeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

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

noncomputable def compactParserStateAtRowsClosedLtCertificate
    (left right : Nat) (hlt : left < right) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    compactParserStateAtRowsZeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue compactParserStateAtRowsZeroValuation
          (shortBinaryNumeralTerm left) <
        termValue compactParserStateAtRowsZeroValuation
          (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

noncomputable def compactParserStateAtRowsValuationLtCertificate
    (leftTerm : ValuationTerm) (right : Nat)
    (hlt : termValue compactParserStateAtRowsZeroValuation leftTerm < right) :
    HybridCertificate
      “!!leftTerm < !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    compactParserStateAtRowsZeroValuation Language.ORing.Rel.lt
    ![leftTerm, shortBinaryNumeralTerm right] (by
      change termValue compactParserStateAtRowsZeroValuation leftTerm <
        termValue compactParserStateAtRowsZeroValuation
          (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

def compactUnifiedParserStateAtRowsClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserStateAtRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm index,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.tokensFinish,
      shortBinaryNumeralTerm coordinates.tasksFinish,
      shortBinaryNumeralTerm coordinates.tokensBoundary,
      shortBinaryNumeralTerm coordinates.tokensCount,
      shortBinaryNumeralTerm coordinates.tasksBoundary,
      shortBinaryNumeralTerm coordinates.tasksCount,
      shortBinaryNumeralTerm sizeWitness.tokensBoundarySize,
      shortBinaryNumeralTerm sizeWitness.tasksBoundarySize]

def compactUnifiedParserStateAtRowsExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm index) <
      !!(shortBinaryNumeralTerm stateCount)” ⋏
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm index)
        (shortBinaryNumeralTerm coordinates.start) ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm stateBoundary)
          (shortBinaryNumeralTerm tokenCount)
          ‘!!(shortBinaryNumeralTerm index) + 1’
          (shortBinaryNumeralTerm coordinates.finish) ⋏
        compactUnifiedParserStateCoreClosedFormula
          tokenTable width tokenCount
          coordinates.start coordinates.finish
          coordinates.tokensFinish coordinates.tasksFinish
          coordinates.tokensBoundary coordinates.tokensCount
          coordinates.tasksBoundary coordinates.tasksCount
          sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize))

def compactUnifiedParserStateAtRowsAtValuationIndexFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserStateAtRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      indexTerm,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.tokensFinish,
      shortBinaryNumeralTerm coordinates.tasksFinish,
      shortBinaryNumeralTerm coordinates.tokensBoundary,
      shortBinaryNumeralTerm coordinates.tokensCount,
      shortBinaryNumeralTerm coordinates.tasksBoundary,
      shortBinaryNumeralTerm coordinates.tasksCount,
      shortBinaryNumeralTerm sizeWitness.tokensBoundarySize,
      shortBinaryNumeralTerm sizeWitness.tasksBoundarySize]

def compactUnifiedParserStateAtRowsAtValuationIndexExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) :
    ValuationFormula :=
  “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)” ⋏
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount)
        indexTerm
        (shortBinaryNumeralTerm coordinates.start) ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm stateBoundary)
          (shortBinaryNumeralTerm tokenCount)
          ‘!!indexTerm + 1’
          (shortBinaryNumeralTerm coordinates.finish) ⋏
        compactUnifiedParserStateCoreClosedFormula
          tokenTable width tokenCount
          coordinates.start coordinates.finish
          coordinates.tokensFinish coordinates.tasksFinish
          coordinates.tokensBoundary coordinates.tokensCount
          coordinates.tasksBoundary coordinates.tasksCount
          sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize))

theorem compactUnifiedParserStateAtRowsClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) :
    compactUnifiedParserStateAtRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness =
      compactUnifiedParserStateAtRowsExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness := by
  unfold compactUnifiedParserStateAtRowsClosedFormula
  unfold compactUnifiedParserStateAtRowsExplicitFormula
  unfold compactUnifiedParserStateAtRowsDef
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactUnifiedParserStateCoreClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactUnifiedParserStateAtRowsAtValuationIndexFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) :
    compactUnifiedParserStateAtRowsAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm
          coordinates sizeWitness =
      compactUnifiedParserStateAtRowsAtValuationIndexExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm
          coordinates sizeWitness := by
  unfold compactUnifiedParserStateAtRowsAtValuationIndexFormula
  unfold compactUnifiedParserStateAtRowsAtValuationIndexExplicitFormula
  unfold compactUnifiedParserStateAtRowsDef
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactUnifiedParserStateCoreClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

noncomputable def compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness) :
    HybridCertificate
      (compactUnifiedParserStateAtRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness) := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactParserStateAtRowsClosedLtCertificate index stateCount hindex)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        compactParserStateAtRowsZeroValuation
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm index)
        (shortBinaryNumeralTerm coordinates.start) (by
          simpa only [termValue_shortBinaryNumeralTerm] using hstart))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          compactParserStateAtRowsZeroValuation
          (shortBinaryNumeralTerm stateBoundary)
          (shortBinaryNumeralTerm tokenCount)
          nextIndexTerm
          (shortBinaryNumeralTerm coordinates.finish) (by
            simpa [nextIndexTerm, termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using hfinish))
        (compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates sizeWitness hcore)))
  exact .cast
    (compactUnifiedParserStateAtRowsClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness).symm parts

noncomputable def
    compactUnifiedParserStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
        (termValue compactParserStateAtRowsZeroValuation indexTerm)
          coordinates sizeWitness) :
    HybridCertificate
      (compactUnifiedParserStateAtRowsAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm
          coordinates sizeWitness) := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactParserStateAtRowsValuationLtCertificate indexTerm stateCount (by
      simpa [compactParserStateAtRowsZeroValuation] using hindex))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        compactParserStateAtRowsZeroValuation
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount)
        indexTerm
        (shortBinaryNumeralTerm coordinates.start) (by
          simpa [compactParserStateAtRowsZeroValuation,
            termValue_shortBinaryNumeralTerm] using hstart))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          compactParserStateAtRowsZeroValuation
          (shortBinaryNumeralTerm stateBoundary)
          (shortBinaryNumeralTerm tokenCount)
          nextIndexTerm
          (shortBinaryNumeralTerm coordinates.finish) (by
            simpa [nextIndexTerm, compactParserStateAtRowsZeroValuation,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne]
              using hfinish))
        (compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates sizeWitness hcore)))
  exact .cast
    (compactUnifiedParserStateAtRowsAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm
        coordinates sizeWitness).symm parts

#print axioms compactUnifiedParserStateAtRowsClosedFormula_alignment
#print axioms compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph
#print axioms compactUnifiedParserStateAtRowsAtValuationIndexFormula_alignment
#print axioms
  compactUnifiedParserStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
