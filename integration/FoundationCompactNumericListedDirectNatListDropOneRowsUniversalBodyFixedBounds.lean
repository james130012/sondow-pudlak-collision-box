import integration.FoundationCompactNumericListedDirectNatListDropOneRowsTerminalSyntaxFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds

/-!
# Fixed source-terminal and universal-body syntax for drop one

The source terminal has five bound variables: the retained row index and four
entry values.  Four public bounded-witness body steps reduce it to the
one-variable body consumed by the outer row universal.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropOneRowsUniversalBodyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropOneRowsTerminalSyntaxFixedBounds

private def dropOneSourceIndexTermArity05 :
    ArithmeticSemiterm Nat 5 :=
  ‘!!(dropOneClosedShift 5 (fixedNumeralTerm 1)) + #4’

private def dropOneSourceNextTermArity05 :
    ArithmeticSemiterm Nat 5 :=
  ‘(!!(dropOneClosedShift 5 (fixedNumeralTerm 1)) + #4) + 1’

def dropOneRowsUniversalTerminalTermCodePolynomial (bitBound : Nat) : Nat :=
  20 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode dropOneSourceIndexTermArity05).length +
    (binaryTermCode dropOneSourceNextTermArity05).length +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length + 1

def dropOneRowsUniversalTerminalFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let termCode := dropOneRowsUniversalTerminalTermCodePolynomial bitBound
  4 * dropOneRowsBranchTerminalEntryCodePolynomial termCode +
    dropOneRowsBranchTerminalRowCodePolynomial termCode +
      4 * (binaryNatCode 4).length + 1

theorem compactAdditiveNatListDropOneRowsTerminal_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary 1)).length <=
      dropOneRowsUniversalTerminalFormulaCodePolynomial bitBound := by
  let termCode := dropOneRowsUniversalTerminalTermCodePolynomial bitBound
  have hclosedNumeral :
      forall value, Nat.size value <= bitBound ->
        (binaryTermCode
          (dropOneClosedShift 5
            (shortBinaryNumeralTerm value))).length <= termCode := by
    intro value hvalueSize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
    have hshift := dropOneClosedShift_code_length_le
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 5
    dsimp only [termCode]
    unfold dropOneRowsUniversalTerminalTermCodePolynomial
    omega
  have hsourceIndex :
      (binaryTermCode dropOneSourceIndexTermArity05).length <= termCode := by
    dsimp only [termCode]
    unfold dropOneRowsUniversalTerminalTermCodePolynomial
    omega
  have hsourceNext :
      (binaryTermCode dropOneSourceNextTermArity05).length <= termCode := by
    dsimp only [termCode]
    unfold dropOneRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold dropOneRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold dropOneRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold dropOneRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold dropOneRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar4 :
      (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold dropOneRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar4Next :
      (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length <=
        termCode := by
    dsimp only [termCode]
    unfold dropOneRowsUniversalTerminalTermCodePolynomial
    omega
  have htokenTable := hclosedNumeral tokenTable htokenTableSize
  have hwidth := hclosedNumeral width hwidthSize
  have htokenCount := hclosedNumeral tokenCount htokenCountSize
  have hsourceBoundary := hclosedNumeral sourceBoundary hsourceBoundarySize
  have htargetBoundary := hclosedNumeral targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropOneClosedShift 5 (shortBinaryNumeralTerm sourceBoundary),
      dropOneClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      dropOneSourceIndexTermArity05, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropOneClosedShift 5 (shortBinaryNumeralTerm sourceBoundary),
      dropOneClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      dropOneSourceNextTermArity05, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropOneClosedShift 5 (shortBinaryNumeralTerm targetBoundary),
      dropOneClosedShift 5 (shortBinaryNumeralTerm tokenCount), #4, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropOneClosedShift 5 (shortBinaryNumeralTerm targetBoundary),
      dropOneClosedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 5 :=
    ![dropOneClosedShift 5 (shortBinaryNumeralTerm tokenTable),
      dropOneClosedShift 5 (shortBinaryNumeralTerm width),
      dropOneClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      #3, #2, #1, #0]
  have hsourceLeftTerms : forall coordinate,
      (binaryTermCode (sourceLeftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact hsourceBoundary
    · exact htokenCount
    · exact hsourceIndex
    · exact hbvar3
  have hsourceRightTerms : forall coordinate,
      (binaryTermCode (sourceRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact hsourceBoundary
    · exact htokenCount
    · exact hsourceNext
    · exact hbvar2
  have htargetLeftTerms : forall coordinate,
      (binaryTermCode (targetLeftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htargetBoundary
    · exact htokenCount
    · exact hbvar4
    · exact hbvar1
  have htargetRightTerms : forall coordinate,
      (binaryTermCode (targetRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htargetBoundary
    · exact htokenCount
    · exact hbvar4Next
    · exact hbvar0
  have hrowTerms : forall coordinate,
      (binaryTermCode (rowTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTable
    · exact hwidth
    · exact htokenCount
    · exact hbvar3
    · exact hbvar2
    · exact hbvar1
    · exact hbvar0
  let sourceLeftFormula : ArithmeticSemiformula Nat 5 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      sourceLeftTerms
  let sourceRightFormula : ArithmeticSemiformula Nat 5 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      sourceRightTerms
  let targetLeftFormula : ArithmeticSemiformula Nat 5 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      targetLeftTerms
  let targetRightFormula : ArithmeticSemiformula Nat 5 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      targetRightTerms
  let rowFormula : ArithmeticSemiformula Nat 5 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜ rowTerms
  have hfive := dropOneRowsFiveLeafFormula_code_length_le
    sourceLeftTerms sourceRightTerms targetLeftTerms targetRightTerms rowTerms
    termCode hsourceLeftTerms hsourceRightTerms htargetLeftTerms
    htargetRightTerms hrowTerms
  unfold compactAdditiveNatListDropFixedNumeralRowsTerminal
  change
    (binaryFormulaCode
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula))))).length <=
      dropOneRowsUniversalTerminalFormulaCodePolynomial bitBound
  simpa only [dropOneRowsUniversalTerminalFormulaCodePolynomial, termCode,
    sourceLeftFormula, sourceRightFormula, targetLeftFormula,
    targetRightFormula, rowFormula] using hfive

def dropOneRowsBodyCodeAfter04Polynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 4 numericBound
    (dropOneRowsUniversalTerminalFormulaCodePolynomial bitBound)

def dropOneRowsBodyCodeAfter03Polynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
    (dropOneRowsBodyCodeAfter04Polynomial numericBound bitBound)

def dropOneRowsBodyCodeAfter02Polynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
    (dropOneRowsBodyCodeAfter03Polynomial numericBound bitBound)

def dropOneRowsUniversalBodyFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
    (dropOneRowsBodyCodeAfter02Polynomial numericBound bitBound)

private theorem dropOneArithmeticOne_freeVariables_eq_empty
    {Variable : Type*} [DecidableEq Variable] {arity : Nat} :
    (‘1’ : ArithmeticSemiterm Variable arity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem dropOneArithmeticAdd_freeVariables
    {Variable : Type*} [DecidableEq Variable] {arity : Nat}
    (left right : ArithmeticSemiterm Variable arity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable arity).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

@[simp] private theorem dropOneClosedShiftShortNumeral_freeVariables_eq_empty
    (arity value : Nat) :
    (dropOneClosedShift arity
      (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
  induction arity with
  | zero =>
      simpa only [dropOneClosedShift] using
        shortBinaryNumeralTerm_freeVariables_eq_empty value
  | succ arity ih =>
      simp only [dropOneClosedShift]
      exact bShift_freeVariables_eq_empty_of_empty _ ih

@[simp] private theorem dropOneClosedShiftFixedOne_freeVariables_eq_empty
    (arity : Nat) :
    (dropOneClosedShift arity
      (fixedNumeralTerm 1)).freeVariables = ∅ := by
  have hbase :
      (fixedNumeralTerm 1).freeVariables = ∅ := by
    unfold fixedNumeralTerm Semiterm.Operator.operator
    simp
  induction arity with
  | zero => simpa only [dropOneClosedShift] using hbase
  | succ arity ih =>
      simp only [dropOneClosedShift]
      exact bShift_freeVariables_eq_empty_of_empty _ ih

private def dropOneRowsClosedTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 5 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropOneClosedShift 5 (shortBinaryNumeralTerm sourceBoundary),
        dropOneClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        ‘!!(dropOneClosedShift 5 (fixedNumeralTerm 1)) + #4’,
        (#3 : ArithmeticSemiterm Nat 5)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![dropOneClosedShift 5 (shortBinaryNumeralTerm sourceBoundary),
          dropOneClosedShift 5 (shortBinaryNumeralTerm tokenCount),
          ‘(!!(dropOneClosedShift 5 (fixedNumeralTerm 1)) + #4) + 1’,
          (#2 : ArithmeticSemiterm Nat 5)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![dropOneClosedShift 5 (shortBinaryNumeralTerm targetBoundary),
            dropOneClosedShift 5 (shortBinaryNumeralTerm tokenCount), #4,
            (#1 : ArithmeticSemiterm Nat 5)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![dropOneClosedShift 5 (shortBinaryNumeralTerm targetBoundary),
              dropOneClosedShift 5 (shortBinaryNumeralTerm tokenCount),
              ‘#4 + 1’, (#0 : ArithmeticSemiterm Nat 5)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜
            ![dropOneClosedShift 5 (shortBinaryNumeralTerm tokenTable),
              dropOneClosedShift 5 (shortBinaryNumeralTerm width),
              dropOneClosedShift 5 (shortBinaryNumeralTerm tokenCount),
              #3, #2, #1, #0]))))

private theorem
    compactAdditiveNatListDropOneRowsTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary 1).freeVariables = ∅ := by
  rw [show
    compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary 1 =
      dropOneRowsClosedTerminal tokenTable width tokenCount sourceBoundary
        targetBoundary by rfl]
  unfold dropOneRowsClosedTerminal
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    Finset.union_eq_empty]
  repeat' apply And.intro
  all_goals
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate <;>
      simp [dropOneArithmeticAdd_freeVariables,
        dropOneArithmeticOne_freeVariables_eq_empty]

private theorem dropOneBexsLTSucc_freeVariables_eq_empty
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity)
    (hbody : body.freeVariables = ∅)
    (hbound : bound.freeVariables = ∅) :
    (body.bexsLTSucc bound).freeVariables = ∅ := by
  have hone : (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ :=
    dropOneArithmeticOne_freeVariables_eq_empty
  have hsuccessor :
      (‘!!bound + 1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    rw [dropOneArithmeticAdd_freeVariables, hbound, hone]
    simp
  have hshifted :
      (Rew.bShift
        (‘!!bound + 1’ : ArithmeticSemiterm Nat arity)).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty _ hsuccessor
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
    LO.FirstOrder.Semiformula.bexsLT LO.FirstOrder.bexs
  rw [LO.FirstOrder.Semiformula.freeVariables_exs,
    LO.FirstOrder.Semiformula.freeVariables_and,
    lessThanFormula_freeVariables, hshifted, hbody]
  simp

@[simp] theorem
    compactAdditiveNatListDropOneRowsBody_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 1).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary 1
  let bound4 := dropOneClosedShift 4 (shortBinaryNumeralTerm tokenCount)
  let bound3 := dropOneClosedShift 3 (shortBinaryNumeralTerm tokenCount)
  let bound2 := dropOneClosedShift 2 (shortBinaryNumeralTerm tokenCount)
  let bound1 := dropOneClosedShift 1 (shortBinaryNumeralTerm tokenCount)
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    exact compactAdditiveNatListDropOneRowsTerminal_freeVariables_eq_empty
      tokenTable width tokenCount sourceBoundary targetBoundary
  have hbound4 : bound4.freeVariables = ∅ := by
    simp only [bound4, dropOneClosedShiftShortNumeral_freeVariables_eq_empty]
  have hbound3 : bound3.freeVariables = ∅ := by
    simp only [bound3, dropOneClosedShiftShortNumeral_freeVariables_eq_empty]
  have hbound2 : bound2.freeVariables = ∅ := by
    simp only [bound2, dropOneClosedShiftShortNumeral_freeVariables_eq_empty]
  have hbound1 : bound1.freeVariables = ∅ := by
    simp only [bound1, dropOneClosedShiftShortNumeral_freeVariables_eq_empty]
  have hstep4 := dropOneBexsLTSucc_freeVariables_eq_empty
    terminal bound4 hterminal hbound4
  have hstep3 := dropOneBexsLTSucc_freeVariables_eq_empty
    (terminal.bexsLTSucc bound4) bound3 hstep4 hbound3
  have hstep2 := dropOneBexsLTSucc_freeVariables_eq_empty
    ((terminal.bexsLTSucc bound4).bexsLTSucc bound3) bound2
    hstep3 hbound2
  have hstep1 := dropOneBexsLTSucc_freeVariables_eq_empty
    (((terminal.bexsLTSucc bound4).bexsLTSucc bound3).bexsLTSucc bound2)
    bound1 hstep2 hbound1
  change
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 1).freeVariables = ∅
  rw [show
    compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary 1 =
      ((((compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
          tokenCount sourceBoundary targetBoundary 1).bexsLTSucc
            (dropOneClosedShift 4
              (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
          (dropOneClosedShift 3
            (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
        (dropOneClosedShift 2
          (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
        (dropOneClosedShift 1
          (shortBinaryNumeralTerm tokenCount)) by rfl]
  exact hstep1

@[simp] theorem
    compactAdditiveNatListDropOneRowsOuterFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary
      targetCount : Nat) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm targetCount))
      (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 1)).freeVariables = ∅ := by
  have hshift :
      (Rew.bShift
        (shortBinaryNumeralTerm targetCount : ValuationTerm)).freeVariables =
          ∅ :=
    bShift_freeVariables_eq_empty_of_empty _
      (shortBinaryNumeralTerm_freeVariables_eq_empty targetCount)
  have htermBound :
      (termBoundFormula
        (Rew.bShift
          (shortBinaryNumeralTerm targetCount : ValuationTerm))).freeVariables =
          ∅ := by
    unfold termBoundFormula
      FoundationCompactPAFiniteCaseSyntax.finiteCaseLessThanFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro candidate hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => simp at hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            change candidate ∈
              (Rew.bShift
                (shortBinaryNumeralTerm targetCount :
                  ValuationTerm)).freeVariables at hcoordinate
            rw [hshift] at hcoordinate
            simp at hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  simp only [LO.FirstOrder.Semiformula.freeVariables_all,
    termBoundedUniversalBody, LO.FirstOrder.Semiformula.freeVariables_imp,
    htermBound,
    compactAdditiveNatListDropOneRowsBody_freeVariables_eq_empty]
  simp

theorem compactAdditiveNatListDropOneRowsBody_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 1)).length <=
      dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
  let terminal :=
    compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary 1
  let after04 : ArithmeticSemiformula Nat 4 :=
    terminal.bexsLTSucc
      (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
        4 (shortBinaryNumeralTerm tokenCount))
  let after03 : ArithmeticSemiformula Nat 3 :=
    after04.bexsLTSucc
      (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
        3 (shortBinaryNumeralTerm tokenCount))
  let after02 : ArithmeticSemiformula Nat 2 :=
    after03.bexsLTSucc
      (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
        2 (shortBinaryNumeralTerm tokenCount))
  let after01 : ArithmeticSemiformula Nat 1 :=
    after02.bexsLTSucc
      (FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift
        1 (shortBinaryNumeralTerm tokenCount))
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hterminal :
      (binaryFormulaCode terminal).length <=
        dropOneRowsUniversalTerminalFormulaCodePolynomial bitBound := by
    dsimp only [terminal]
    exact compactAdditiveNatListDropOneRowsTerminal_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary bitBound
      htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
      htargetBoundarySize
  have h04raw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public
      tokenCount (dropOneRowsUniversalTerminalFormulaCodePolynomial bitBound)
      terminal hterminal
  have h04mono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      4 htokenCount
      (Nat.le_refl
        (dropOneRowsUniversalTerminalFormulaCodePolynomial bitBound))
  have h04 :
      (binaryFormulaCode after04).length <=
        dropOneRowsBodyCodeAfter04Polynomial numericBound bitBound := by
    simpa only [after04, dropOneRowsBodyCodeAfter04Polynomial,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using h04raw.trans h04mono
  have h03raw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (dropOneRowsBodyCodeAfter04Polynomial numericBound bitBound)
      after04 h04
  have h03mono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      3 htokenCount
      (Nat.le_refl (dropOneRowsBodyCodeAfter04Polynomial numericBound bitBound))
  have h03 :
      (binaryFormulaCode after03).length <=
        dropOneRowsBodyCodeAfter03Polynomial numericBound bitBound := by
    simpa only [after03, dropOneRowsBodyCodeAfter03Polynomial,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using h03raw.trans h03mono
  have h02raw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (dropOneRowsBodyCodeAfter03Polynomial numericBound bitBound)
      after03 h03
  have h02mono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      2 htokenCount
      (Nat.le_refl (dropOneRowsBodyCodeAfter03Polynomial numericBound bitBound))
  have h02 :
      (binaryFormulaCode after02).length <=
        dropOneRowsBodyCodeAfter02Polynomial numericBound bitBound := by
    simpa only [after02, dropOneRowsBodyCodeAfter02Polynomial,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using h02raw.trans h02mono
  have h01raw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (dropOneRowsBodyCodeAfter02Polynomial numericBound bitBound)
      after02 h02
  have h01mono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      1 htokenCount
      (Nat.le_refl (dropOneRowsBodyCodeAfter02Polynomial numericBound bitBound))
  have h01 :
      (binaryFormulaCode after01).length <=
        dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
    simpa only [after01, dropOneRowsUniversalBodyFormulaCodePolynomial,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using h01raw.trans h01mono
  unfold compactAdditiveNatListDropFixedNumeralRowsBody
  change (binaryFormulaCode after01).length <=
    dropOneRowsUniversalBodyFormulaCodePolynomial numericBound bitBound
  exact h01

#print axioms compactAdditiveNatListDropOneRowsTerminal_code_length_le_fixed
#print axioms compactAdditiveNatListDropOneRowsOuterFormula_freeVariables_eq_empty
#print axioms compactAdditiveNatListDropOneRowsBody_code_length_le_fixed

end FoundationCompactNumericListedDirectNatListDropOneRowsUniversalBodyFixedBounds
