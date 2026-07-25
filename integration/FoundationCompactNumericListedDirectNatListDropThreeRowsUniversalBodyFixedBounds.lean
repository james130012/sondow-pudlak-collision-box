import integration.FoundationCompactNumericListedDirectNatListDropThreeRowsTerminalSyntaxFixedBounds
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

namespace FoundationCompactNumericListedDirectNatListDropThreeRowsUniversalBodyFixedBounds

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
open FoundationCompactNumericListedDirectNatListDropThreeRowsTerminalSyntaxFixedBounds

private def dropThreeSourceIndexTermArity05 :
    ArithmeticSemiterm Nat 5 :=
  ‘!!(dropThreeClosedShift 5 (fixedNumeralTerm 3)) + #4’

private def dropThreeSourceNextTermArity05 :
    ArithmeticSemiterm Nat 5 :=
  ‘(!!(dropThreeClosedShift 5 (fixedNumeralTerm 3)) + #4) + 1’

def dropThreeRowsUniversalTerminalTermCodePolynomial (bitBound : Nat) : Nat :=
  20 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode dropThreeSourceIndexTermArity05).length +
    (binaryTermCode dropThreeSourceNextTermArity05).length +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length + 1

def dropThreeRowsUniversalTerminalFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let termCode := dropThreeRowsUniversalTerminalTermCodePolynomial bitBound
  4 * dropThreeRowsBranchTerminalEntryCodePolynomial termCode +
    dropThreeRowsBranchTerminalRowCodePolynomial termCode +
      4 * (binaryNatCode 4).length + 1

theorem compactAdditiveNatListDropThreeRowsTerminal_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary 3)).length <=
      dropThreeRowsUniversalTerminalFormulaCodePolynomial bitBound := by
  let termCode := dropThreeRowsUniversalTerminalTermCodePolynomial bitBound
  have hclosedNumeral :
      forall value, Nat.size value <= bitBound ->
        (binaryTermCode
          (dropThreeClosedShift 5
            (shortBinaryNumeralTerm value))).length <= termCode := by
    intro value hvalueSize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
    have hshift := dropThreeClosedShift_code_length_le
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 5
    dsimp only [termCode]
    unfold dropThreeRowsUniversalTerminalTermCodePolynomial
    omega
  have hsourceIndex :
      (binaryTermCode dropThreeSourceIndexTermArity05).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsUniversalTerminalTermCodePolynomial
    omega
  have hsourceNext :
      (binaryTermCode dropThreeSourceNextTermArity05).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar4 :
      (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsUniversalTerminalTermCodePolynomial
    omega
  have hbvar4Next :
      (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length <=
        termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsUniversalTerminalTermCodePolynomial
    omega
  have htokenTable := hclosedNumeral tokenTable htokenTableSize
  have hwidth := hclosedNumeral width hwidthSize
  have htokenCount := hclosedNumeral tokenCount htokenCountSize
  have hsourceBoundary := hclosedNumeral sourceBoundary hsourceBoundarySize
  have htargetBoundary := hclosedNumeral targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropThreeClosedShift 5 (shortBinaryNumeralTerm sourceBoundary),
      dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      dropThreeSourceIndexTermArity05, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropThreeClosedShift 5 (shortBinaryNumeralTerm sourceBoundary),
      dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      dropThreeSourceNextTermArity05, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropThreeClosedShift 5 (shortBinaryNumeralTerm targetBoundary),
      dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenCount), #4, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropThreeClosedShift 5 (shortBinaryNumeralTerm targetBoundary),
      dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 5 :=
    ![dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenTable),
      dropThreeClosedShift 5 (shortBinaryNumeralTerm width),
      dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenCount),
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
  have hfive := dropThreeRowsFiveLeafFormula_code_length_le
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
      dropThreeRowsUniversalTerminalFormulaCodePolynomial bitBound
  simpa only [dropThreeRowsUniversalTerminalFormulaCodePolynomial, termCode,
    sourceLeftFormula, sourceRightFormula, targetLeftFormula,
    targetRightFormula, rowFormula] using hfive

def dropThreeRowsBodyCodeAfter04Polynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 4 numericBound
    (dropThreeRowsUniversalTerminalFormulaCodePolynomial bitBound)

def dropThreeRowsBodyCodeAfter03Polynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
    (dropThreeRowsBodyCodeAfter04Polynomial numericBound bitBound)

def dropThreeRowsBodyCodeAfter02Polynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
    (dropThreeRowsBodyCodeAfter03Polynomial numericBound bitBound)

def dropThreeRowsUniversalBodyFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
    (dropThreeRowsBodyCodeAfter02Polynomial numericBound bitBound)

private theorem dropThreeArithmeticOne_freeVariables_eq_empty
    {Variable : Type*} [DecidableEq Variable] {arity : Nat} :
    (‘1’ : ArithmeticSemiterm Variable arity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem dropThreeArithmeticAdd_freeVariables
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

@[simp] private theorem dropThreeClosedShiftShortNumeral_freeVariables_eq_empty
    (arity value : Nat) :
    (dropThreeClosedShift arity
      (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
  induction arity with
  | zero =>
      simpa only [dropThreeClosedShift] using
        shortBinaryNumeralTerm_freeVariables_eq_empty value
  | succ arity ih =>
      simp only [dropThreeClosedShift]
      exact bShift_freeVariables_eq_empty_of_empty _ ih

@[simp] private theorem dropThreeClosedShiftFixedOne_freeVariables_eq_empty
    (arity : Nat) :
    (dropThreeClosedShift arity
      (fixedNumeralTerm 3)).freeVariables = ∅ := by
  have hbase :
      (fixedNumeralTerm 3).freeVariables = ∅ := by
    unfold fixedNumeralTerm Semiterm.Operator.operator
    simp
  induction arity with
  | zero => simpa only [dropThreeClosedShift] using hbase
  | succ arity ih =>
      simp only [dropThreeClosedShift]
      exact bShift_freeVariables_eq_empty_of_empty _ ih

private def dropThreeRowsClosedTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 5 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropThreeClosedShift 5 (shortBinaryNumeralTerm sourceBoundary),
        dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        ‘!!(dropThreeClosedShift 5 (fixedNumeralTerm 3)) + #4’,
        (#3 : ArithmeticSemiterm Nat 5)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![dropThreeClosedShift 5 (shortBinaryNumeralTerm sourceBoundary),
          dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenCount),
          ‘(!!(dropThreeClosedShift 5 (fixedNumeralTerm 3)) + #4) + 1’,
          (#2 : ArithmeticSemiterm Nat 5)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![dropThreeClosedShift 5 (shortBinaryNumeralTerm targetBoundary),
            dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenCount), #4,
            (#1 : ArithmeticSemiterm Nat 5)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![dropThreeClosedShift 5 (shortBinaryNumeralTerm targetBoundary),
              dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenCount),
              ‘#4 + 1’, (#0 : ArithmeticSemiterm Nat 5)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜
            ![dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenTable),
              dropThreeClosedShift 5 (shortBinaryNumeralTerm width),
              dropThreeClosedShift 5 (shortBinaryNumeralTerm tokenCount),
              #3, #2, #1, #0]))))

private theorem
    compactAdditiveNatListDropThreeRowsTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary 3).freeVariables = ∅ := by
  rw [show
    compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary 3 =
      dropThreeRowsClosedTerminal tokenTable width tokenCount sourceBoundary
        targetBoundary by rfl]
  unfold dropThreeRowsClosedTerminal
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    Finset.union_eq_empty]
  repeat' apply And.intro
  all_goals
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate <;>
      simp [dropThreeArithmeticAdd_freeVariables,
        dropThreeArithmeticOne_freeVariables_eq_empty]

private theorem dropThreeBexsLTSucc_freeVariables_eq_empty
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity)
    (hbody : body.freeVariables = ∅)
    (hbound : bound.freeVariables = ∅) :
    (body.bexsLTSucc bound).freeVariables = ∅ := by
  have hone : (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ :=
    dropThreeArithmeticOne_freeVariables_eq_empty
  have hsuccessor :
      (‘!!bound + 1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    rw [dropThreeArithmeticAdd_freeVariables, hbound, hone]
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
    compactAdditiveNatListDropThreeRowsBody_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 3).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary 3
  let bound4 := dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount)
  let bound3 := dropThreeClosedShift 3 (shortBinaryNumeralTerm tokenCount)
  let bound2 := dropThreeClosedShift 2 (shortBinaryNumeralTerm tokenCount)
  let bound1 := dropThreeClosedShift 1 (shortBinaryNumeralTerm tokenCount)
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    exact compactAdditiveNatListDropThreeRowsTerminal_freeVariables_eq_empty
      tokenTable width tokenCount sourceBoundary targetBoundary
  have hbound4 : bound4.freeVariables = ∅ := by
    simp only [bound4, dropThreeClosedShiftShortNumeral_freeVariables_eq_empty]
  have hbound3 : bound3.freeVariables = ∅ := by
    simp only [bound3, dropThreeClosedShiftShortNumeral_freeVariables_eq_empty]
  have hbound2 : bound2.freeVariables = ∅ := by
    simp only [bound2, dropThreeClosedShiftShortNumeral_freeVariables_eq_empty]
  have hbound1 : bound1.freeVariables = ∅ := by
    simp only [bound1, dropThreeClosedShiftShortNumeral_freeVariables_eq_empty]
  have hstep4 := dropThreeBexsLTSucc_freeVariables_eq_empty
    terminal bound4 hterminal hbound4
  have hstep3 := dropThreeBexsLTSucc_freeVariables_eq_empty
    (terminal.bexsLTSucc bound4) bound3 hstep4 hbound3
  have hstep2 := dropThreeBexsLTSucc_freeVariables_eq_empty
    ((terminal.bexsLTSucc bound4).bexsLTSucc bound3) bound2
    hstep3 hbound2
  have hstep1 := dropThreeBexsLTSucc_freeVariables_eq_empty
    (((terminal.bexsLTSucc bound4).bexsLTSucc bound3).bexsLTSucc bound2)
    bound1 hstep2 hbound1
  change
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 3).freeVariables = ∅
  rw [show
    compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary 3 =
      ((((compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
          tokenCount sourceBoundary targetBoundary 3).bexsLTSucc
            (dropThreeClosedShift 4
              (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
          (dropThreeClosedShift 3
            (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
        (dropThreeClosedShift 2
          (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
        (dropThreeClosedShift 1
          (shortBinaryNumeralTerm tokenCount)) by rfl]
  exact hstep1

@[simp] theorem
    compactAdditiveNatListDropThreeRowsOuterFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary
      targetCount : Nat) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm targetCount))
      (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 3)).freeVariables = ∅ := by
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
    compactAdditiveNatListDropThreeRowsBody_freeVariables_eq_empty]
  simp

theorem compactAdditiveNatListDropThreeRowsBody_code_length_le_fixed
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
        tokenCount sourceBoundary targetBoundary 3)).length <=
      dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
  let terminal :=
    compactAdditiveNatListDropFixedNumeralRowsTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary 3
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
        dropThreeRowsUniversalTerminalFormulaCodePolynomial bitBound := by
    dsimp only [terminal]
    exact compactAdditiveNatListDropThreeRowsTerminal_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary bitBound
      htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
      htargetBoundarySize
  have h04raw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public
      tokenCount (dropThreeRowsUniversalTerminalFormulaCodePolynomial bitBound)
      terminal hterminal
  have h04mono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      4 htokenCount
      (Nat.le_refl
        (dropThreeRowsUniversalTerminalFormulaCodePolynomial bitBound))
  have h04 :
      (binaryFormulaCode after04).length <=
        dropThreeRowsBodyCodeAfter04Polynomial numericBound bitBound := by
    simpa only [after04, dropThreeRowsBodyCodeAfter04Polynomial,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using h04raw.trans h04mono
  have h03raw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (dropThreeRowsBodyCodeAfter04Polynomial numericBound bitBound)
      after04 h04
  have h03mono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      3 htokenCount
      (Nat.le_refl (dropThreeRowsBodyCodeAfter04Polynomial numericBound bitBound))
  have h03 :
      (binaryFormulaCode after03).length <=
        dropThreeRowsBodyCodeAfter03Polynomial numericBound bitBound := by
    simpa only [after03, dropThreeRowsBodyCodeAfter03Polynomial,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using h03raw.trans h03mono
  have h02raw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (dropThreeRowsBodyCodeAfter03Polynomial numericBound bitBound)
      after03 h03
  have h02mono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      2 htokenCount
      (Nat.le_refl (dropThreeRowsBodyCodeAfter03Polynomial numericBound bitBound))
  have h02 :
      (binaryFormulaCode after02).length <=
        dropThreeRowsBodyCodeAfter02Polynomial numericBound bitBound := by
    simpa only [after02, dropThreeRowsBodyCodeAfter02Polynomial,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using h02raw.trans h02mono
  have h01raw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public tokenCount
      (dropThreeRowsBodyCodeAfter02Polynomial numericBound bitBound)
      after02 h02
  have h01mono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      1 htokenCount
      (Nat.le_refl (dropThreeRowsBodyCodeAfter02Polynomial numericBound bitBound))
  have h01 :
      (binaryFormulaCode after01).length <=
        dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
    simpa only [after01, dropThreeRowsUniversalBodyFormulaCodePolynomial,
      FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
      using h01raw.trans h01mono
  unfold compactAdditiveNatListDropFixedNumeralRowsBody
  change (binaryFormulaCode after01).length <=
    dropThreeRowsUniversalBodyFormulaCodePolynomial numericBound bitBound
  exact h01

#print axioms compactAdditiveNatListDropThreeRowsTerminal_code_length_le_fixed
#print axioms compactAdditiveNatListDropThreeRowsOuterFormula_freeVariables_eq_empty
#print axioms compactAdditiveNatListDropThreeRowsBody_code_length_le_fixed

end FoundationCompactNumericListedDirectNatListDropThreeRowsUniversalBodyFixedBounds

