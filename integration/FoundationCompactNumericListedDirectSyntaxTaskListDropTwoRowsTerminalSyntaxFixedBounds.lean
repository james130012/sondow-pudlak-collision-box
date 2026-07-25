import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed syntax bound for the syntax-task drop-two terminal

The consumed count is the fixed native numeral `2`.  Hence the two shifted
source-index terms have constant code; all remaining closed parameters are
controlled by the common bit bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 240000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsTerminalSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate

def dropTwoClosedShift :
    (arity : Nat) ->
      FoundationCompactPAValuationTermCompiler.ValuationTerm ->
      ArithmeticSemiterm Nat arity
  | 0, term => term
  | arity + 1, term => Rew.bShift (dropTwoClosedShift arity term)

private def dropTwoSourceIndexTermArity04 :
    ArithmeticSemiterm Nat 4 :=
  ‘!!(dropTwoClosedShift 4 (fixedNumeralTerm 2)) + &0’

private def dropTwoSourceNextTermArity04 :
    ArithmeticSemiterm Nat 4 :=
  ‘(!!(dropTwoClosedShift 4 (fixedNumeralTerm 2)) + &0) + 1’

def taskDropTwoTerminalTermCodePolynomial (bitBound : Nat) : Nat :=
  16 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode dropTwoSourceIndexTermArity04).length +
    (binaryTermCode dropTwoSourceNextTermArity04).length +
    (binaryTermCode (&0 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (‘&0 + 1’ : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length + 1

def taskDropTwoTerminalEntryCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def taskDropTwoTerminalRowCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val)).length

def taskDropTwoTerminalFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := taskDropTwoTerminalTermCodePolynomial bitBound
  4 * taskDropTwoTerminalEntryCodePolynomial termCode +
    taskDropTwoTerminalRowCodePolynomial termCode +
    4 * (binaryNatCode 4).length + 1

def taskDropTwoBranchTerminalExplicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  let sourceLeft :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropTwoClosedShift 4 (shortBinaryNumeralTerm sourceBoundary),
        dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount),
        dropTwoSourceIndexTermArity04, #3]
  let sourceRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropTwoClosedShift 4 (shortBinaryNumeralTerm sourceBoundary),
        dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount),
        dropTwoSourceNextTermArity04, #2]
  let targetLeft :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropTwoClosedShift 4 (shortBinaryNumeralTerm targetBoundary),
        dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount), &0, #1]
  let targetRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropTwoClosedShift 4 (shortBinaryNumeralTerm targetBoundary),
        dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #0]
  let row :=
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      ![dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenTable),
        dropTwoClosedShift 4 (shortBinaryNumeralTerm width),
        dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount),
        #3, #2, #1, #0]
  sourceLeft ⋏ (sourceRight ⋏ (targetLeft ⋏ (targetRight ⋏ row)))

private theorem dropTwoClosedShift_symbolCount
    (term : FoundationCompactPAValuationTermCompiler.ValuationTerm) :
    forall arity,
      termSymbolCount (dropTwoClosedShift arity term) = termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [dropTwoClosedShift, termSymbolCount_bShift,
        dropTwoClosedShift_symbolCount term arity]

private theorem dropTwoClosedShift_code_length_le
    (term : FoundationCompactPAValuationTermCompiler.ValuationTerm)
    (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    forall arity,
      (binaryTermCode (dropTwoClosedShift arity term)).length <=
        (2 * arity + 1) * bound
  | 0 => by
      simpa only [dropTwoClosedShift, Nat.mul_zero, Nat.zero_add, Nat.one_mul]
        using hterm
  | arity + 1 => by
      have hinduction :=
        dropTwoClosedShift_code_length_le term bound hterm arity
      have hsymbols : termSymbolCount term <= bound :=
        (termSymbolCount_le_binaryTermCode_length term).trans hterm
      have hshiftSymbols :
          termSymbolCount (dropTwoClosedShift arity term) <= bound := by
        rw [dropTwoClosedShift_symbolCount]
        exact hsymbols
      have hshift :=
        binaryTermCode_bShift_length_le_add_symbols
          (dropTwoClosedShift arity term)
      have hcoefficient :
          (2 * (arity + 1) + 1) * bound =
            (2 * arity + 1) * bound + 2 * bound := by
        ring
      simp only [dropTwoClosedShift]
      rw [hcoefficient]
      omega

private theorem dropTwoClosedShift_freeVariables_eq_empty
    (term : FoundationCompactPAValuationTermCompiler.ValuationTerm)
    (hterm : term.freeVariables = ∅) :
    forall arity, (dropTwoClosedShift arity term).freeVariables = ∅
  | 0 => hterm
  | arity + 1 => by
      simp only [dropTwoClosedShift]
      exact bShift_freeVariables_eq_empty_of_empty _
        (dropTwoClosedShift_freeVariables_eq_empty term hterm arity)

private theorem dropTwoShiftedShortNumeral_freeVariables_subset
    (value : Nat) :
    (dropTwoClosedShift 4
      (shortBinaryNumeralTerm value)).freeVariables ⊆ {0} := by
  rw [dropTwoClosedShift_freeVariables_eq_empty _
    (shortBinaryNumeralTerm_freeVariables_eq_empty value) 4]
  simp

private theorem binaryFunctionTerm_freeVariables_dropTwoArity04
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ArithmeticSemiterm Nat 4) :
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
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr
        ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr
        ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticOneArity04_freeVariables_eq_empty :
    (‘1’ : ArithmeticSemiterm Nat 4).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem fixedNumeralTwo_freeVariables_eq_empty :
    (fixedNumeralTerm 2).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

private theorem dropTwoSourceIndexArity04_freeVariables_subset :
    dropTwoSourceIndexTermArity04.freeVariables ⊆ {0} := by
  unfold dropTwoSourceIndexTermArity04
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![dropTwoClosedShift 4 (fixedNumeralTerm 2),
        (&0 : ArithmeticSemiterm Nat 4)]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropTwoArity04,
    dropTwoClosedShift_freeVariables_eq_empty _
      fixedNumeralTwo_freeVariables_eq_empty 4]
  simp

private theorem dropTwoSourceNextArity04_freeVariables_subset :
    dropTwoSourceNextTermArity04.freeVariables ⊆ {0} := by
  unfold dropTwoSourceNextTermArity04
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![LO.FirstOrder.Semiterm.func Language.Add.add
        ![dropTwoClosedShift 4 (fixedNumeralTerm 2),
          (&0 : ArithmeticSemiterm Nat 4)], ‘1’]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropTwoArity04,
    binaryFunctionTerm_freeVariables_dropTwoArity04,
    dropTwoClosedShift_freeVariables_eq_empty _
      fixedNumeralTwo_freeVariables_eq_empty 4,
    arithmeticOneArity04_freeVariables_eq_empty]
  simp

private theorem dropTwoTargetIndexArity04_freeVariables_subset :
    ((&0 : ArithmeticSemiterm Nat 4).freeVariables) ⊆ {0} := by
  simp

private theorem dropTwoTargetNextArity04_freeVariables_subset :
    ((‘&0 + 1’ : ArithmeticSemiterm Nat 4).freeVariables) ⊆ {0} := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![(&0 : ArithmeticSemiterm Nat 4), ‘1’]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropTwoArity04,
    arithmeticOneArity04_freeVariables_eq_empty]
  simp

private theorem dropTwoBoundVariableArity04_freeVariables_subset
    (index : Fin 4) :
    ((#index : ArithmeticSemiterm Nat 4).freeVariables) ⊆ {0} := by
  simp

private theorem embeddedSubstitution_code_length_le_dropTwoTerminal
    {sourceArity targetArity : Nat}
    (source : ArithmeticSemiformula Nat sourceArity)
    (termCode : Nat)
    (terms : Fin sourceArity -> ArithmeticSemiterm Nat targetArity)
    (hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode) :
    (binaryFormulaCode (source ⇜ terms)).length <=
      uniformRewritingFormulaCodeEnvelope termCode
        (binaryFormulaCode source).length := by
  let rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity := Rew.subst terms
  have hrewriting : RewritingImageCodeBound rewriting termCode := by
    constructor
    · intro coordinate
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      exact hterms coordinate
    · intro coordinate
      dsimp only [rewriting]
      simp
  have hraw :=
    binaryFormulaCode_rewriting_length_le_uniform rewriting termCode
      hrewriting source
  simpa only [rewriting] using hraw

theorem
    taskDropTwoBranchTerminalExplicit_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (taskDropTwoBranchTerminalExplicit tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      taskDropTwoTerminalFormulaCodePolynomial bitBound := by
  let termCode := taskDropTwoTerminalTermCodePolynomial bitBound
  let entryCode := taskDropTwoTerminalEntryCodePolynomial termCode
  let rowCode := taskDropTwoTerminalRowCodePolynomial termCode
  have hclosedNumeral :
      forall value, Nat.size value <= bitBound ->
        (binaryTermCode
          (dropTwoClosedShift 4
            (shortBinaryNumeralTerm value))).length <= termCode := by
    intro value hvalueSize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
    have hshift := dropTwoClosedShift_code_length_le
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 4
    dsimp only [termCode]
    unfold taskDropTwoTerminalTermCodePolynomial
    omega
  have hsourceIndex :
      (binaryTermCode dropTwoSourceIndexTermArity04).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoTerminalTermCodePolynomial
    omega
  have hsourceNext :
      (binaryTermCode dropTwoSourceNextTermArity04).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoTerminalTermCodePolynomial
    omega
  have htargetIndex :
      (binaryTermCode (&0 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoTerminalTermCodePolynomial
    omega
  have htargetNext :
      (binaryTermCode (‘&0 + 1’ : ArithmeticSemiterm Nat 4)).length <=
        termCode := by
    dsimp only [termCode]
    unfold taskDropTwoTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoTerminalTermCodePolynomial
    omega
  have htokenTable := hclosedNumeral tokenTable htokenTableSize
  have hwidth := hclosedNumeral width hwidthSize
  have htokenCount := hclosedNumeral tokenCount htokenCountSize
  have hsourceBoundary := hclosedNumeral sourceBoundary hsourceBoundarySize
  have htargetBoundary := hclosedNumeral targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropTwoClosedShift 4 (shortBinaryNumeralTerm sourceBoundary),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount),
      dropTwoSourceIndexTermArity04, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropTwoClosedShift 4 (shortBinaryNumeralTerm sourceBoundary),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount),
      dropTwoSourceNextTermArity04, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropTwoClosedShift 4 (shortBinaryNumeralTerm targetBoundary),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount), &0, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropTwoClosedShift 4 (shortBinaryNumeralTerm targetBoundary),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 4 :=
    ![dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenTable),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm width),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount),
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
    · exact htargetIndex
    · exact hbvar1
  have htargetRightTerms : forall coordinate,
      (binaryTermCode (targetRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htargetBoundary
    · exact htokenCount
    · exact htargetNext
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
  let sourceLeftFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      sourceLeftTerms
  let sourceRightFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      sourceRightTerms
  let targetLeftFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      targetLeftTerms
  let targetRightFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      targetRightTerms
  let rowFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      rowTerms
  have hsourceLeft :
      (binaryFormulaCode sourceLeftFormula).length <= entryCode := by
    simpa only [sourceLeftFormula, entryCode,
      taskDropTwoTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropTwoTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode sourceLeftTerms hsourceLeftTerms
  have hsourceRight :
      (binaryFormulaCode sourceRightFormula).length <= entryCode := by
    simpa only [sourceRightFormula, entryCode,
      taskDropTwoTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropTwoTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode sourceRightTerms hsourceRightTerms
  have htargetLeft :
      (binaryFormulaCode targetLeftFormula).length <= entryCode := by
    simpa only [targetLeftFormula, entryCode,
      taskDropTwoTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropTwoTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode targetLeftTerms htargetLeftTerms
  have htargetRight :
      (binaryFormulaCode targetRightFormula).length <= entryCode := by
    simpa only [targetRightFormula, entryCode,
      taskDropTwoTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropTwoTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode targetRightTerms htargetRightTerms
  have hrow : (binaryFormulaCode rowFormula).length <= rowCode := by
    simpa only [rowFormula, rowCode,
      taskDropTwoTerminalRowCodePolynomial] using
      embeddedSubstitution_code_length_le_dropTwoTerminal
        (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val)
        termCode rowTerms hrowTerms
  have htail4 := andSemiformula_code_length_le targetRightFormula rowFormula
  have htail3 := andSemiformula_code_length_le targetLeftFormula
    (targetRightFormula ⋏ rowFormula)
  have htail2 := andSemiformula_code_length_le sourceRightFormula
    (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula))
  have htotal := andSemiformula_code_length_le sourceLeftFormula
    (sourceRightFormula ⋏
      (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula)))
  have hfinal :
      (binaryFormulaCode
        (sourceLeftFormula ⋏
          (sourceRightFormula ⋏
            (targetLeftFormula ⋏
              (targetRightFormula ⋏ rowFormula))))).length <=
        taskDropTwoTerminalFormulaCodePolynomial bitBound := by
    change
      (binaryFormulaCode
        (sourceLeftFormula ⋏
          (sourceRightFormula ⋏
            (targetLeftFormula ⋏
              (targetRightFormula ⋏ rowFormula))))).length <=
        4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1
    omega
  unfold taskDropTwoBranchTerminalExplicit
  change
    (binaryFormulaCode
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula))))).length <=
      taskDropTwoTerminalFormulaCodePolynomial bitBound
  exact hfinal

theorem
    compactAdditiveSyntaxTaskListDropTwoRowsBranchTerminal_eq_explicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal
        tokenTable width tokenCount sourceBoundary targetBoundary 2 =
      taskDropTwoBranchTerminalExplicit tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  rfl

theorem taskDropTwoBranchTerminalExplicit_freeVariables_subset_singleton
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (taskDropTwoBranchTerminalExplicit tokenTable width tokenCount
      sourceBoundary targetBoundary).freeVariables ⊆ {0} := by
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropTwoClosedShift 4 (shortBinaryNumeralTerm sourceBoundary),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount),
      dropTwoSourceIndexTermArity04, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropTwoClosedShift 4 (shortBinaryNumeralTerm sourceBoundary),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount),
      dropTwoSourceNextTermArity04, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropTwoClosedShift 4 (shortBinaryNumeralTerm targetBoundary),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount), &0, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropTwoClosedShift 4 (shortBinaryNumeralTerm targetBoundary),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 4 :=
    ![dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenTable),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm width),
      dropTwoClosedShift 4 (shortBinaryNumeralTerm tokenCount),
      #3, #2, #1, #0]
  let sourceLeftFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      sourceLeftTerms
  let sourceRightFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      sourceRightTerms
  let targetLeftFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      targetLeftTerms
  let targetRightFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      targetRightTerms
  let rowFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      rowTerms
  have hsourceLeft : sourceLeftFormula.freeVariables ⊆ {0} := by
    dsimp only [sourceLeftFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact dropTwoShiftedShortNumeral_freeVariables_subset sourceBoundary
    · exact dropTwoShiftedShortNumeral_freeVariables_subset tokenCount
    · exact dropTwoSourceIndexArity04_freeVariables_subset
    · exact dropTwoBoundVariableArity04_freeVariables_subset 3
  have hsourceRight : sourceRightFormula.freeVariables ⊆ {0} := by
    dsimp only [sourceRightFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact dropTwoShiftedShortNumeral_freeVariables_subset sourceBoundary
    · exact dropTwoShiftedShortNumeral_freeVariables_subset tokenCount
    · exact dropTwoSourceNextArity04_freeVariables_subset
    · exact dropTwoBoundVariableArity04_freeVariables_subset 2
  have htargetLeft : targetLeftFormula.freeVariables ⊆ {0} := by
    dsimp only [targetLeftFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact dropTwoShiftedShortNumeral_freeVariables_subset targetBoundary
    · exact dropTwoShiftedShortNumeral_freeVariables_subset tokenCount
    · exact dropTwoTargetIndexArity04_freeVariables_subset
    · exact dropTwoBoundVariableArity04_freeVariables_subset 1
  have htargetRight : targetRightFormula.freeVariables ⊆ {0} := by
    dsimp only [targetRightFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact dropTwoShiftedShortNumeral_freeVariables_subset targetBoundary
    · exact dropTwoShiftedShortNumeral_freeVariables_subset tokenCount
    · exact dropTwoTargetNextArity04_freeVariables_subset
    · exact dropTwoBoundVariableArity04_freeVariables_subset 0
  have hrow : rowFormula.freeVariables ⊆ {0} := by
    dsimp only [rowFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact dropTwoShiftedShortNumeral_freeVariables_subset tokenTable
    · exact dropTwoShiftedShortNumeral_freeVariables_subset width
    · exact dropTwoShiftedShortNumeral_freeVariables_subset tokenCount
    · exact dropTwoBoundVariableArity04_freeVariables_subset 3
    · exact dropTwoBoundVariableArity04_freeVariables_subset 2
    · exact dropTwoBoundVariableArity04_freeVariables_subset 1
    · exact dropTwoBoundVariableArity04_freeVariables_subset 0
  unfold taskDropTwoBranchTerminalExplicit
  change
    (sourceLeftFormula ⋏
      (sourceRightFormula ⋏
        (targetLeftFormula ⋏
          (targetRightFormula ⋏ rowFormula)))).freeVariables ⊆ {0}
  simp only [LO.FirstOrder.Semiformula.freeVariables_and]
  exact Finset.union_subset hsourceLeft
    (Finset.union_subset hsourceRight
      (Finset.union_subset htargetLeft
        (Finset.union_subset htargetRight hrow)))

#print axioms
  taskDropTwoBranchTerminalExplicit_code_length_le_fixed
#print axioms
  compactAdditiveSyntaxTaskListDropTwoRowsBranchTerminal_eq_explicit
#print axioms
  taskDropTwoBranchTerminalExplicit_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsTerminalSyntaxFixedBounds
