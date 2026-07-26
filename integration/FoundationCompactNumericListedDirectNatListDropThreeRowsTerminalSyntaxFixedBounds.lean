import integration.FoundationCompactNumericListedDirectNatListDropThreeRowsTerminalFullyFixedBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed syntax bound for the drop-one row branch terminal

After fixing the consumed count to the native numeral `3`, both shifted source
index terms have constant syntax.  The remaining varying terms are canonical
short numerals controlled by the common bit bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropThreeRowsTerminalSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

def dropThreeClosedShift :
    (arity : Nat) -> FoundationCompactPAValuationTermCompiler.ValuationTerm ->
      ArithmeticSemiterm Nat arity
  | 0, term => term
  | arity + 1, term => Rew.bShift (dropThreeClosedShift arity term)

private def dropThreeSourceIndexTermArity04 :
    ArithmeticSemiterm Nat 4 :=
  ‘!!(dropThreeClosedShift 4 (fixedNumeralTerm 3)) + &0’

private def dropThreeSourceNextTermArity04 :
    ArithmeticSemiterm Nat 4 :=
  ‘(!!(dropThreeClosedShift 4 (fixedNumeralTerm 3)) + &0) + 1’

def dropThreeRowsBranchTerminalTermCodePolynomial (bitBound : Nat) : Nat :=
  16 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode dropThreeSourceIndexTermArity04).length +
    (binaryTermCode dropThreeSourceNextTermArity04).length +
    (binaryTermCode (&0 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (‘&0 + 1’ : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length + 1

def dropThreeRowsBranchTerminalEntryCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def dropThreeRowsBranchTerminalRowCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val)).length

def dropThreeRowsBranchTerminalFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := dropThreeRowsBranchTerminalTermCodePolynomial bitBound
  let entryCode := dropThreeRowsBranchTerminalEntryCodePolynomial termCode
  let rowCode := dropThreeRowsBranchTerminalRowCodePolynomial termCode
  4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1

private theorem dropThreeClosedShift_symbolCount
    (term : FoundationCompactPAValuationTermCompiler.ValuationTerm) :
    forall arity,
      termSymbolCount (dropThreeClosedShift arity term) = termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [dropThreeClosedShift, termSymbolCount_bShift,
        dropThreeClosedShift_symbolCount term arity]

theorem dropThreeClosedShift_code_length_le
    (term : FoundationCompactPAValuationTermCompiler.ValuationTerm)
    (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    forall arity,
      (binaryTermCode (dropThreeClosedShift arity term)).length <=
        (2 * arity + 1) * bound
  | 0 => by
      simpa only [dropThreeClosedShift, Nat.mul_zero, Nat.zero_add, Nat.one_mul]
        using hterm
  | arity + 1 => by
      have hinduction :=
        dropThreeClosedShift_code_length_le term bound hterm arity
      have hsymbols : termSymbolCount term <= bound :=
        (termSymbolCount_le_binaryTermCode_length term).trans hterm
      have hshiftSymbols :
          termSymbolCount (dropThreeClosedShift arity term) <= bound := by
        rw [dropThreeClosedShift_symbolCount]
        exact hsymbols
      have hshift :=
        binaryTermCode_bShift_length_le_add_symbols
          (dropThreeClosedShift arity term)
      have hcoefficient :
          (2 * (arity + 1) + 1) * bound =
            (2 * arity + 1) * bound + 2 * bound := by
        ring
      simp only [dropThreeClosedShift]
      rw [hcoefficient]
      omega

private theorem dropThreeClosedShift_freeVariables_eq_empty
    (term : FoundationCompactPAValuationTermCompiler.ValuationTerm)
    (hterm : term.freeVariables = ∅) :
    forall arity, (dropThreeClosedShift arity term).freeVariables = ∅
  | 0 => hterm
  | arity + 1 => by
      simp only [dropThreeClosedShift]
      exact bShift_freeVariables_eq_empty_of_empty _
        (dropThreeClosedShift_freeVariables_eq_empty term hterm arity)

@[simp] private theorem
    dropThreeClosedShift_shortBinaryNumeral_freeVariables_eq_empty
    (arity value : Nat) :
    (dropThreeClosedShift arity
      (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
  exact dropThreeClosedShift_freeVariables_eq_empty _
    (shortBinaryNumeralTerm_freeVariables_eq_empty value) arity

@[simp] private theorem
    dropThreeClosedShift_fixedNumeralOne_freeVariables_eq_empty
    (arity : Nat) :
    (dropThreeClosedShift arity (fixedNumeralTerm 3)).freeVariables = ∅ := by
  apply dropThreeClosedShift_freeVariables_eq_empty
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

private theorem dropThreeShiftedShortNumeral_freeVariables_subset
    (value : Nat) :
    (dropThreeClosedShift 4
      (shortBinaryNumeralTerm value)).freeVariables ⊆ {0} := by
  rw [dropThreeClosedShift_shortBinaryNumeral_freeVariables_eq_empty]
  simp

private theorem binaryFunctionTerm_freeVariables_dropThreeArity04
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

private theorem dropThreeSourceIndexArity04_freeVariables_subset :
    dropThreeSourceIndexTermArity04.freeVariables ⊆ {0} := by
  unfold dropThreeSourceIndexTermArity04
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![dropThreeClosedShift 4 (fixedNumeralTerm 3),
        (&0 : ArithmeticSemiterm Nat 4)]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropThreeArity04,
    dropThreeClosedShift_fixedNumeralOne_freeVariables_eq_empty]
  simp

private theorem dropThreeSourceNextArity04_freeVariables_subset :
    dropThreeSourceNextTermArity04.freeVariables ⊆ {0} := by
  unfold dropThreeSourceNextTermArity04
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![LO.FirstOrder.Semiterm.func Language.Add.add
        ![dropThreeClosedShift 4 (fixedNumeralTerm 3),
          (&0 : ArithmeticSemiterm Nat 4)], ‘1’]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropThreeArity04,
    binaryFunctionTerm_freeVariables_dropThreeArity04,
    dropThreeClosedShift_fixedNumeralOne_freeVariables_eq_empty,
    arithmeticOneArity04_freeVariables_eq_empty]
  simp

private theorem dropThreeTargetIndexArity04_freeVariables_subset :
    ((&0 : ArithmeticSemiterm Nat 4).freeVariables) ⊆ {0} := by
  simp

private theorem dropThreeTargetNextArity04_freeVariables_subset :
    ((‘&0 + 1’ : ArithmeticSemiterm Nat 4).freeVariables) ⊆ {0} := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![(&0 : ArithmeticSemiterm Nat 4), ‘1’]).freeVariables ⊆ {0}
  rw [binaryFunctionTerm_freeVariables_dropThreeArity04,
    arithmeticOneArity04_freeVariables_eq_empty]
  simp

private theorem dropThreeBoundVariableArity04_freeVariables_subset
    (index : Fin 4) :
    ((#index : ArithmeticSemiterm Nat 4).freeVariables) ⊆ {0} := by
  simp

private theorem embeddedSubstitution_code_length_le_dropThreeTerminal
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

theorem dropThreeRowsFiveLeafFormula_code_length_le
    {boundArity : Nat}
    (sourceLeftTerms sourceRightTerms targetLeftTerms targetRightTerms :
      Fin 4 -> ArithmeticSemiterm Nat boundArity)
    (rowTerms : Fin 7 -> ArithmeticSemiterm Nat boundArity)
    (termCode : Nat)
    (hsourceLeftTerms : forall coordinate,
      (binaryTermCode (sourceLeftTerms coordinate)).length <= termCode)
    (hsourceRightTerms : forall coordinate,
      (binaryTermCode (sourceRightTerms coordinate)).length <= termCode)
    (htargetLeftTerms : forall coordinate,
      (binaryTermCode (targetLeftTerms coordinate)).length <= termCode)
    (htargetRightTerms : forall coordinate,
      (binaryTermCode (targetRightTerms coordinate)).length <= termCode)
    (hrowTerms : forall coordinate,
      (binaryTermCode (rowTerms coordinate)).length <= termCode) :
    let sourceLeftFormula : ArithmeticSemiformula Nat boundArity :=
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        sourceLeftTerms
    let sourceRightFormula : ArithmeticSemiformula Nat boundArity :=
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        sourceRightTerms
    let targetLeftFormula : ArithmeticSemiformula Nat boundArity :=
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        targetLeftTerms
    let targetRightFormula : ArithmeticSemiformula Nat boundArity :=
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        targetRightTerms
    let rowFormula : ArithmeticSemiformula Nat boundArity :=
      (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜
        rowTerms
    (binaryFormulaCode
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula))))).length <=
      4 * dropThreeRowsBranchTerminalEntryCodePolynomial termCode +
        dropThreeRowsBranchTerminalRowCodePolynomial termCode +
          4 * (binaryNatCode 4).length + 1 := by
  let sourceLeftFormula : ArithmeticSemiformula Nat boundArity :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      sourceLeftTerms
  let sourceRightFormula : ArithmeticSemiformula Nat boundArity :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      sourceRightTerms
  let targetLeftFormula : ArithmeticSemiformula Nat boundArity :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      targetLeftTerms
  let targetRightFormula : ArithmeticSemiformula Nat boundArity :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      targetRightTerms
  let rowFormula : ArithmeticSemiformula Nat boundArity :=
    (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜ rowTerms
  have hsourceLeft :
      (binaryFormulaCode sourceLeftFormula).length <=
        dropThreeRowsBranchTerminalEntryCodePolynomial termCode := by
    simpa only [sourceLeftFormula,
      dropThreeRowsBranchTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropThreeTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode sourceLeftTerms hsourceLeftTerms
  have hsourceRight :
      (binaryFormulaCode sourceRightFormula).length <=
        dropThreeRowsBranchTerminalEntryCodePolynomial termCode := by
    simpa only [sourceRightFormula,
      dropThreeRowsBranchTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropThreeTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode sourceRightTerms hsourceRightTerms
  have htargetLeft :
      (binaryFormulaCode targetLeftFormula).length <=
        dropThreeRowsBranchTerminalEntryCodePolynomial termCode := by
    simpa only [targetLeftFormula,
      dropThreeRowsBranchTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropThreeTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode targetLeftTerms htargetLeftTerms
  have htargetRight :
      (binaryFormulaCode targetRightFormula).length <=
        dropThreeRowsBranchTerminalEntryCodePolynomial termCode := by
    simpa only [targetRightFormula,
      dropThreeRowsBranchTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropThreeTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode targetRightTerms htargetRightTerms
  have hrow :
      (binaryFormulaCode rowFormula).length <=
        dropThreeRowsBranchTerminalRowCodePolynomial termCode := by
    simpa only [rowFormula,
      dropThreeRowsBranchTerminalRowCodePolynomial] using
      embeddedSubstitution_code_length_le_dropThreeTerminal
        (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val)
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
        4 * dropThreeRowsBranchTerminalEntryCodePolynomial termCode +
          dropThreeRowsBranchTerminalRowCodePolynomial termCode +
            4 * (binaryNatCode 4).length + 1 := by
    omega
  simpa only [sourceLeftFormula, sourceRightFormula, targetLeftFormula,
    targetRightFormula, rowFormula] using hfinal

theorem compactAdditiveNatListDropThreeRowsBranchTerminal_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListDropFixedNumeralRowsBranchTerminal tokenTable
        width tokenCount sourceBoundary targetBoundary 3)).length <=
      dropThreeRowsBranchTerminalFormulaCodePolynomial bitBound := by
  let termCode := dropThreeRowsBranchTerminalTermCodePolynomial bitBound
  let entryCode := dropThreeRowsBranchTerminalEntryCodePolynomial termCode
  let rowCode := dropThreeRowsBranchTerminalRowCodePolynomial termCode
  have hclosedNumeral :
      forall value, Nat.size value <= bitBound ->
        (binaryTermCode
          (dropThreeClosedShift 4 (shortBinaryNumeralTerm value))).length <=
            termCode := by
    intro value hvalueSize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
    have hshift := dropThreeClosedShift_code_length_le
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 4
    dsimp only [termCode]
    unfold dropThreeRowsBranchTerminalTermCodePolynomial
    omega
  have hsourceIndex :
      (binaryTermCode dropThreeSourceIndexTermArity04).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsBranchTerminalTermCodePolynomial
    omega
  have hsourceNext :
      (binaryTermCode dropThreeSourceNextTermArity04).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsBranchTerminalTermCodePolynomial
    omega
  have htargetIndex :
      (binaryTermCode (&0 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsBranchTerminalTermCodePolynomial
    omega
  have htargetNext :
      (binaryTermCode (‘&0 + 1’ : ArithmeticSemiterm Nat 4)).length <=
        termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsBranchTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsBranchTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsBranchTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsBranchTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold dropThreeRowsBranchTerminalTermCodePolynomial
    omega
  have htokenTable := hclosedNumeral tokenTable htokenTableSize
  have hwidth := hclosedNumeral width hwidthSize
  have htokenCount := hclosedNumeral tokenCount htokenCountSize
  have hsourceBoundary := hclosedNumeral sourceBoundary hsourceBoundarySize
  have htargetBoundary := hclosedNumeral targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropThreeClosedShift 4 (shortBinaryNumeralTerm sourceBoundary),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount),
      dropThreeSourceIndexTermArity04, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropThreeClosedShift 4 (shortBinaryNumeralTerm sourceBoundary),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount),
      dropThreeSourceNextTermArity04, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropThreeClosedShift 4 (shortBinaryNumeralTerm targetBoundary),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount), &0, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropThreeClosedShift 4 (shortBinaryNumeralTerm targetBoundary),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 4 :=
    ![dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenTable),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm width),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]
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
    (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜
      rowTerms
  have hsourceLeft :
      (binaryFormulaCode sourceLeftFormula).length <= entryCode := by
    simpa only [sourceLeftFormula, entryCode,
      dropThreeRowsBranchTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropThreeTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode sourceLeftTerms hsourceLeftTerms
  have hsourceRight :
      (binaryFormulaCode sourceRightFormula).length <= entryCode := by
    simpa only [sourceRightFormula, entryCode,
      dropThreeRowsBranchTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropThreeTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode sourceRightTerms hsourceRightTerms
  have htargetLeft :
      (binaryFormulaCode targetLeftFormula).length <= entryCode := by
    simpa only [targetLeftFormula, entryCode,
      dropThreeRowsBranchTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropThreeTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode targetLeftTerms htargetLeftTerms
  have htargetRight :
      (binaryFormulaCode targetRightFormula).length <= entryCode := by
    simpa only [targetRightFormula, entryCode,
      dropThreeRowsBranchTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_dropThreeTerminal
        (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
        termCode targetRightTerms htargetRightTerms
  have hrow : (binaryFormulaCode rowFormula).length <= rowCode := by
    simpa only [rowFormula, rowCode,
      dropThreeRowsBranchTerminalRowCodePolynomial] using
      embeddedSubstitution_code_length_le_dropThreeTerminal
        (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val)
        termCode rowTerms hrowTerms
  have htail4 := andSemiformula_code_length_le
    targetRightFormula rowFormula
  have htail3 := andSemiformula_code_length_le
    targetLeftFormula (targetRightFormula ⋏ rowFormula)
  have htail2 := andSemiformula_code_length_le
    sourceRightFormula
    (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula))
  have htotal := andSemiformula_code_length_le
    sourceLeftFormula
    (sourceRightFormula ⋏
      (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula)))
  have hfinal :
      (binaryFormulaCode
        (sourceLeftFormula ⋏
          (sourceRightFormula ⋏
            (targetLeftFormula ⋏
              (targetRightFormula ⋏ rowFormula))))).length <=
        dropThreeRowsBranchTerminalFormulaCodePolynomial bitBound := by
    change
      (binaryFormulaCode
        (sourceLeftFormula ⋏
          (sourceRightFormula ⋏
            (targetLeftFormula ⋏
              (targetRightFormula ⋏ rowFormula))))).length <=
        4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1
    omega
  unfold compactAdditiveNatListDropFixedNumeralRowsBranchTerminal
  change
    (binaryFormulaCode
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula))))).length <=
      dropThreeRowsBranchTerminalFormulaCodePolynomial bitBound
  exact hfinal

theorem
    compactAdditiveNatListDropThreeRowsBranchTerminal_freeVariables_subset_singleton
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListDropFixedNumeralRowsBranchTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary 3).freeVariables ⊆ {0} := by
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropThreeClosedShift 4 (shortBinaryNumeralTerm sourceBoundary),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount),
      dropThreeSourceIndexTermArity04, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropThreeClosedShift 4 (shortBinaryNumeralTerm sourceBoundary),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount),
      dropThreeSourceNextTermArity04, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropThreeClosedShift 4 (shortBinaryNumeralTerm targetBoundary),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount), &0, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![dropThreeClosedShift 4 (shortBinaryNumeralTerm targetBoundary),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 4 :=
    ![dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenTable),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm width),
      dropThreeClosedShift 4 (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]
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
    (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜ rowTerms
  have hsourceLeft : sourceLeftFormula.freeVariables ⊆ {0} := by
    dsimp only [sourceLeftFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact dropThreeShiftedShortNumeral_freeVariables_subset sourceBoundary
    · exact dropThreeShiftedShortNumeral_freeVariables_subset tokenCount
    · exact dropThreeSourceIndexArity04_freeVariables_subset
    · exact dropThreeBoundVariableArity04_freeVariables_subset 3
  have hsourceRight : sourceRightFormula.freeVariables ⊆ {0} := by
    dsimp only [sourceRightFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact dropThreeShiftedShortNumeral_freeVariables_subset sourceBoundary
    · exact dropThreeShiftedShortNumeral_freeVariables_subset tokenCount
    · exact dropThreeSourceNextArity04_freeVariables_subset
    · exact dropThreeBoundVariableArity04_freeVariables_subset 2
  have htargetLeft : targetLeftFormula.freeVariables ⊆ {0} := by
    dsimp only [targetLeftFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact dropThreeShiftedShortNumeral_freeVariables_subset targetBoundary
    · exact dropThreeShiftedShortNumeral_freeVariables_subset tokenCount
    · exact dropThreeTargetIndexArity04_freeVariables_subset
    · exact dropThreeBoundVariableArity04_freeVariables_subset 1
  have htargetRight : targetRightFormula.freeVariables ⊆ {0} := by
    dsimp only [targetRightFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact dropThreeShiftedShortNumeral_freeVariables_subset targetBoundary
    · exact dropThreeShiftedShortNumeral_freeVariables_subset tokenCount
    · exact dropThreeTargetNextArity04_freeVariables_subset
    · exact dropThreeBoundVariableArity04_freeVariables_subset 0
  have hrow : rowFormula.freeVariables ⊆ {0} := by
    dsimp only [rowFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact dropThreeShiftedShortNumeral_freeVariables_subset tokenTable
    · exact dropThreeShiftedShortNumeral_freeVariables_subset width
    · exact dropThreeShiftedShortNumeral_freeVariables_subset tokenCount
    · exact dropThreeBoundVariableArity04_freeVariables_subset 3
    · exact dropThreeBoundVariableArity04_freeVariables_subset 2
    · exact dropThreeBoundVariableArity04_freeVariables_subset 1
    · exact dropThreeBoundVariableArity04_freeVariables_subset 0
  unfold compactAdditiveNatListDropFixedNumeralRowsBranchTerminal
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
  dropThreeRowsFiveLeafFormula_code_length_le
#print axioms
  compactAdditiveNatListDropThreeRowsBranchTerminal_code_length_le_fixed
#print axioms
  compactAdditiveNatListDropThreeRowsBranchTerminal_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectNatListDropThreeRowsTerminalSyntaxFixedBounds
