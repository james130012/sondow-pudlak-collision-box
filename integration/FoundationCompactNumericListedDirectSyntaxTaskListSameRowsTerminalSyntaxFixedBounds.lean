import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsAtomicFixedBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Fixed syntax bound for a syntax-task same-rows terminal

The terminal has four fixed-width entry formulas and one syntax-task row
formula.  This module bounds its original five-variable source formula before
the four bounded witnesses are installed.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate

def taskSameRowsTerminalTermCodePolynomial (bitBound : Nat) : Nat :=
  16 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (&0 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (‘&0 + 1’ : ArithmeticSemiterm Nat 4)).length + 1

def taskSameRowsTerminalEntryCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def taskSameRowsTerminalRowCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val)).length

def taskSameRowsBranchTerminalFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := taskSameRowsTerminalTermCodePolynomial bitBound
  let entryCode := taskSameRowsTerminalEntryCodePolynomial termCode
  let rowCode := taskSameRowsTerminalRowCodePolynomial termCode
  4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1

private theorem taskClosedShift_symbolCount
    (term : FoundationCompactPAValuationTermCompiler.ValuationTerm) :
    forall arity,
      termSymbolCount (syntaxTaskListSameRowsClosedShift arity term) =
        termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [syntaxTaskListSameRowsClosedShift_succ,
        termSymbolCount_bShift, taskClosedShift_symbolCount term arity]

private theorem taskClosedShift_code_length_le
    (term : FoundationCompactPAValuationTermCompiler.ValuationTerm)
    (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    forall arity,
      (binaryTermCode
        (syntaxTaskListSameRowsClosedShift arity term)).length <=
          (2 * arity + 1) * bound
  | 0 => by
      simpa only [syntaxTaskListSameRowsClosedShift_zero, Nat.mul_zero,
        Nat.zero_add, Nat.one_mul]
        using hterm
  | arity + 1 => by
      have hinduction :=
        taskClosedShift_code_length_le term bound hterm arity
      have hsymbols : termSymbolCount term <= bound :=
        (termSymbolCount_le_binaryTermCode_length term).trans hterm
      have hshiftSymbols :
          termSymbolCount
              (syntaxTaskListSameRowsClosedShift arity term) <= bound := by
        rw [taskClosedShift_symbolCount]
        exact hsymbols
      have hshift :=
        binaryTermCode_bShift_length_le_add_symbols
          (syntaxTaskListSameRowsClosedShift arity term)
      have hcoefficient :
          (2 * (arity + 1) + 1) * bound =
            (2 * arity + 1) * bound + 2 * bound := by
        ring
      simp only [syntaxTaskListSameRowsClosedShift_succ]
      rw [hcoefficient]
      omega

private theorem embeddedSubstitution_code_length_le_taskTerminal
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

def taskSameRowsBranchTerminalExplicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  let shift := syntaxTaskListSameRowsClosedShift 4
  let sourceLeft :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![shift (shortBinaryNumeralTerm sourceBoundary),
        shift (shortBinaryNumeralTerm tokenCount), &0, #3]
  let sourceRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![shift (shortBinaryNumeralTerm sourceBoundary),
        shift (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #2]
  let targetLeft :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![shift (shortBinaryNumeralTerm targetBoundary),
        shift (shortBinaryNumeralTerm tokenCount), &0, #1]
  let targetRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![shift (shortBinaryNumeralTerm targetBoundary),
        shift (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #0]
  let row :=
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      ![shift (shortBinaryNumeralTerm tokenTable),
        shift (shortBinaryNumeralTerm width),
        shift (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]
  sourceLeft ⋏ (sourceRight ⋏ (targetLeft ⋏ (targetRight ⋏ row)))

theorem taskSameRowsBranchTerminalExplicit_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (taskSameRowsBranchTerminalExplicit tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      taskSameRowsBranchTerminalFormulaCodePolynomial bitBound := by
  let termCode := taskSameRowsTerminalTermCodePolynomial bitBound
  let entryCode := taskSameRowsTerminalEntryCodePolynomial termCode
  let rowCode := taskSameRowsTerminalRowCodePolynomial termCode
  have hclosedNumeral :
      forall value, Nat.size value <= bitBound ->
        (binaryTermCode
          (syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm value))).length <= termCode := by
    intro value hvalueSize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
    have hshift := taskClosedShift_code_length_le
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 4
    dsimp only [termCode]
    unfold taskSameRowsTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskSameRowsTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskSameRowsTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskSameRowsTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskSameRowsTerminalTermCodePolynomial
    omega
  have hfreeIndex :
      (binaryTermCode (&0 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskSameRowsTerminalTermCodePolynomial
    omega
  have hfreeIndexSucc :
      (binaryTermCode (‘&0 + 1’ : ArithmeticSemiterm Nat 4)).length <=
        termCode := by
    dsimp only [termCode]
    unfold taskSameRowsTerminalTermCodePolynomial
    omega
  have htokenTable := hclosedNumeral tokenTable htokenTableSize
  have hwidth := hclosedNumeral width hwidthSize
  have htokenCount := hclosedNumeral tokenCount htokenCountSize
  have hsourceBoundary := hclosedNumeral sourceBoundary hsourceBoundarySize
  have htargetBoundary := hclosedNumeral targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm sourceBoundary),
      syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm tokenCount), &0, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm sourceBoundary),
      syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm targetBoundary),
      syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm tokenCount), &0, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm targetBoundary),
      syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 4 :=
    ![syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm tokenTable),
      syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm width),
      syntaxTaskListSameRowsClosedShift 4
        (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]
  have hsourceLeftTerms : forall coordinate,
      (binaryTermCode (sourceLeftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact hsourceBoundary
    · exact htokenCount
    · exact hfreeIndex
    · exact hbvar3
  have hsourceRightTerms : forall coordinate,
      (binaryTermCode (sourceRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact hsourceBoundary
    · exact htokenCount
    · exact hfreeIndexSucc
    · exact hbvar2
  have htargetLeftTerms : forall coordinate,
      (binaryTermCode (targetLeftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htargetBoundary
    · exact htokenCount
    · exact hfreeIndex
    · exact hbvar1
  have htargetRightTerms : forall coordinate,
      (binaryTermCode (targetRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htargetBoundary
    · exact htokenCount
    · exact hfreeIndexSucc
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
      taskSameRowsTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_taskTerminal
        compactFixedWidthEntryDef.val termCode sourceLeftTerms hsourceLeftTerms
  have hsourceRight :
      (binaryFormulaCode sourceRightFormula).length <= entryCode := by
    simpa only [sourceRightFormula, entryCode,
      taskSameRowsTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_taskTerminal
        compactFixedWidthEntryDef.val termCode sourceRightTerms
        hsourceRightTerms
  have htargetLeft :
      (binaryFormulaCode targetLeftFormula).length <= entryCode := by
    simpa only [targetLeftFormula, entryCode,
      taskSameRowsTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_taskTerminal
        compactFixedWidthEntryDef.val termCode targetLeftTerms htargetLeftTerms
  have htargetRight :
      (binaryFormulaCode targetRightFormula).length <= entryCode := by
    simpa only [targetRightFormula, entryCode,
      taskSameRowsTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_taskTerminal
        compactFixedWidthEntryDef.val termCode targetRightTerms
        htargetRightTerms
  have hrow : (binaryFormulaCode rowFormula).length <= rowCode := by
    simpa only [rowFormula, rowCode,
      taskSameRowsTerminalRowCodePolynomial] using
      embeddedSubstitution_code_length_le_taskTerminal
        compactAdditiveSyntaxTaskRowEqDef.val termCode rowTerms hrowTerms
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
        taskSameRowsBranchTerminalFormulaCodePolynomial bitBound := by
    change
      (binaryFormulaCode
        (sourceLeftFormula ⋏
          (sourceRightFormula ⋏
            (targetLeftFormula ⋏
              (targetRightFormula ⋏ rowFormula))))).length <=
        4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1
    omega
  change
    (binaryFormulaCode
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula))))).length <=
      taskSameRowsBranchTerminalFormulaCodePolynomial bitBound
  exact hfinal

theorem compactAdditiveSyntaxTaskListSameRowsBranchTerminal_eq_explicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary =
      taskSameRowsBranchTerminalExplicit tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  rfl

theorem compactAdditiveSyntaxTaskListSameRowsBranchTerminal_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary)).length <=
      taskSameRowsBranchTerminalFormulaCodePolynomial bitBound := by
  rw [compactAdditiveSyntaxTaskListSameRowsBranchTerminal_eq_explicit]
  exact taskSameRowsBranchTerminalExplicit_code_length_le_fixed
    tokenTable width tokenCount sourceBoundary targetBoundary bitBound
    htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
    htargetBoundarySize

#print axioms taskSameRowsBranchTerminalExplicit_code_length_le_fixed
#print axioms
  compactAdditiveSyntaxTaskListSameRowsBranchTerminal_eq_explicit
#print axioms
  compactAdditiveSyntaxTaskListSameRowsBranchTerminal_code_length_le_fixed

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalSyntaxFixedBounds
