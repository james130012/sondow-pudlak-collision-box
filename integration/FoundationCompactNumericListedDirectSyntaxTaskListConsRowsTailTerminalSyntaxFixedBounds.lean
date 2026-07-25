import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsHeadInstalledFullyFixedBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Fixed syntax bound for a syntax-task cons-rows tail terminal

The terminal has four fixed-width entry formulas and one syntax-task row
formula.  This module bounds its original five-variable source formula before
the four bounded witnesses are installed.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailTerminalSyntaxFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate

def taskConsRowsTailTerminalTermCodePolynomial (bitBound : Nat) : Nat :=
  16 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (&0 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (‘&0 + 1’ : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (‘&0 + 2’ : ArithmeticSemiterm Nat 4)).length + 1

def taskConsRowsTailTerminalEntryCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def taskConsRowsTailTerminalRowCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val)).length

def taskConsRowsTailBranchTerminalFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := taskConsRowsTailTerminalTermCodePolynomial bitBound
  let entryCode := taskConsRowsTailTerminalEntryCodePolynomial termCode
  let rowCode := taskConsRowsTailTerminalRowCodePolynomial termCode
  4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1

private theorem taskClosedShift_symbolCount
    (term : FoundationCompactPAValuationTermCompiler.ValuationTerm) :
    forall arity,
      termSymbolCount (syntaxTaskListConsRowsClosedShift arity term) =
        termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [syntaxTaskListConsRowsClosedShift_succ,
        termSymbolCount_bShift, taskClosedShift_symbolCount term arity]

private theorem taskClosedShift_code_length_le
    (term : FoundationCompactPAValuationTermCompiler.ValuationTerm)
    (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    forall arity,
      (binaryTermCode
        (syntaxTaskListConsRowsClosedShift arity term)).length <=
          (2 * arity + 1) * bound
  | 0 => by
      simpa only [syntaxTaskListConsRowsClosedShift_zero, Nat.mul_zero,
        Nat.zero_add, Nat.one_mul]
        using hterm
  | arity + 1 => by
      have hinduction :=
        taskClosedShift_code_length_le term bound hterm arity
      have hsymbols : termSymbolCount term <= bound :=
        (termSymbolCount_le_binaryTermCode_length term).trans hterm
      have hshiftSymbols :
          termSymbolCount
              (syntaxTaskListConsRowsClosedShift arity term) <= bound := by
        rw [taskClosedShift_symbolCount]
        exact hsymbols
      have hshift :=
        binaryTermCode_bShift_length_le_add_symbols
          (syntaxTaskListConsRowsClosedShift arity term)
      have hcoefficient :
          (2 * (arity + 1) + 1) * bound =
            (2 * arity + 1) * bound + 2 * bound := by
        ring
      simp only [syntaxTaskListConsRowsClosedShift_succ]
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

def taskConsRowsTailBranchTerminalExplicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  let shift := syntaxTaskListConsRowsClosedShift 4
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
        shift (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #1]
  let targetRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![shift (shortBinaryNumeralTerm targetBoundary),
        shift (shortBinaryNumeralTerm tokenCount), ‘&0 + 2’, #0]
  let row :=
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      ![shift (shortBinaryNumeralTerm tokenTable),
        shift (shortBinaryNumeralTerm width),
        shift (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]
  sourceLeft ⋏ (sourceRight ⋏ (targetLeft ⋏ (targetRight ⋏ row)))

theorem taskConsRowsTailBranchTerminalExplicit_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (taskConsRowsTailBranchTerminalExplicit tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      taskConsRowsTailBranchTerminalFormulaCodePolynomial bitBound := by
  let termCode := taskConsRowsTailTerminalTermCodePolynomial bitBound
  let entryCode := taskConsRowsTailTerminalEntryCodePolynomial termCode
  let rowCode := taskConsRowsTailTerminalRowCodePolynomial termCode
  have hclosedNumeral :
      forall value, Nat.size value <= bitBound ->
        (binaryTermCode
          (syntaxTaskListConsRowsClosedShift 4
            (shortBinaryNumeralTerm value))).length <= termCode := by
    intro value hvalueSize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
    have hshift := taskClosedShift_code_length_le
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 4
    dsimp only [termCode]
    unfold taskConsRowsTailTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskConsRowsTailTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskConsRowsTailTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskConsRowsTailTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskConsRowsTailTerminalTermCodePolynomial
    omega
  have hfreeIndex :
      (binaryTermCode (&0 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold taskConsRowsTailTerminalTermCodePolynomial
    omega
  have hfreeIndexSucc :
      (binaryTermCode (‘&0 + 1’ : ArithmeticSemiterm Nat 4)).length <=
        termCode := by
    dsimp only [termCode]
    unfold taskConsRowsTailTerminalTermCodePolynomial
    omega
  have hfreeIndexSucc2 :
      (binaryTermCode (‘&0 + 2’ : ArithmeticSemiterm Nat 4)).length <=
        termCode := by
    dsimp only [termCode]
    unfold taskConsRowsTailTerminalTermCodePolynomial
    omega
  have htokenTable := hclosedNumeral tokenTable htokenTableSize
  have hwidth := hclosedNumeral width hwidthSize
  have htokenCount := hclosedNumeral tokenCount htokenCountSize
  have hsourceBoundary := hclosedNumeral sourceBoundary hsourceBoundarySize
  have htargetBoundary := hclosedNumeral targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![syntaxTaskListConsRowsClosedShift 4
        (shortBinaryNumeralTerm sourceBoundary),
      syntaxTaskListConsRowsClosedShift 4
        (shortBinaryNumeralTerm tokenCount), &0, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![syntaxTaskListConsRowsClosedShift 4
        (shortBinaryNumeralTerm sourceBoundary),
      syntaxTaskListConsRowsClosedShift 4
        (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![syntaxTaskListConsRowsClosedShift 4
        (shortBinaryNumeralTerm targetBoundary),
      syntaxTaskListConsRowsClosedShift 4
        (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![syntaxTaskListConsRowsClosedShift 4
        (shortBinaryNumeralTerm targetBoundary),
      syntaxTaskListConsRowsClosedShift 4
        (shortBinaryNumeralTerm tokenCount), ‘&0 + 2’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 4 :=
    ![syntaxTaskListConsRowsClosedShift 4
        (shortBinaryNumeralTerm tokenTable),
      syntaxTaskListConsRowsClosedShift 4
        (shortBinaryNumeralTerm width),
      syntaxTaskListConsRowsClosedShift 4
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
    · exact hfreeIndexSucc
    · exact hbvar1
  have htargetRightTerms : forall coordinate,
      (binaryTermCode (targetRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htargetBoundary
    · exact htokenCount
    · exact hfreeIndexSucc2
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
      taskConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_taskTerminal
        compactFixedWidthEntryDef.val termCode sourceLeftTerms hsourceLeftTerms
  have hsourceRight :
      (binaryFormulaCode sourceRightFormula).length <= entryCode := by
    simpa only [sourceRightFormula, entryCode,
      taskConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_taskTerminal
        compactFixedWidthEntryDef.val termCode sourceRightTerms
        hsourceRightTerms
  have htargetLeft :
      (binaryFormulaCode targetLeftFormula).length <= entryCode := by
    simpa only [targetLeftFormula, entryCode,
      taskConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_taskTerminal
        compactFixedWidthEntryDef.val termCode targetLeftTerms htargetLeftTerms
  have htargetRight :
      (binaryFormulaCode targetRightFormula).length <= entryCode := by
    simpa only [targetRightFormula, entryCode,
      taskConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_taskTerminal
        compactFixedWidthEntryDef.val termCode targetRightTerms
        htargetRightTerms
  have hrow : (binaryFormulaCode rowFormula).length <= rowCode := by
    simpa only [rowFormula, rowCode,
      taskConsRowsTailTerminalRowCodePolynomial] using
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
        taskConsRowsTailBranchTerminalFormulaCodePolynomial bitBound := by
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
      taskConsRowsTailBranchTerminalFormulaCodePolynomial bitBound
  exact hfinal

theorem compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal_eq_explicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary =
      taskConsRowsTailBranchTerminalExplicit tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  rfl

theorem compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary)).length <=
      taskConsRowsTailBranchTerminalFormulaCodePolynomial bitBound := by
  rw [compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal_eq_explicit]
  exact taskConsRowsTailBranchTerminalExplicit_code_length_le_fixed
    tokenTable width tokenCount sourceBoundary targetBoundary bitBound
    htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
    htargetBoundarySize

#print axioms taskConsRowsTailBranchTerminalExplicit_code_length_le_fixed
#print axioms
  compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal_eq_explicit
#print axioms
  compactAdditiveSyntaxTaskListConsRowsTailBranchTerminal_code_length_le_fixed

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailTerminalSyntaxFixedBounds
