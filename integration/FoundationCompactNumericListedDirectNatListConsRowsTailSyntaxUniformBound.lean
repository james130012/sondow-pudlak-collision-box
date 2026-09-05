import integration.FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-! # Fixed syntax bound for a natural-list cons tail terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 420000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailSyntaxUniformBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailCertificate

def natListConsRowsTailTerminalTermCodePolynomial (bitBound : Nat) : Nat :=
  16 * (binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode consRowsTailIndexTerm).length +
    (binaryTermCode consRowsTailSuccessorTerm).length +
    (binaryTermCode consRowsTailSecondSuccessorTerm).length) +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length +
    1

def natListConsRowsTailTerminalEntryCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def natListConsRowsTailTerminalRowCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val)).length

def natListConsRowsTailBranchFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := natListConsRowsTailTerminalTermCodePolynomial bitBound
  let entryCode := natListConsRowsTailTerminalEntryCodePolynomial termCode
  let rowCode := natListConsRowsTailTerminalRowCodePolynomial termCode
  4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1

private theorem consClosedShift_symbolCount (term : ValuationTerm) :
    forall arity, termSymbolCount (closedShift arity term) = termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [closedShift, termSymbolCount_bShift,
        consClosedShift_symbolCount term arity]

private theorem consClosedShift_code_length_le
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    forall arity,
      (binaryTermCode (closedShift arity term)).length <=
        (2 * arity + 1) * bound
  | 0 => by
      simpa only [closedShift, Nat.mul_zero, Nat.zero_add, Nat.one_mul] using
        hterm
  | arity + 1 => by
      have hinduction := consClosedShift_code_length_le term bound hterm arity
      have hsymbols : termSymbolCount term <= bound :=
        (termSymbolCount_le_binaryTermCode_length term).trans hterm
      have hshiftSymbols :
          termSymbolCount (closedShift arity term) <= bound := by
        rw [consClosedShift_symbolCount]
        exact hsymbols
      have hshift := binaryTermCode_bShift_length_le_add_symbols
        (closedShift arity term)
      have hcoefficient :
          (2 * (arity + 1) + 1) * bound =
            (2 * arity + 1) * bound + 2 * bound := by
        ring
      simp only [closedShift]
      rw [hcoefficient]
      omega

private theorem embeddedSubstitution_code_length_le_consTail
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
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    termCode hrewriting source
  simpa only [rewriting] using hraw

def compactAdditiveNatListConsRowsTailBranchTerminalExplicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  let shift := closedShift 4
  let sourceLeft :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![shift (shortBinaryNumeralTerm sourceBoundary),
        shift (shortBinaryNumeralTerm tokenCount),
        shift consRowsTailIndexTerm, #3]
  let sourceRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![shift (shortBinaryNumeralTerm sourceBoundary),
        shift (shortBinaryNumeralTerm tokenCount),
        shift consRowsTailSuccessorTerm, #2]
  let targetLeft :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![shift (shortBinaryNumeralTerm targetBoundary),
        shift (shortBinaryNumeralTerm tokenCount),
        shift consRowsTailSuccessorTerm, #1]
  let targetRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![shift (shortBinaryNumeralTerm targetBoundary),
        shift (shortBinaryNumeralTerm tokenCount),
        shift consRowsTailSecondSuccessorTerm, #0]
  let row :=
    (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜
      ![shift (shortBinaryNumeralTerm tokenTable),
        shift (shortBinaryNumeralTerm width),
        shift (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]
  sourceLeft ⋏ (sourceRight ⋏ (targetLeft ⋏ (targetRight ⋏ row)))

theorem compactAdditiveNatListConsRowsTailBranchTerminalExplicit_code_length_le
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListConsRowsTailBranchTerminalExplicit tokenTable
        width tokenCount sourceBoundary targetBoundary)).length <=
      natListConsRowsTailBranchFormulaCodePolynomial bitBound := by
  let termCode := natListConsRowsTailTerminalTermCodePolynomial bitBound
  let entryCode := natListConsRowsTailTerminalEntryCodePolynomial termCode
  let rowCode := natListConsRowsTailTerminalRowCodePolynomial termCode
  have hclosedNumeral : forall value, Nat.size value <= bitBound ->
      (binaryTermCode
        (closedShift 4 (shortBinaryNumeralTerm value))).length <= termCode := by
    intro value hvalueSize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
    have hshift := consClosedShift_code_length_le
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 4
    dsimp only [termCode]
    unfold natListConsRowsTailTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailTerminalTermCodePolynomial
    omega
  have hfreeIndex :
      (binaryTermCode (closedShift 4 consRowsTailIndexTerm)).length <=
        termCode := by
    have hshift := consClosedShift_code_length_le consRowsTailIndexTerm
      (binaryTermCode consRowsTailIndexTerm).length le_rfl 4
    dsimp only [termCode]
    unfold natListConsRowsTailTerminalTermCodePolynomial
    omega
  have hfreeIndexSucc :
      (binaryTermCode
        (closedShift 4 consRowsTailSuccessorTerm)).length <= termCode := by
    have hshift := consClosedShift_code_length_le consRowsTailSuccessorTerm
      (binaryTermCode consRowsTailSuccessorTerm).length le_rfl 4
    dsimp only [termCode]
    unfold natListConsRowsTailTerminalTermCodePolynomial
    omega
  have hfreeIndexSucc2 :
      (binaryTermCode
        (closedShift 4 consRowsTailSecondSuccessorTerm)).length <= termCode := by
    have hshift := consClosedShift_code_length_le
      consRowsTailSecondSuccessorTerm
      (binaryTermCode consRowsTailSecondSuccessorTerm).length le_rfl 4
    dsimp only [termCode]
    unfold natListConsRowsTailTerminalTermCodePolynomial
    omega
  have htokenTable := hclosedNumeral tokenTable htokenTableSize
  have hwidth := hclosedNumeral width hwidthSize
  have htokenCount := hclosedNumeral tokenCount htokenCountSize
  have hsourceBoundary := hclosedNumeral sourceBoundary hsourceBoundarySize
  have htargetBoundary := hclosedNumeral targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
      closedShift 4 (shortBinaryNumeralTerm tokenCount),
      closedShift 4 consRowsTailIndexTerm, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
      closedShift 4 (shortBinaryNumeralTerm tokenCount),
      closedShift 4 consRowsTailSuccessorTerm, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
      closedShift 4 (shortBinaryNumeralTerm tokenCount),
      closedShift 4 consRowsTailSuccessorTerm, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
      closedShift 4 (shortBinaryNumeralTerm tokenCount),
      closedShift 4 consRowsTailSecondSuccessorTerm, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
      closedShift 4 (shortBinaryNumeralTerm width),
      closedShift 4 (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]
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
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ sourceLeftTerms
  let sourceRightFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ sourceRightTerms
  let targetLeftFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ targetLeftTerms
  let targetRightFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ targetRightTerms
  let rowFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜ rowTerms
  have hsourceLeft :
      (binaryFormulaCode sourceLeftFormula).length <= entryCode := by
    simpa only [sourceLeftFormula, entryCode,
      natListConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_consTail compactFixedWidthEntryDef.val
        termCode sourceLeftTerms hsourceLeftTerms
  have hsourceRight :
      (binaryFormulaCode sourceRightFormula).length <= entryCode := by
    simpa only [sourceRightFormula, entryCode,
      natListConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_consTail compactFixedWidthEntryDef.val
        termCode sourceRightTerms hsourceRightTerms
  have htargetLeft :
      (binaryFormulaCode targetLeftFormula).length <= entryCode := by
    simpa only [targetLeftFormula, entryCode,
      natListConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_consTail compactFixedWidthEntryDef.val
        termCode targetLeftTerms htargetLeftTerms
  have htargetRight :
      (binaryFormulaCode targetRightFormula).length <= entryCode := by
    simpa only [targetRightFormula, entryCode,
      natListConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_consTail compactFixedWidthEntryDef.val
        termCode targetRightTerms htargetRightTerms
  have hrow : (binaryFormulaCode rowFormula).length <= rowCode := by
    simpa only [rowFormula, rowCode,
      natListConsRowsTailTerminalRowCodePolynomial] using
      embeddedSubstitution_code_length_le_consTail
        compactAdditiveAtomicRowEqDef.val termCode rowTerms hrowTerms
  have htail4 := andSemiformula_code_length_le targetRightFormula rowFormula
  have htail3 := andSemiformula_code_length_le targetLeftFormula
    (targetRightFormula ⋏ rowFormula)
  have htail2 := andSemiformula_code_length_le sourceRightFormula
    (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula))
  have htotal := andSemiformula_code_length_le sourceLeftFormula
    (sourceRightFormula ⋏
      (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula)))
  change
    (binaryFormulaCode
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula))))).length <=
      natListConsRowsTailBranchFormulaCodePolynomial bitBound
  change _ <= 4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1
  omega

theorem compactAdditiveNatListConsRowsTailBranchTerminal_eq_explicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary =
      compactAdditiveNatListConsRowsTailBranchTerminalExplicit tokenTable width
        tokenCount sourceBoundary targetBoundary := by
  rfl

theorem compactAdditiveNatListConsRowsTailBranchTerminal_code_length_le_uniform
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary)).length <=
      natListConsRowsTailBranchFormulaCodePolynomial bitBound := by
  rw [compactAdditiveNatListConsRowsTailBranchTerminal_eq_explicit]
  exact
    compactAdditiveNatListConsRowsTailBranchTerminalExplicit_code_length_le
      tokenTable width tokenCount sourceBoundary targetBoundary bitBound
      htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
      htargetBoundarySize

#print axioms
  compactAdditiveNatListConsRowsTailBranchTerminalExplicit_code_length_le
#print axioms compactAdditiveNatListConsRowsTailBranchTerminal_eq_explicit
#print axioms
  compactAdditiveNatListConsRowsTailBranchTerminal_code_length_le_uniform

end FoundationCompactNumericListedDirectNatListConsRowsTailSyntaxUniformBound
