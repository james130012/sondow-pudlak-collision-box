import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSyntaxUniformBound
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-! # Fixed syntax bound for the five-variable cons-tail source terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 320000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailSourceTerminalSyntaxUniformBound

open FoundationSuccinctFiniteConsistencyTarget
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
open FoundationCompactNumericListedDirectNatListConsRowsTailSyntaxUniformBound

def natListConsRowsTailSourceTerminalTermCodePolynomial
    (bitBound : Nat) : Nat :=
  16 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (‘#4 + 2’ : ArithmeticSemiterm Nat 5)).length + 1

def natListConsRowsTailSourceTerminalFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let termCode := natListConsRowsTailSourceTerminalTermCodePolynomial bitBound
  let entryCode := natListConsRowsTailTerminalEntryCodePolynomial termCode
  let rowCode := natListConsRowsTailTerminalRowCodePolynomial termCode
  4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1

private theorem consSourceClosedShift_symbolCount (term : ValuationTerm) :
    forall arity, termSymbolCount (closedShift arity term) =
      termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [closedShift, termSymbolCount_bShift,
        consSourceClosedShift_symbolCount term arity]

private theorem consSourceClosedShift_code_length_le
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    forall arity,
      (binaryTermCode (closedShift arity term)).length <=
        (2 * arity + 1) * bound
  | 0 => by
      simpa only [closedShift, Nat.mul_zero, Nat.zero_add, Nat.one_mul] using
        hterm
  | arity + 1 => by
      have hinduction :=
        consSourceClosedShift_code_length_le term bound hterm arity
      have hsymbols : termSymbolCount term <= bound :=
        (termSymbolCount_le_binaryTermCode_length term).trans hterm
      have hshiftSymbols :
          termSymbolCount (closedShift arity term) <= bound := by
        rw [consSourceClosedShift_symbolCount]
        exact hsymbols
      have hshift := binaryTermCode_bShift_length_le_add_symbols
        (closedShift arity term)
      have hcoefficient :
          (2 * (arity + 1) + 1) * bound =
            (2 * arity + 1) * bound + 2 * bound := by ring
      simp only [closedShift]
      rw [hcoefficient]
      omega

private theorem embeddedSubstitution_code_length_le_consSourceTail
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

theorem compactAdditiveNatListConsRowsTailSourceTerminal_code_length_le_uniform
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListConsRowsTailTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      natListConsRowsTailSourceTerminalFormulaCodePolynomial bitBound := by
  let termCode := natListConsRowsTailSourceTerminalTermCodePolynomial bitBound
  let entryCode := natListConsRowsTailTerminalEntryCodePolynomial termCode
  let rowCode := natListConsRowsTailTerminalRowCodePolynomial termCode
  have hclosedNumeral : forall value, Nat.size value <= bitBound ->
      (binaryTermCode
        (closedShift 5 (shortBinaryNumeralTerm value))).length <= termCode := by
    intro value hvalueSize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
    have hshift := consSourceClosedShift_code_length_le
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 5
    dsimp only [termCode]
    unfold natListConsRowsTailSourceTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailSourceTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailSourceTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailSourceTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailSourceTerminalTermCodePolynomial
    omega
  have hbvar4 :
      (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailSourceTerminalTermCodePolynomial
    omega
  have hsuccessor :
      (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length <=
        termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailSourceTerminalTermCodePolynomial
    omega
  have hsecondSuccessor :
      (binaryTermCode (‘#4 + 2’ : ArithmeticSemiterm Nat 5)).length <=
        termCode := by
    dsimp only [termCode]
    unfold natListConsRowsTailSourceTerminalTermCodePolynomial
    omega
  have htokenTable := hclosedNumeral tokenTable htokenTableSize
  have hwidth := hclosedNumeral width hwidthSize
  have htokenCount := hclosedNumeral tokenCount htokenCountSize
  have hsourceBoundary := hclosedNumeral sourceBoundary hsourceBoundarySize
  have htargetBoundary := hclosedNumeral targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
      closedShift 5 (shortBinaryNumeralTerm tokenCount), #4, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
      closedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
      closedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
      closedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 2’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 5 :=
    ![closedShift 5 (shortBinaryNumeralTerm tokenTable),
      closedShift 5 (shortBinaryNumeralTerm width),
      closedShift 5 (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]
  have hsourceLeftTerms : forall coordinate,
      (binaryTermCode (sourceLeftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact hsourceBoundary
    · exact htokenCount
    · exact hbvar4
    · exact hbvar3
  have hsourceRightTerms : forall coordinate,
      (binaryTermCode (sourceRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact hsourceBoundary
    · exact htokenCount
    · exact hsuccessor
    · exact hbvar2
  have htargetLeftTerms : forall coordinate,
      (binaryTermCode (targetLeftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htargetBoundary
    · exact htokenCount
    · exact hsuccessor
    · exact hbvar1
  have htargetRightTerms : forall coordinate,
      (binaryTermCode (targetRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htargetBoundary
    · exact htokenCount
    · exact hsecondSuccessor
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
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ sourceLeftTerms
  let sourceRightFormula : ArithmeticSemiformula Nat 5 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ sourceRightTerms
  let targetLeftFormula : ArithmeticSemiformula Nat 5 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ targetLeftTerms
  let targetRightFormula : ArithmeticSemiformula Nat 5 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ targetRightTerms
  let rowFormula : ArithmeticSemiformula Nat 5 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜ rowTerms
  have hsourceLeft :
      (binaryFormulaCode sourceLeftFormula).length <= entryCode := by
    simpa only [sourceLeftFormula, entryCode,
      natListConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_consSourceTail
        compactFixedWidthEntryDef.val termCode sourceLeftTerms hsourceLeftTerms
  have hsourceRight :
      (binaryFormulaCode sourceRightFormula).length <= entryCode := by
    simpa only [sourceRightFormula, entryCode,
      natListConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_consSourceTail
        compactFixedWidthEntryDef.val termCode sourceRightTerms hsourceRightTerms
  have htargetLeft :
      (binaryFormulaCode targetLeftFormula).length <= entryCode := by
    simpa only [targetLeftFormula, entryCode,
      natListConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_consSourceTail
        compactFixedWidthEntryDef.val termCode targetLeftTerms htargetLeftTerms
  have htargetRight :
      (binaryFormulaCode targetRightFormula).length <= entryCode := by
    simpa only [targetRightFormula, entryCode,
      natListConsRowsTailTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_consSourceTail
        compactFixedWidthEntryDef.val termCode targetRightTerms htargetRightTerms
  have hrow : (binaryFormulaCode rowFormula).length <= rowCode := by
    simpa only [rowFormula, rowCode,
      natListConsRowsTailTerminalRowCodePolynomial] using
      embeddedSubstitution_code_length_le_consSourceTail
        compactAdditiveAtomicRowEqDef.val termCode rowTerms hrowTerms
  have htail4 := andSemiformula_code_length_le targetRightFormula rowFormula
  have htail3 := andSemiformula_code_length_le targetLeftFormula
    (targetRightFormula ⋏ rowFormula)
  have htail2 := andSemiformula_code_length_le sourceRightFormula
    (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula))
  have htotal := andSemiformula_code_length_le sourceLeftFormula
    (sourceRightFormula ⋏
      (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula)))
  unfold compactAdditiveNatListConsRowsTailTerminal
  change
    (binaryFormulaCode
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula))))).length <= _
  change _ <=
    4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1
  omega

#print axioms
  compactAdditiveNatListConsRowsTailSourceTerminal_code_length_le_uniform

end FoundationCompactNumericListedDirectNatListConsRowsTailSourceTerminalSyntaxUniformBound
