import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsUniformBranchFullyFixedBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Fixed source-body syntax for syntax-task drop one

The five-variable source terminal is bounded before the four bounded
existential layers are installed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsUniversalBodyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsTerminalSyntaxFixedBounds

private abbrev dropOnePublicClosedShift :
    (arity : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat arity :=
  FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift

private def dropOneSourceIndexTermArity05 :
    ArithmeticSemiterm Nat 5 :=
  ‘!!(dropOnePublicClosedShift 5 (fixedNumeralTerm 1)) + #4’

private def dropOneSourceNextTermArity05 :
    ArithmeticSemiterm Nat 5 :=
  ‘(!!(dropOnePublicClosedShift 5 (fixedNumeralTerm 1)) + #4) + 1’

def taskDropOneSourceTerminalTermCodePolynomial (bitBound : Nat) : Nat :=
  16 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode dropOneSourceIndexTermArity05).length +
    (binaryTermCode dropOneSourceNextTermArity05).length +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length + 1

def taskDropOneSourceTerminalEntryCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def taskDropOneSourceTerminalRowCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val)).length

def taskDropOneSourceTerminalFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := taskDropOneSourceTerminalTermCodePolynomial bitBound
  4 * taskDropOneSourceTerminalEntryCodePolynomial termCode +
    taskDropOneSourceTerminalRowCodePolynomial termCode +
    4 * (binaryNatCode 4).length + 1

def taskDropOneSourceTerminalExplicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 5 :=
  let sourceLeft :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropOnePublicClosedShift 5
          (shortBinaryNumeralTerm sourceBoundary),
        dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        dropOneSourceIndexTermArity05, #3]
  let sourceRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropOnePublicClosedShift 5
          (shortBinaryNumeralTerm sourceBoundary),
        dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        dropOneSourceNextTermArity05, #2]
  let targetLeft :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropOnePublicClosedShift 5
          (shortBinaryNumeralTerm targetBoundary),
        dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        #4, #1]
  let targetRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropOnePublicClosedShift 5
          (shortBinaryNumeralTerm targetBoundary),
        dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        ‘#4 + 1’, #0]
  let row :=
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      ![dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenTable),
        dropOnePublicClosedShift 5 (shortBinaryNumeralTerm width),
        dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        #3, #2, #1, #0]
  sourceLeft ⋏ (sourceRight ⋏ (targetLeft ⋏ (targetRight ⋏ row)))

private theorem closedShift_symbolCount
    (term : ValuationTerm) :
    forall arity,
      termSymbolCount (dropOnePublicClosedShift arity term) =
        termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [dropOnePublicClosedShift,
        FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift,
        termSymbolCount_bShift, closedShift_symbolCount term arity]

private theorem closedShift_code_length_le
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    forall arity,
      (binaryTermCode (dropOnePublicClosedShift arity term)).length <=
        (2 * arity + 1) * bound
  | 0 => by
      simpa only [dropOnePublicClosedShift,
        FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift,
        Nat.mul_zero, Nat.zero_add, Nat.one_mul] using hterm
  | arity + 1 => by
      have hinduction := closedShift_code_length_le term bound hterm arity
      have hsymbols : termSymbolCount term <= bound :=
        (termSymbolCount_le_binaryTermCode_length term).trans hterm
      have hshiftSymbols :
          termSymbolCount (dropOnePublicClosedShift arity term) <= bound := by
        rw [closedShift_symbolCount]
        exact hsymbols
      have hshift :=
        binaryTermCode_bShift_length_le_add_symbols
          (dropOnePublicClosedShift arity term)
      have hcoefficient :
          (2 * (arity + 1) + 1) * bound =
            (2 * arity + 1) * bound + 2 * bound := by ring
      change
        (binaryTermCode
          (Rew.bShift (dropOnePublicClosedShift arity term))).length <= _
      rw [hcoefficient]
      omega

private theorem embeddedSubstitution_code_length_le_sourceTerminal
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

theorem taskDropOneSourceTerminalExplicit_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (taskDropOneSourceTerminalExplicit tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      taskDropOneSourceTerminalFormulaCodePolynomial bitBound := by
  let termCode := taskDropOneSourceTerminalTermCodePolynomial bitBound
  let entryCode := taskDropOneSourceTerminalEntryCodePolynomial termCode
  let rowCode := taskDropOneSourceTerminalRowCodePolynomial termCode
  have hshifted :
      forall value, Nat.size value <= bitBound ->
        (binaryTermCode
          (dropOnePublicClosedShift 5
            (shortBinaryNumeralTerm value))).length <= termCode := by
    intro value hsize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hsize
    have hraw := closedShift_code_length_le
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 5
    dsimp only [termCode]
    unfold taskDropOneSourceTerminalTermCodePolynomial
    omega
  have hsourceIndex :
      (binaryTermCode dropOneSourceIndexTermArity05).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropOneSourceTerminalTermCodePolynomial
    omega
  have hsourceNext :
      (binaryTermCode dropOneSourceNextTermArity05).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropOneSourceTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropOneSourceTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropOneSourceTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropOneSourceTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropOneSourceTerminalTermCodePolynomial
    omega
  have hbvar4 :
      (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropOneSourceTerminalTermCodePolynomial
    omega
  have htargetNext :
      (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length <=
        termCode := by
    dsimp only [termCode]
    unfold taskDropOneSourceTerminalTermCodePolynomial
    omega
  have htokenTable := hshifted tokenTable htokenTableSize
  have hwidth := hshifted width hwidthSize
  have htokenCount := hshifted tokenCount htokenCountSize
  have hsourceBoundary := hshifted sourceBoundary hsourceBoundarySize
  have htargetBoundary := hshifted targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropOnePublicClosedShift 5
        (shortBinaryNumeralTerm sourceBoundary),
      dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      dropOneSourceIndexTermArity05, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropOnePublicClosedShift 5
        (shortBinaryNumeralTerm sourceBoundary),
      dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      dropOneSourceNextTermArity05, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropOnePublicClosedShift 5
        (shortBinaryNumeralTerm targetBoundary),
      dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      #4, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropOnePublicClosedShift 5
        (shortBinaryNumeralTerm targetBoundary),
      dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      ‘#4 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 5 :=
    ![dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenTable),
      dropOnePublicClosedShift 5 (shortBinaryNumeralTerm width),
      dropOnePublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
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
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      rowTerms
  have hsourceLeft :
      (binaryFormulaCode sourceLeftFormula).length <= entryCode := by
    simpa only [sourceLeftFormula, entryCode,
      taskDropOneSourceTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode sourceLeftTerms
        hsourceLeftTerms
  have hsourceRight :
      (binaryFormulaCode sourceRightFormula).length <= entryCode := by
    simpa only [sourceRightFormula, entryCode,
      taskDropOneSourceTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode sourceRightTerms
        hsourceRightTerms
  have htargetLeft :
      (binaryFormulaCode targetLeftFormula).length <= entryCode := by
    simpa only [targetLeftFormula, entryCode,
      taskDropOneSourceTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode targetLeftTerms
        htargetLeftTerms
  have htargetRight :
      (binaryFormulaCode targetRightFormula).length <= entryCode := by
    simpa only [targetRightFormula, entryCode,
      taskDropOneSourceTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode targetRightTerms
        htargetRightTerms
  have hrow : (binaryFormulaCode rowFormula).length <= rowCode := by
    simpa only [rowFormula, rowCode,
      taskDropOneSourceTerminalRowCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactAdditiveSyntaxTaskRowEqDef.val termCode rowTerms hrowTerms
  have htail4 := andSemiformula_code_length_le targetRightFormula rowFormula
  have htail3 := andSemiformula_code_length_le targetLeftFormula
    (targetRightFormula ⋏ rowFormula)
  have htail2 := andSemiformula_code_length_le sourceRightFormula
    (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula))
  have htotal := andSemiformula_code_length_le sourceLeftFormula
    (sourceRightFormula ⋏
      (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula)))
  unfold taskDropOneSourceTerminalExplicit
  change
    (binaryFormulaCode
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula))))).length <= _
  unfold taskDropOneSourceTerminalFormulaCodePolynomial
  dsimp only [termCode, entryCode, rowCode] at hsourceLeft hsourceRight htargetLeft htargetRight hrow ⊢
  omega

theorem
    compactAdditiveSyntaxTaskListDropOneRowsSourceTerminal_eq_explicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary 1 =
      taskDropOneSourceTerminalExplicit tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  rfl

def taskDropOneBodyAfter04
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  (compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal tokenTable width
    tokenCount sourceBoundary targetBoundary 1).bexsLTSucc
      (dropOnePublicClosedShift 4 (shortBinaryNumeralTerm tokenCount))

def taskDropOneBodyAfter03
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 3 :=
  (taskDropOneBodyAfter04 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (dropOnePublicClosedShift 3 (shortBinaryNumeralTerm tokenCount))

def taskDropOneBodyAfter02
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 2 :=
  (taskDropOneBodyAfter03 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (dropOnePublicClosedShift 2 (shortBinaryNumeralTerm tokenCount))

def taskDropOneBodyAfter01
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (taskDropOneBodyAfter02 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (dropOnePublicClosedShift 1 (shortBinaryNumeralTerm tokenCount))

def taskDropOneBodyAfter04FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 4 numericBound
    (taskDropOneSourceTerminalFormulaCodePolynomial bitBound)

def taskDropOneBodyAfter03FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
    (taskDropOneBodyAfter04FormulaCodePolynomial numericBound bitBound)

def taskDropOneBodyAfter02FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
    (taskDropOneBodyAfter03FormulaCodePolynomial numericBound bitBound)

def taskDropOneUniversalBodyFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
    (taskDropOneBodyAfter02FormulaCodePolynomial numericBound bitBound)

theorem compactAdditiveSyntaxTaskListDropOneRowsBody_eq_after01
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 1 =
      taskDropOneBodyAfter01 tokenTable width tokenCount sourceBoundary
        targetBoundary := by
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody
    taskDropOneBodyAfter01 taskDropOneBodyAfter02 taskDropOneBodyAfter03
    taskDropOneBodyAfter04
  congr 1

private theorem recursive_body_code_le_dropOneFixed
    {arity bound numericBound bodyCodeBound : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (hbound : bound <= numericBound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      (body.bexsLTSucc
        (dropOnePublicClosedShift arity
          (shortBinaryNumeralTerm bound)))).length <=
      explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity numericBound
        bodyCodeBound := by
  have hraw :=
    explicitBoundedWitnessRecursiveBody_code_length_le_public
      bound bodyCodeBound body hbody
  have hmono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_hybridFixed
      arity hbound (Nat.le_refl bodyCodeBound)
  exact hraw.trans hmono

theorem
    compactAdditiveSyntaxTaskListDropOneRowsBody_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 1)).length <=
      taskDropOneUniversalBodyFormulaCodePolynomial numericBound bitBound := by
  have hsource :
      (binaryFormulaCode
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal tokenTable
          width tokenCount sourceBoundary targetBoundary 1)).length <=
        taskDropOneSourceTerminalFormulaCodePolynomial bitBound := by
    rw [compactAdditiveSyntaxTaskListDropOneRowsSourceTerminal_eq_explicit]
    exact taskDropOneSourceTerminalExplicit_code_length_le_fixed tokenTable
      width tokenCount sourceBoundary targetBoundary bitBound htokenTableSize
      hwidthSize htokenCountSize hsourceBoundarySize htargetBoundarySize
  have h04 :
      (binaryFormulaCode
        (taskDropOneBodyAfter04 tokenTable width tokenCount sourceBoundary
          targetBoundary)).length <=
        taskDropOneBodyAfter04FormulaCodePolynomial numericBound bitBound := by
    unfold taskDropOneBodyAfter04
      taskDropOneBodyAfter04FormulaCodePolynomial
    exact recursive_body_code_le_dropOneFixed _ htokenCount hsource
  have h03 :
      (binaryFormulaCode
        (taskDropOneBodyAfter03 tokenTable width tokenCount sourceBoundary
          targetBoundary)).length <=
        taskDropOneBodyAfter03FormulaCodePolynomial numericBound bitBound := by
    unfold taskDropOneBodyAfter03
      taskDropOneBodyAfter03FormulaCodePolynomial
    exact recursive_body_code_le_dropOneFixed _ htokenCount h04
  have h02 :
      (binaryFormulaCode
        (taskDropOneBodyAfter02 tokenTable width tokenCount sourceBoundary
          targetBoundary)).length <=
        taskDropOneBodyAfter02FormulaCodePolynomial numericBound bitBound := by
    unfold taskDropOneBodyAfter02
      taskDropOneBodyAfter02FormulaCodePolynomial
    exact recursive_body_code_le_dropOneFixed _ htokenCount h03
  have h01 :
      (binaryFormulaCode
        (taskDropOneBodyAfter01 tokenTable width tokenCount sourceBoundary
          targetBoundary)).length <=
        taskDropOneUniversalBodyFormulaCodePolynomial numericBound
          bitBound := by
    unfold taskDropOneBodyAfter01
      taskDropOneUniversalBodyFormulaCodePolynomial
    exact recursive_body_code_le_dropOneFixed _ htokenCount h02
  rw [compactAdditiveSyntaxTaskListDropOneRowsBody_eq_after01]
  exact h01

private theorem dropOneClosedShift_freeVariables_eq_empty
    (term : ValuationTerm) (hterm : term.freeVariables = ∅) :
    forall arity,
      (dropOnePublicClosedShift arity term).freeVariables = ∅
  | 0 => by
      simpa only [dropOnePublicClosedShift,
        FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
        using hterm
  | arity + 1 => by
      change
        (Rew.bShift
          (dropOnePublicClosedShift arity term)).freeVariables = ∅
      exact bShift_freeVariables_eq_empty_of_empty _
        (dropOneClosedShift_freeVariables_eq_empty term hterm arity)

private theorem dropOneArithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem dropOneBinaryFunctionTerm_freeVariables
    {boundArity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ArithmeticSemiterm Nat boundArity) :
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

private theorem dropOneArithmeticOneTerm_freeVariables_eq_empty
    {boundArity : Nat} :
    (‘1’ : ArithmeticSemiterm Nat boundArity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem dropOneFixedNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

private theorem
    taskDropOneSourceTerminalExplicit_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (taskDropOneSourceTerminalExplicit tokenTable width tokenCount
      sourceBoundary targetBoundary).freeVariables = ∅ := by
  have hshifted : forall value,
      (dropOnePublicClosedShift 5
        (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
    intro value
    exact dropOneClosedShift_freeVariables_eq_empty
      (shortBinaryNumeralTerm value)
      (shortBinaryNumeralTerm_freeVariables_eq_empty value) 5
  have hfixed :
      (dropOnePublicClosedShift 5
        (fixedNumeralTerm 1)).freeVariables = ∅ := by
    exact dropOneClosedShift_freeVariables_eq_empty
      (fixedNumeralTerm 1)
      (dropOneFixedNumeralTerm_freeVariables_eq_empty 1) 5
  have hone :
      (‘1’ : ArithmeticSemiterm Nat 5).freeVariables = ∅ :=
    dropOneArithmeticOneTerm_freeVariables_eq_empty
  have hsourceIndex :
      dropOneSourceIndexTermArity05.freeVariables = ∅ := by
    unfold dropOneSourceIndexTermArity05
    rw [dropOneArithmeticAddTerm_eq_func,
      dropOneBinaryFunctionTerm_freeVariables, hfixed]
    simp
  have hsourceNext :
      dropOneSourceNextTermArity05.freeVariables = ∅ := by
    unfold dropOneSourceNextTermArity05
    rw [dropOneArithmeticAddTerm_eq_func,
      dropOneBinaryFunctionTerm_freeVariables,
      dropOneArithmeticAddTerm_eq_func,
      dropOneBinaryFunctionTerm_freeVariables, hfixed, hone]
    simp
  have htargetNext :
      (‘#4 + 1’ : ArithmeticSemiterm Nat 5).freeVariables = ∅ := by
    rw [dropOneArithmeticAddTerm_eq_func,
      dropOneBinaryFunctionTerm_freeVariables, hone]
    simp
  unfold taskDropOneSourceTerminalExplicit
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    Finset.union_eq_empty]
  repeat' apply And.intro
  all_goals
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate <;>
      simp [hshifted, hsourceIndex, hsourceNext, htargetNext]

theorem
    compactAdditiveSyntaxTaskListDropOneRowsBody_freeVariables_eq_empty_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 1).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary 1
  let body04 := taskDropOneBodyAfter04 tokenTable width tokenCount
    sourceBoundary targetBoundary
  let body03 := taskDropOneBodyAfter03 tokenTable width tokenCount
    sourceBoundary targetBoundary
  let body02 := taskDropOneBodyAfter02 tokenTable width tokenCount
    sourceBoundary targetBoundary
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    rw [compactAdditiveSyntaxTaskListDropOneRowsSourceTerminal_eq_explicit]
    exact taskDropOneSourceTerminalExplicit_freeVariables_eq_empty tokenTable
      width tokenCount sourceBoundary targetBoundary
  have h04subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount terminal
  have h04 : body04.freeVariables = ∅ := by
    apply Finset.subset_empty.mp
    apply h04subset.trans
    simpa only [terminal, body04, taskDropOneBodyAfter04] using
      Finset.subset_of_eq hterminal
  have h03subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount body04
  have h03 : body03.freeVariables = ∅ := by
    apply Finset.subset_empty.mp
    exact h03subset.trans (by rw [h04])
  have h02subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount body03
  have h02 : body02.freeVariables = ∅ := by
    apply Finset.subset_empty.mp
    exact h02subset.trans (by rw [h03])
  have h01subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount body02
  have h01 :
      (taskDropOneBodyAfter01 tokenTable width tokenCount sourceBoundary
        targetBoundary).freeVariables = ∅ := by
    apply Finset.subset_empty.mp
    simpa only [taskDropOneBodyAfter01, body02] using
      h01subset.trans (by rw [h02])
  rw [compactAdditiveSyntaxTaskListDropOneRowsBody_eq_after01]
  exact h01

theorem
    compactAdditiveSyntaxTaskListDropOneRowsOuterFormula_freeVariables_eq_empty_fixed
    (tokenTable width tokenCount sourceBoundary targetCount
      targetBoundary : Nat) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm targetCount))
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
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
          (shortBinaryNumeralTerm targetCount :
            ValuationTerm))).freeVariables = ∅ := by
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
    compactAdditiveSyntaxTaskListDropOneRowsBody_freeVariables_eq_empty_fixed]
  simp

#print axioms taskDropOneSourceTerminalExplicit_code_length_le_fixed
#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsSourceTerminal_eq_explicit
#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsBody_code_length_le_fixed
#print axioms
  compactAdditiveSyntaxTaskListDropOneRowsOuterFormula_freeVariables_eq_empty_fixed

end FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsUniversalBodyFixedBounds
