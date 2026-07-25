import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniformBranchFullyFixedBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Fixed source-body syntax for syntax-task drop two

The five-variable source terminal is bounded before the four bounded
existential layers are installed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniversalBodyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsTerminalSyntaxFixedBounds

private abbrev dropTwoPublicClosedShift :
    (arity : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat arity :=
  FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift

private def dropTwoSourceIndexTermArity05 :
    ArithmeticSemiterm Nat 5 :=
  ‘!!(dropTwoPublicClosedShift 5 (fixedNumeralTerm 2)) + #4’

private def dropTwoSourceNextTermArity05 :
    ArithmeticSemiterm Nat 5 :=
  ‘(!!(dropTwoPublicClosedShift 5 (fixedNumeralTerm 2)) + #4) + 1’

def taskDropTwoSourceTerminalTermCodePolynomial (bitBound : Nat) : Nat :=
  16 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode dropTwoSourceIndexTermArity05).length +
    (binaryTermCode dropTwoSourceNextTermArity05).length +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length + 1

def taskDropTwoSourceTerminalEntryCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def taskDropTwoSourceTerminalRowCodePolynomial (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val)).length

def taskDropTwoSourceTerminalFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := taskDropTwoSourceTerminalTermCodePolynomial bitBound
  4 * taskDropTwoSourceTerminalEntryCodePolynomial termCode +
    taskDropTwoSourceTerminalRowCodePolynomial termCode +
    4 * (binaryNatCode 4).length + 1

def taskDropTwoSourceTerminalExplicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 5 :=
  let sourceLeft :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropTwoPublicClosedShift 5
          (shortBinaryNumeralTerm sourceBoundary),
        dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        dropTwoSourceIndexTermArity05, #3]
  let sourceRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropTwoPublicClosedShift 5
          (shortBinaryNumeralTerm sourceBoundary),
        dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        dropTwoSourceNextTermArity05, #2]
  let targetLeft :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropTwoPublicClosedShift 5
          (shortBinaryNumeralTerm targetBoundary),
        dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        #4, #1]
  let targetRight :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![dropTwoPublicClosedShift 5
          (shortBinaryNumeralTerm targetBoundary),
        dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        ‘#4 + 1’, #0]
  let row :=
    (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
      ![dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenTable),
        dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm width),
        dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
        #3, #2, #1, #0]
  sourceLeft ⋏ (sourceRight ⋏ (targetLeft ⋏ (targetRight ⋏ row)))

private theorem closedShift_symbolCount
    (term : ValuationTerm) :
    forall arity,
      termSymbolCount (dropTwoPublicClosedShift arity term) =
        termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [dropTwoPublicClosedShift,
        FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift,
        termSymbolCount_bShift, closedShift_symbolCount term arity]

private theorem closedShift_code_length_le
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    forall arity,
      (binaryTermCode (dropTwoPublicClosedShift arity term)).length <=
        (2 * arity + 1) * bound
  | 0 => by
      simpa only [dropTwoPublicClosedShift,
        FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift,
        Nat.mul_zero, Nat.zero_add, Nat.one_mul] using hterm
  | arity + 1 => by
      have hinduction := closedShift_code_length_le term bound hterm arity
      have hsymbols : termSymbolCount term <= bound :=
        (termSymbolCount_le_binaryTermCode_length term).trans hterm
      have hshiftSymbols :
          termSymbolCount (dropTwoPublicClosedShift arity term) <= bound := by
        rw [closedShift_symbolCount]
        exact hsymbols
      have hshift :=
        binaryTermCode_bShift_length_le_add_symbols
          (dropTwoPublicClosedShift arity term)
      have hcoefficient :
          (2 * (arity + 1) + 1) * bound =
            (2 * arity + 1) * bound + 2 * bound := by ring
      change
        (binaryTermCode
          (Rew.bShift (dropTwoPublicClosedShift arity term))).length <= _
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

theorem taskDropTwoSourceTerminalExplicit_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (taskDropTwoSourceTerminalExplicit tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      taskDropTwoSourceTerminalFormulaCodePolynomial bitBound := by
  let termCode := taskDropTwoSourceTerminalTermCodePolynomial bitBound
  let entryCode := taskDropTwoSourceTerminalEntryCodePolynomial termCode
  let rowCode := taskDropTwoSourceTerminalRowCodePolynomial termCode
  have hshifted :
      forall value, Nat.size value <= bitBound ->
        (binaryTermCode
          (dropTwoPublicClosedShift 5
            (shortBinaryNumeralTerm value))).length <= termCode := by
    intro value hsize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hsize
    have hraw := closedShift_code_length_le
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 5
    dsimp only [termCode]
    unfold taskDropTwoSourceTerminalTermCodePolynomial
    omega
  have hsourceIndex :
      (binaryTermCode dropTwoSourceIndexTermArity05).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoSourceTerminalTermCodePolynomial
    omega
  have hsourceNext :
      (binaryTermCode dropTwoSourceNextTermArity05).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoSourceTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoSourceTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoSourceTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoSourceTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoSourceTerminalTermCodePolynomial
    omega
  have hbvar4 :
      (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskDropTwoSourceTerminalTermCodePolynomial
    omega
  have htargetNext :
      (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length <=
        termCode := by
    dsimp only [termCode]
    unfold taskDropTwoSourceTerminalTermCodePolynomial
    omega
  have htokenTable := hshifted tokenTable htokenTableSize
  have hwidth := hshifted width hwidthSize
  have htokenCount := hshifted tokenCount htokenCountSize
  have hsourceBoundary := hshifted sourceBoundary hsourceBoundarySize
  have htargetBoundary := hshifted targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropTwoPublicClosedShift 5
        (shortBinaryNumeralTerm sourceBoundary),
      dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      dropTwoSourceIndexTermArity05, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropTwoPublicClosedShift 5
        (shortBinaryNumeralTerm sourceBoundary),
      dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      dropTwoSourceNextTermArity05, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropTwoPublicClosedShift 5
        (shortBinaryNumeralTerm targetBoundary),
      dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      #4, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![dropTwoPublicClosedShift 5
        (shortBinaryNumeralTerm targetBoundary),
      dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
      ‘#4 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 5 :=
    ![dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenTable),
      dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm width),
      dropTwoPublicClosedShift 5 (shortBinaryNumeralTerm tokenCount),
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
      taskDropTwoSourceTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode sourceLeftTerms
        hsourceLeftTerms
  have hsourceRight :
      (binaryFormulaCode sourceRightFormula).length <= entryCode := by
    simpa only [sourceRightFormula, entryCode,
      taskDropTwoSourceTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode sourceRightTerms
        hsourceRightTerms
  have htargetLeft :
      (binaryFormulaCode targetLeftFormula).length <= entryCode := by
    simpa only [targetLeftFormula, entryCode,
      taskDropTwoSourceTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode targetLeftTerms
        htargetLeftTerms
  have htargetRight :
      (binaryFormulaCode targetRightFormula).length <= entryCode := by
    simpa only [targetRightFormula, entryCode,
      taskDropTwoSourceTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode targetRightTerms
        htargetRightTerms
  have hrow : (binaryFormulaCode rowFormula).length <= rowCode := by
    simpa only [rowFormula, rowCode,
      taskDropTwoSourceTerminalRowCodePolynomial] using
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
  unfold taskDropTwoSourceTerminalExplicit
  change
    (binaryFormulaCode
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula))))).length <= _
  unfold taskDropTwoSourceTerminalFormulaCodePolynomial
  dsimp only [termCode, entryCode, rowCode] at hsourceLeft hsourceRight htargetLeft htargetRight hrow ⊢
  omega

theorem
    compactAdditiveSyntaxTaskListDropTwoRowsSourceTerminal_eq_explicit
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary 2 =
      taskDropTwoSourceTerminalExplicit tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  rfl

def taskDropTwoBodyAfter04
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  (compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal tokenTable width
    tokenCount sourceBoundary targetBoundary 2).bexsLTSucc
      (dropTwoPublicClosedShift 4 (shortBinaryNumeralTerm tokenCount))

def taskDropTwoBodyAfter03
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 3 :=
  (taskDropTwoBodyAfter04 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (dropTwoPublicClosedShift 3 (shortBinaryNumeralTerm tokenCount))

def taskDropTwoBodyAfter02
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 2 :=
  (taskDropTwoBodyAfter03 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (dropTwoPublicClosedShift 2 (shortBinaryNumeralTerm tokenCount))

def taskDropTwoBodyAfter01
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (taskDropTwoBodyAfter02 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (dropTwoPublicClosedShift 1 (shortBinaryNumeralTerm tokenCount))

def taskDropTwoBodyAfter04FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 4 numericBound
    (taskDropTwoSourceTerminalFormulaCodePolynomial bitBound)

def taskDropTwoBodyAfter03FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
    (taskDropTwoBodyAfter04FormulaCodePolynomial numericBound bitBound)

def taskDropTwoBodyAfter02FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
    (taskDropTwoBodyAfter03FormulaCodePolynomial numericBound bitBound)

def taskDropTwoUniversalBodyFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
    (taskDropTwoBodyAfter02FormulaCodePolynomial numericBound bitBound)

theorem compactAdditiveSyntaxTaskListDropTwoRowsBody_eq_after01
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 2 =
      taskDropTwoBodyAfter01 tokenTable width tokenCount sourceBoundary
        targetBoundary := by
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody
    taskDropTwoBodyAfter01 taskDropTwoBodyAfter02 taskDropTwoBodyAfter03
    taskDropTwoBodyAfter04
  congr 1

private theorem recursive_body_code_le_dropTwoFixed
    {arity bound numericBound bodyCodeBound : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (hbound : bound <= numericBound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      (body.bexsLTSucc
        (dropTwoPublicClosedShift arity
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
    compactAdditiveSyntaxTaskListDropTwoRowsBody_code_length_le_fixed
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
        tokenCount sourceBoundary targetBoundary 2)).length <=
      taskDropTwoUniversalBodyFormulaCodePolynomial numericBound bitBound := by
  have hsource :
      (binaryFormulaCode
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal tokenTable
          width tokenCount sourceBoundary targetBoundary 2)).length <=
        taskDropTwoSourceTerminalFormulaCodePolynomial bitBound := by
    rw [compactAdditiveSyntaxTaskListDropTwoRowsSourceTerminal_eq_explicit]
    exact taskDropTwoSourceTerminalExplicit_code_length_le_fixed tokenTable
      width tokenCount sourceBoundary targetBoundary bitBound htokenTableSize
      hwidthSize htokenCountSize hsourceBoundarySize htargetBoundarySize
  have h04 :
      (binaryFormulaCode
        (taskDropTwoBodyAfter04 tokenTable width tokenCount sourceBoundary
          targetBoundary)).length <=
        taskDropTwoBodyAfter04FormulaCodePolynomial numericBound bitBound := by
    unfold taskDropTwoBodyAfter04
      taskDropTwoBodyAfter04FormulaCodePolynomial
    exact recursive_body_code_le_dropTwoFixed _ htokenCount hsource
  have h03 :
      (binaryFormulaCode
        (taskDropTwoBodyAfter03 tokenTable width tokenCount sourceBoundary
          targetBoundary)).length <=
        taskDropTwoBodyAfter03FormulaCodePolynomial numericBound bitBound := by
    unfold taskDropTwoBodyAfter03
      taskDropTwoBodyAfter03FormulaCodePolynomial
    exact recursive_body_code_le_dropTwoFixed _ htokenCount h04
  have h02 :
      (binaryFormulaCode
        (taskDropTwoBodyAfter02 tokenTable width tokenCount sourceBoundary
          targetBoundary)).length <=
        taskDropTwoBodyAfter02FormulaCodePolynomial numericBound bitBound := by
    unfold taskDropTwoBodyAfter02
      taskDropTwoBodyAfter02FormulaCodePolynomial
    exact recursive_body_code_le_dropTwoFixed _ htokenCount h03
  have h01 :
      (binaryFormulaCode
        (taskDropTwoBodyAfter01 tokenTable width tokenCount sourceBoundary
          targetBoundary)).length <=
        taskDropTwoUniversalBodyFormulaCodePolynomial numericBound
          bitBound := by
    unfold taskDropTwoBodyAfter01
      taskDropTwoUniversalBodyFormulaCodePolynomial
    exact recursive_body_code_le_dropTwoFixed _ htokenCount h02
  rw [compactAdditiveSyntaxTaskListDropTwoRowsBody_eq_after01]
  exact h01

private theorem dropTwoClosedShift_freeVariables_eq_empty
    (term : ValuationTerm) (hterm : term.freeVariables = ∅) :
    forall arity,
      (dropTwoPublicClosedShift arity term).freeVariables = ∅
  | 0 => by
      simpa only [dropTwoPublicClosedShift,
        FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift]
        using hterm
  | arity + 1 => by
      change
        (Rew.bShift
          (dropTwoPublicClosedShift arity term)).freeVariables = ∅
      exact bShift_freeVariables_eq_empty_of_empty _
        (dropTwoClosedShift_freeVariables_eq_empty term hterm arity)

private theorem dropTwoArithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem dropTwoBinaryFunctionTerm_freeVariables
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

private theorem dropTwoArithmeticOneTerm_freeVariables_eq_empty
    {boundArity : Nat} :
    (‘1’ : ArithmeticSemiterm Nat boundArity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem dropTwoFixedNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

private theorem
    taskDropTwoSourceTerminalExplicit_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (taskDropTwoSourceTerminalExplicit tokenTable width tokenCount
      sourceBoundary targetBoundary).freeVariables = ∅ := by
  have hshifted : forall value,
      (dropTwoPublicClosedShift 5
        (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
    intro value
    exact dropTwoClosedShift_freeVariables_eq_empty
      (shortBinaryNumeralTerm value)
      (shortBinaryNumeralTerm_freeVariables_eq_empty value) 5
  have hfixed :
      (dropTwoPublicClosedShift 5
        (fixedNumeralTerm 2)).freeVariables = ∅ := by
    exact dropTwoClosedShift_freeVariables_eq_empty
      (fixedNumeralTerm 2)
      (dropTwoFixedNumeralTerm_freeVariables_eq_empty 2) 5
  have hone :
      (‘1’ : ArithmeticSemiterm Nat 5).freeVariables = ∅ :=
    dropTwoArithmeticOneTerm_freeVariables_eq_empty
  have hsourceIndex :
      dropTwoSourceIndexTermArity05.freeVariables = ∅ := by
    unfold dropTwoSourceIndexTermArity05
    rw [dropTwoArithmeticAddTerm_eq_func,
      dropTwoBinaryFunctionTerm_freeVariables, hfixed]
    simp
  have hsourceNext :
      dropTwoSourceNextTermArity05.freeVariables = ∅ := by
    unfold dropTwoSourceNextTermArity05
    rw [dropTwoArithmeticAddTerm_eq_func,
      dropTwoBinaryFunctionTerm_freeVariables,
      dropTwoArithmeticAddTerm_eq_func,
      dropTwoBinaryFunctionTerm_freeVariables, hfixed, hone]
    simp
  have htargetNext :
      (‘#4 + 1’ : ArithmeticSemiterm Nat 5).freeVariables = ∅ := by
    rw [dropTwoArithmeticAddTerm_eq_func,
      dropTwoBinaryFunctionTerm_freeVariables, hone]
    simp
  unfold taskDropTwoSourceTerminalExplicit
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    Finset.union_eq_empty]
  repeat' apply And.intro
  all_goals
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate <;>
      simp [hshifted, hsourceIndex, hsourceNext, htargetNext]

theorem
    compactAdditiveSyntaxTaskListDropTwoRowsBody_freeVariables_eq_empty_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary 2).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary 2
  let body04 := taskDropTwoBodyAfter04 tokenTable width tokenCount
    sourceBoundary targetBoundary
  let body03 := taskDropTwoBodyAfter03 tokenTable width tokenCount
    sourceBoundary targetBoundary
  let body02 := taskDropTwoBodyAfter02 tokenTable width tokenCount
    sourceBoundary targetBoundary
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    rw [compactAdditiveSyntaxTaskListDropTwoRowsSourceTerminal_eq_explicit]
    exact taskDropTwoSourceTerminalExplicit_freeVariables_eq_empty tokenTable
      width tokenCount sourceBoundary targetBoundary
  have h04subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount terminal
  have h04 : body04.freeVariables = ∅ := by
    apply Finset.subset_empty.mp
    apply h04subset.trans
    simpa only [terminal, body04, taskDropTwoBodyAfter04] using
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
      (taskDropTwoBodyAfter01 tokenTable width tokenCount sourceBoundary
        targetBoundary).freeVariables = ∅ := by
    apply Finset.subset_empty.mp
    simpa only [taskDropTwoBodyAfter01, body02] using
      h01subset.trans (by rw [h02])
  rw [compactAdditiveSyntaxTaskListDropTwoRowsBody_eq_after01]
  exact h01

theorem
    compactAdditiveSyntaxTaskListDropTwoRowsOuterFormula_freeVariables_eq_empty_fixed
    (tokenTable width tokenCount sourceBoundary targetCount
      targetBoundary : Nat) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm targetCount))
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary 2)).freeVariables = ∅ := by
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
    compactAdditiveSyntaxTaskListDropTwoRowsBody_freeVariables_eq_empty_fixed]
  simp

#print axioms taskDropTwoSourceTerminalExplicit_code_length_le_fixed
#print axioms
  compactAdditiveSyntaxTaskListDropTwoRowsSourceTerminal_eq_explicit
#print axioms
  compactAdditiveSyntaxTaskListDropTwoRowsBody_code_length_le_fixed
#print axioms
  compactAdditiveSyntaxTaskListDropTwoRowsOuterFormula_freeVariables_eq_empty_fixed

end FoundationCompactNumericListedDirectSyntaxTaskListDropTwoRowsUniversalBodyFixedBounds
