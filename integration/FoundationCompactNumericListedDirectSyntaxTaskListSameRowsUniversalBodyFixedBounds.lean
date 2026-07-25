import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniformBranchFullyFixedBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Fixed source-body syntax for syntax-task same rows

This module bounds the actual five-variable source terminal and then the four
bounded existential layers that form the one-variable universal body.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalBodyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniformBranchFullyFixedBounds

private abbrev taskPublicClosedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k :=
  FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.closedShift

private theorem syntaxTaskClosedShift_eq_public
    (term : ValuationTerm) :
    forall arity,
      syntaxTaskListSameRowsClosedShift arity term =
        taskPublicClosedShift arity term
  | 0 => rfl
  | arity + 1 => by
      rw [syntaxTaskListSameRowsClosedShift_succ]
      change Rew.bShift (syntaxTaskListSameRowsClosedShift arity term) =
        Rew.bShift (taskPublicClosedShift arity term)
      rw [syntaxTaskClosedShift_eq_public term arity]

def taskSameRowsSourceTerminalTermCodePolynomial (bitBound : Nat) : Nat :=
  16 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length + 1

def taskSameRowsSourceTerminalFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := taskSameRowsSourceTerminalTermCodePolynomial bitBound
  let entryCode := taskSameRowsTerminalEntryCodePolynomial termCode
  let rowCode := taskSameRowsTerminalRowCodePolynomial termCode
  4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1

private theorem taskClosedShift_symbolCount_source
    (term : ValuationTerm) :
    forall arity,
      termSymbolCount (syntaxTaskListSameRowsClosedShift arity term) =
        termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [syntaxTaskListSameRowsClosedShift_succ,
        termSymbolCount_bShift,
        taskClosedShift_symbolCount_source term arity]

private theorem taskClosedShift_code_length_le_source
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    forall arity,
      (binaryTermCode
        (syntaxTaskListSameRowsClosedShift arity term)).length <=
          (2 * arity + 1) * bound
  | 0 => by
      simpa only [syntaxTaskListSameRowsClosedShift_zero, Nat.mul_zero,
        Nat.zero_add, Nat.one_mul] using hterm
  | arity + 1 => by
      have hinduction :=
        taskClosedShift_code_length_le_source term bound hterm arity
      have hsymbols : termSymbolCount term <= bound :=
        (termSymbolCount_le_binaryTermCode_length term).trans hterm
      have hshiftSymbols :
          termSymbolCount
              (syntaxTaskListSameRowsClosedShift arity term) <= bound := by
        rw [taskClosedShift_symbolCount_source]
        exact hsymbols
      have hshift :=
        binaryTermCode_bShift_length_le_add_symbols
          (syntaxTaskListSameRowsClosedShift arity term)
      have hcoefficient :
          (2 * (arity + 1) + 1) * bound =
            (2 * arity + 1) * bound + 2 * bound := by ring
      simp only [syntaxTaskListSameRowsClosedShift_succ]
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

theorem compactAdditiveSyntaxTaskListSameRowsSourceTerminal_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListSameRowsTerminal tokenTable width
        tokenCount sourceBoundary targetBoundary)).length <=
      taskSameRowsSourceTerminalFormulaCodePolynomial bitBound := by
  let termCode := taskSameRowsSourceTerminalTermCodePolynomial bitBound
  let entryCode := taskSameRowsTerminalEntryCodePolynomial termCode
  let rowCode := taskSameRowsTerminalRowCodePolynomial termCode
  have hshifted :
      forall value, Nat.size value <= bitBound ->
        (binaryTermCode
          (syntaxTaskListSameRowsClosedShift 5
            (shortBinaryNumeralTerm value))).length <= termCode := by
    intro value hsize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hsize
    have hraw := taskClosedShift_code_length_le_source
      (shortBinaryNumeralTerm value)
      (binaryNumeralTermCodeEnvelope bitBound) hbase 5
    dsimp only [termCode]
    unfold taskSameRowsSourceTerminalTermCodePolynomial
    omega
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskSameRowsSourceTerminalTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskSameRowsSourceTerminalTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskSameRowsSourceTerminalTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskSameRowsSourceTerminalTermCodePolynomial
    omega
  have hbvar4 :
      (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length <= termCode := by
    dsimp only [termCode]
    unfold taskSameRowsSourceTerminalTermCodePolynomial
    omega
  have hsuccessor :
      (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length <=
        termCode := by
    dsimp only [termCode]
    unfold taskSameRowsSourceTerminalTermCodePolynomial
    omega
  have htokenTable := hshifted tokenTable htokenTableSize
  have hwidth := hshifted width hwidthSize
  have htokenCount := hshifted tokenCount htokenCountSize
  have hsourceBoundary := hshifted sourceBoundary hsourceBoundarySize
  have htargetBoundary := hshifted targetBoundary htargetBoundarySize
  let sourceLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm sourceBoundary),
      syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm tokenCount), #4, #3]
  let sourceRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm sourceBoundary),
      syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’, #2]
  let targetLeftTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm targetBoundary),
      syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm tokenCount), #4, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm targetBoundary),
      syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 5 :=
    ![syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm tokenTable),
      syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm width),
      syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]
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
    · exact hbvar4
    · exact hbvar1
  have htargetRightTerms : forall coordinate,
      (binaryTermCode (targetRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htargetBoundary
    · exact htokenCount
    · exact hsuccessor
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
      taskSameRowsTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode sourceLeftTerms
        hsourceLeftTerms
  have hsourceRight :
      (binaryFormulaCode sourceRightFormula).length <= entryCode := by
    simpa only [sourceRightFormula, entryCode,
      taskSameRowsTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode sourceRightTerms
        hsourceRightTerms
  have htargetLeft :
      (binaryFormulaCode targetLeftFormula).length <= entryCode := by
    simpa only [targetLeftFormula, entryCode,
      taskSameRowsTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode targetLeftTerms
        htargetLeftTerms
  have htargetRight :
      (binaryFormulaCode targetRightFormula).length <= entryCode := by
    simpa only [targetRightFormula, entryCode,
      taskSameRowsTerminalEntryCodePolynomial] using
      embeddedSubstitution_code_length_le_sourceTerminal
        compactFixedWidthEntryDef.val termCode targetRightTerms
        htargetRightTerms
  have hrow : (binaryFormulaCode rowFormula).length <= rowCode := by
    simpa only [rowFormula, rowCode,
      taskSameRowsTerminalRowCodePolynomial] using
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
  unfold compactAdditiveSyntaxTaskListSameRowsTerminal
  change
    (binaryFormulaCode
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula))))).length <= _
  unfold taskSameRowsSourceTerminalFormulaCodePolynomial
  dsimp only [termCode, entryCode, rowCode] at hsourceLeft hsourceRight htargetLeft htargetRight hrow ⊢
  omega

def taskSameRowsBodyAfter04
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  (compactAdditiveSyntaxTaskListSameRowsTerminal tokenTable width tokenCount
    sourceBoundary targetBoundary).bexsLTSucc
      (taskPublicClosedShift 4
        (shortBinaryNumeralTerm tokenCount))

def taskSameRowsBodyAfter03
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 3 :=
  (taskSameRowsBodyAfter04 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (taskPublicClosedShift 3
        (shortBinaryNumeralTerm tokenCount))

def taskSameRowsBodyAfter02
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 2 :=
  (taskSameRowsBodyAfter03 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (taskPublicClosedShift 2
        (shortBinaryNumeralTerm tokenCount))

def taskSameRowsBodyAfter01
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (taskSameRowsBodyAfter02 tokenTable width tokenCount sourceBoundary
    targetBoundary).bexsLTSucc
      (taskPublicClosedShift 1
        (shortBinaryNumeralTerm tokenCount))

def taskSameRowsBodyAfter04FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 4 numericBound
    (taskSameRowsSourceTerminalFormulaCodePolynomial bitBound)

def taskSameRowsBodyAfter03FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
    (taskSameRowsBodyAfter04FormulaCodePolynomial numericBound bitBound)

def taskSameRowsBodyAfter02FormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
    (taskSameRowsBodyAfter03FormulaCodePolynomial numericBound bitBound)

def taskSameRowsUniversalBodyFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
    (taskSameRowsBodyAfter02FormulaCodePolynomial numericBound bitBound)

private theorem recursive_body_code_le_taskFixed
    {arity bound numericBound bodyCodeBound : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (hbound : bound <= numericBound)
    (hbody : (binaryFormulaCode body).length <= bodyCodeBound) :
    (binaryFormulaCode
      (body.bexsLTSucc
        (taskPublicClosedShift arity
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

theorem taskSameRowsBodyAfter04_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (taskSameRowsBodyAfter04 tokenTable width tokenCount sourceBoundary
        targetBoundary)).length <=
      taskSameRowsBodyAfter04FormulaCodePolynomial numericBound bitBound := by
  unfold taskSameRowsBodyAfter04
    taskSameRowsBodyAfter04FormulaCodePolynomial
  exact recursive_body_code_le_taskFixed
    (compactAdditiveSyntaxTaskListSameRowsTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary)
    htokenCount
    (compactAdditiveSyntaxTaskListSameRowsSourceTerminal_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary bitBound
      htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
      htargetBoundarySize)

theorem taskSameRowsBodyAfter03_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (h04 : (binaryFormulaCode
      (taskSameRowsBodyAfter04 tokenTable width tokenCount sourceBoundary
        targetBoundary)).length <=
      taskSameRowsBodyAfter04FormulaCodePolynomial numericBound bitBound) :
    (binaryFormulaCode
      (taskSameRowsBodyAfter03 tokenTable width tokenCount sourceBoundary
        targetBoundary)).length <=
      taskSameRowsBodyAfter03FormulaCodePolynomial numericBound bitBound := by
  unfold taskSameRowsBodyAfter03
    taskSameRowsBodyAfter03FormulaCodePolynomial
  exact recursive_body_code_le_taskFixed
    (taskSameRowsBodyAfter04 tokenTable width tokenCount sourceBoundary
      targetBoundary) htokenCount h04

theorem taskSameRowsBodyAfter02_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (h03 : (binaryFormulaCode
      (taskSameRowsBodyAfter03 tokenTable width tokenCount sourceBoundary
        targetBoundary)).length <=
      taskSameRowsBodyAfter03FormulaCodePolynomial numericBound bitBound) :
    (binaryFormulaCode
      (taskSameRowsBodyAfter02 tokenTable width tokenCount sourceBoundary
        targetBoundary)).length <=
      taskSameRowsBodyAfter02FormulaCodePolynomial numericBound bitBound := by
  unfold taskSameRowsBodyAfter02
    taskSameRowsBodyAfter02FormulaCodePolynomial
  exact recursive_body_code_le_taskFixed
    (taskSameRowsBodyAfter03 tokenTable width tokenCount sourceBoundary
      targetBoundary) htokenCount h03

theorem compactAdditiveSyntaxTaskListSameRowsBody_eq_after01
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary =
      taskSameRowsBodyAfter01 tokenTable width tokenCount sourceBoundary
        targetBoundary := by
  unfold compactAdditiveSyntaxTaskListSameRowsBody taskSameRowsBodyAfter01
    taskSameRowsBodyAfter02 taskSameRowsBodyAfter03
    taskSameRowsBodyAfter04
  congr 1

theorem compactAdditiveSyntaxTaskListSameRowsBody_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      taskSameRowsUniversalBodyFormulaCodePolynomial numericBound bitBound := by
  have h04 := taskSameRowsBodyAfter04_code_length_le_fixed tokenTable width
    tokenCount sourceBoundary targetBoundary numericBound bitBound
    htokenCount htokenTableSize hwidthSize htokenCountSize
    hsourceBoundarySize htargetBoundarySize
  have h03 := taskSameRowsBodyAfter03_code_length_le_fixed tokenTable width
    tokenCount sourceBoundary targetBoundary numericBound bitBound
    htokenCount h04
  have h02 := taskSameRowsBodyAfter02_code_length_le_fixed tokenTable width
    tokenCount sourceBoundary targetBoundary numericBound bitBound
    htokenCount h03
  rw [compactAdditiveSyntaxTaskListSameRowsBody_eq_after01]
  unfold taskSameRowsBodyAfter01
    taskSameRowsUniversalBodyFormulaCodePolynomial
  exact recursive_body_code_le_taskFixed
    (taskSameRowsBodyAfter02 tokenTable width tokenCount sourceBoundary
      targetBoundary) htokenCount h02

private theorem taskClosedShift_freeVariables_eq_empty_source
    (term : ValuationTerm) (hterm : term.freeVariables = ∅) :
    forall arity,
      (syntaxTaskListSameRowsClosedShift arity term).freeVariables = ∅
  | 0 => by
      simpa only [syntaxTaskListSameRowsClosedShift_zero] using hterm
  | arity + 1 => by
      rw [syntaxTaskListSameRowsClosedShift_succ]
      exact bShift_freeVariables_eq_empty_of_empty _
        (taskClosedShift_freeVariables_eq_empty_source term hterm arity)

private theorem arithmeticAddTerm_eq_func_source
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables_source
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

private theorem arithmeticOneTerm_freeVariables_eq_empty_source
    {boundArity : Nat} :
    (‘1’ : ArithmeticSemiterm Nat boundArity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem
    compactAdditiveSyntaxTaskListSameRowsSourceTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveSyntaxTaskListSameRowsTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary).freeVariables = ∅ := by
  have hshifted : forall value,
      (syntaxTaskListSameRowsClosedShift 5
        (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
    intro value
    exact taskClosedShift_freeVariables_eq_empty_source
      (shortBinaryNumeralTerm value)
      (shortBinaryNumeralTerm_freeVariables_eq_empty value) 5
  have hsuccessor :
      (‘#4 + 1’ : ArithmeticSemiterm Nat 5).freeVariables = ∅ := by
    rw [arithmeticAddTerm_eq_func_source,
      binaryFunctionTerm_freeVariables_source,
      arithmeticOneTerm_freeVariables_eq_empty_source]
    simp
  unfold compactAdditiveSyntaxTaskListSameRowsTerminal
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    Finset.union_eq_empty]
  repeat' apply And.intro
  all_goals
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate <;> simp [hshifted, hsuccessor]

theorem compactAdditiveSyntaxTaskListSameRowsBody_freeVariables_eq_empty_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary).freeVariables = ∅ := by
  let terminal := compactAdditiveSyntaxTaskListSameRowsTerminal tokenTable
    width tokenCount sourceBoundary targetBoundary
  let body04 := terminal.bexsLTSucc
    (syntaxTaskListSameRowsClosedShift 4
      (shortBinaryNumeralTerm tokenCount))
  let body03 := body04.bexsLTSucc
    (syntaxTaskListSameRowsClosedShift 3
      (shortBinaryNumeralTerm tokenCount))
  let body02 := body03.bexsLTSucc
    (syntaxTaskListSameRowsClosedShift 2
      (shortBinaryNumeralTerm tokenCount))
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    exact
      compactAdditiveSyntaxTaskListSameRowsSourceTerminal_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary targetBoundary
  have h04subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount terminal
  have h04 : body04.freeVariables = ∅ :=
    Finset.subset_empty.mp (h04subset.trans (by rw [hterminal]))
  have h03subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount body04
  have h03 : body03.freeVariables = ∅ :=
    Finset.subset_empty.mp (h03subset.trans (by rw [h04]))
  have h02subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount body03
  have h02 : body02.freeVariables = ∅ :=
    Finset.subset_empty.mp (h02subset.trans (by rw [h03]))
  have h01subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount body02
  have h01 :
      (body02.bexsLTSucc
        (syntaxTaskListSameRowsClosedShift 1
          (shortBinaryNumeralTerm tokenCount))).freeVariables = ∅ :=
    Finset.subset_empty.mp (h01subset.trans (by rw [h02]))
  simpa only [compactAdditiveSyntaxTaskListSameRowsBody, terminal, body04,
    body03, body02] using h01

theorem
    compactAdditiveSyntaxTaskListSameRowsOuterFormula_freeVariables_eq_empty_fixed
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary : Nat) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount))
      (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary)).freeVariables = ∅ := by
  have hshift :
      (Rew.bShift
        (shortBinaryNumeralTerm sourceCount : ValuationTerm)).freeVariables =
          ∅ :=
    bShift_freeVariables_eq_empty_of_empty _
      (shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount)
  have htermBound :
      (termBoundFormula
        (Rew.bShift
          (shortBinaryNumeralTerm sourceCount : ValuationTerm))).freeVariables =
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
                (shortBinaryNumeralTerm sourceCount :
                  ValuationTerm)).freeVariables at hcoordinate
            rw [hshift] at hcoordinate
            simp at hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  simp only [LO.FirstOrder.Semiformula.freeVariables_all,
    termBoundedUniversalBody, LO.FirstOrder.Semiformula.freeVariables_imp,
    htermBound,
    compactAdditiveSyntaxTaskListSameRowsBody_freeVariables_eq_empty_fixed]
  simp

#print axioms
  compactAdditiveSyntaxTaskListSameRowsSourceTerminal_code_length_le_fixed
#print axioms compactAdditiveSyntaxTaskListSameRowsBody_code_length_le_fixed
#print axioms
  compactAdditiveSyntaxTaskListSameRowsOuterFormula_freeVariables_eq_empty_fixed

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniversalBodyFixedBounds
