import integration.FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds
import integration.FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Fixed-polynomial route for equal natural-list rows

The first endpoint removes all four concrete row-entry witness values from the
bounded-existential prefix.  The remaining terminal resource is isolated for
the five-leaf fixed-width/atomic-row assembly bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListSameRowsFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
open FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
open FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationBounds

private abbrev sameRowsZeroValuationFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.zeroValuation

private theorem arithmeticAddTerm_freeVariables_sameRowsFixed
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

private theorem arithmeticOneTerm_freeVariables_sameRowsFixed
    {Variable : Type*} [DecidableEq Variable] {arity : Nat} :
    (‘1’ : ArithmeticSemiterm Variable arity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

@[simp] private theorem closedShiftShortNumeral_freeVariables_eq_empty
    (arity value : Nat) :
    (closedShift arity
      (shortBinaryNumeralTerm value : ValuationTerm)).freeVariables = ∅ := by
  induction arity with
  | zero =>
      simpa only [closedShift] using
        shortBinaryNumeralTerm_freeVariables_eq_empty value
  | succ arity ih =>
      simp only [closedShift]
      exact bShift_freeVariables_eq_empty_of_empty _ ih

@[simp] private theorem boundSuccessorTerm_freeVariables_eq_empty :
    (‘#4 + 1’ : ArithmeticSemiterm Nat 5).freeVariables = ∅ := by
  rw [arithmeticAddTerm_freeVariables_sameRowsFixed,
    arithmeticOneTerm_freeVariables_sameRowsFixed]
  simp

private theorem freeFormulaAtArity_freeVariables_subset_sameRowsFixed
    {arity : Nat}
    (formula : ArithmeticSemiformula Nat (arity + 1)) :
    (Rewriting.free formula).freeVariables ⊆
      insert 0 (formula.freeVariables.image Nat.succ) := by
  intro index hindex
  have hrewritten : (Rewriting.free formula).FVar? index := hindex
  rcases LO.FirstOrder.Semiformula.fvar?_rew hrewritten with
      hbound | hfree
  · rcases hbound with ⟨boundIndex, hboundIndex⟩
    cases boundIndex using Fin.lastCases with
    | last =>
        have hindexZero : index = 0 := by
          have hzeroIndex : 0 = index := by
            simpa [LO.FirstOrder.Semiformula.FVar?] using hboundIndex
          exact hzeroIndex.symm
        subst index
        exact Finset.mem_insert_self _ _
    | cast previous =>
        simp at hboundIndex
  · rcases hfree with ⟨sourceIndex, hsource, himage⟩
    have hindexSucc : index = sourceIndex + 1 := by
      have hsuccIndex : sourceIndex + 1 = index := by
        simpa [LO.FirstOrder.Semiformula.FVar?] using himage
      exact hsuccIndex.symm
    subst index
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨sourceIndex, hsource, rfl⟩)

private theorem
    compactAdditiveNatListSameRowsTerminal_freeVariables_eq_empty_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListSameRowsTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary).freeVariables = ∅ := by
  unfold compactAdditiveNatListSameRowsTerminal
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    Finset.union_eq_empty]
  repeat' apply And.intro
  all_goals
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate <;> simp

theorem
    compactAdditiveNatListSameRowsBranchTerminal_freeVariables_subset_singleton
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListSameRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary).freeVariables ⊆ {0} := by
  rw [← compactAdditiveNatListSameRowsTerminal_free_alignment]
  have hsubset := freeFormulaAtArity_freeVariables_subset_sameRowsFixed
    (compactAdditiveNatListSameRowsTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary)
  rw [compactAdditiveNatListSameRowsTerminal_freeVariables_eq_empty_fixed]
    at hsubset
  simpa using hsubset

private theorem bexsLTSucc_freeVariables_eq_empty_of_empty_sameRowsFixed
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity)
    (hbody : body.freeVariables = ∅)
    (hbound : bound.freeVariables = ∅) :
    (body.bexsLTSucc bound).freeVariables = ∅ := by
  have hone : (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ :=
    arithmeticOneTerm_freeVariables_sameRowsFixed
  have hsuccessor :
      (‘!!bound + 1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    rw [arithmeticAddTerm_freeVariables_sameRowsFixed, hbound, hone]
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

@[simp] theorem compactAdditiveNatListSameRowsBody_freeVariables_eq_empty_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary).freeVariables = ∅ := by
  let terminal := compactAdditiveNatListSameRowsTerminal tokenTable width
    tokenCount sourceBoundary targetBoundary
  let bound4 := closedShift 4 (shortBinaryNumeralTerm tokenCount)
  let bound3 := closedShift 3 (shortBinaryNumeralTerm tokenCount)
  let bound2 := closedShift 2 (shortBinaryNumeralTerm tokenCount)
  let bound1 := closedShift 1 (shortBinaryNumeralTerm tokenCount)
  have hterminal : terminal.freeVariables = ∅ :=
    compactAdditiveNatListSameRowsTerminal_freeVariables_eq_empty_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary
  have hbound4 : bound4.freeVariables = ∅ := by
    simp only [bound4, closedShiftShortNumeral_freeVariables_eq_empty]
  have hbound3 : bound3.freeVariables = ∅ := by
    simp only [bound3, closedShiftShortNumeral_freeVariables_eq_empty]
  have hbound2 : bound2.freeVariables = ∅ := by
    simp only [bound2, closedShiftShortNumeral_freeVariables_eq_empty]
  have hbound1 : bound1.freeVariables = ∅ := by
    simp only [bound1, closedShiftShortNumeral_freeVariables_eq_empty]
  have hstep4 := bexsLTSucc_freeVariables_eq_empty_of_empty_sameRowsFixed
    terminal bound4 hterminal hbound4
  have hstep3 := bexsLTSucc_freeVariables_eq_empty_of_empty_sameRowsFixed
    (terminal.bexsLTSucc bound4) bound3 hstep4 hbound3
  have hstep2 := bexsLTSucc_freeVariables_eq_empty_of_empty_sameRowsFixed
    ((terminal.bexsLTSucc bound4).bexsLTSucc bound3) bound2
    hstep3 hbound2
  have hstep1 := bexsLTSucc_freeVariables_eq_empty_of_empty_sameRowsFixed
    (((terminal.bexsLTSucc bound4).bexsLTSucc bound3).bexsLTSucc bound2)
    bound1 hstep2 hbound1
  simpa only [compactAdditiveNatListSameRowsBody, terminal, bound4, bound3,
    bound2, bound1] using hstep1

@[simp] theorem
    compactAdditiveNatListSameRowsOuterFormula_freeVariables_eq_empty_fixed
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary : Nat) :
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount))
      (compactAdditiveNatListSameRowsBody tokenTable width tokenCount
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
    compactAdditiveNatListSameRowsBody_freeVariables_eq_empty_fixed]
  simp

def sameRowsUniversalSubstitutionTermCodePolynomial
    (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  11 * numeralCode +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length +
    (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length + 1

def sameRowsEmbeddedEntryFormulaCodeFromTermPolynomial
    (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def sameRowsEmbeddedRowFormulaCodeFromTermPolynomial
    (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val)).length

def sameRowsUniversalTerminalFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let termCode := sameRowsUniversalSubstitutionTermCodePolynomial bitBound
  let entryCode := sameRowsEmbeddedEntryFormulaCodeFromTermPolynomial termCode
  let rowCode := sameRowsEmbeddedRowFormulaCodeFromTermPolynomial termCode
  4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1

def sameRowsUniversalBodyFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  let terminalCode := sameRowsUniversalTerminalFormulaCodePolynomial bitBound
  let bodyCode03 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 4 numericBound
      terminalCode
  let bodyCode02 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 numericBound
      bodyCode03
  let bodyCode01 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 numericBound
      bodyCode02
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
    bodyCode01

private theorem termSymbolCount_closedShift_sameRowsFixed
    (term : ValuationTerm) :
    forall arity,
      termSymbolCount (closedShift arity term) = termSymbolCount term
  | 0 => rfl
  | arity + 1 => by
      simp only [closedShift, termSymbolCount_bShift,
        termSymbolCount_closedShift_sameRowsFixed term arity]

private theorem closedShift_code_length_le_linear_sameRowsFixed
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    forall arity,
      (binaryTermCode (closedShift arity term)).length <=
        (2 * arity + 1) * bound
  | 0 => by simpa [closedShift] using hterm
  | arity + 1 => by
      have hinduction :=
        closedShift_code_length_le_linear_sameRowsFixed term bound hterm arity
      have hsymbols : termSymbolCount term <= bound :=
        (termSymbolCount_le_binaryTermCode_length term).trans hterm
      have hshiftSymbols :
          termSymbolCount (closedShift arity term) <= bound := by
        rw [termSymbolCount_closedShift_sameRowsFixed]
        exact hsymbols
      have hshift :=
        binaryTermCode_bShift_length_le_add_symbols
          (closedShift arity term)
      have hcoefficient :
          (2 * (arity + 1) + 1) * bound =
            (2 * arity + 1) * bound + 2 * bound := by
        ring
      simp only [closedShift]
      rw [hcoefficient]
      omega

private theorem embeddedSubstitution_code_length_le_sameRowsFixed
    {sourceArity targetArity : Nat}
    (source : ArithmeticSemiformula Nat sourceArity)
    (termCode : Nat)
    (terms : Fin sourceArity -> ArithmeticSemiterm Nat targetArity)
    (hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode) :
    (binaryFormulaCode
      (source ⇜ terms)).length <=
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

theorem compactAdditiveNatListSameRowsTerminal_code_length_le_fixed
    (tokenTable width tokenCount sourceBoundary targetBoundary bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListSameRowsTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      sameRowsUniversalTerminalFormulaCodePolynomial bitBound := by
  let termCode := sameRowsUniversalSubstitutionTermCodePolynomial bitBound
  let entryCode := sameRowsEmbeddedEntryFormulaCodeFromTermPolynomial termCode
  let rowCode := sameRowsEmbeddedRowFormulaCodeFromTermPolynomial termCode
  have hclosedNumeral :
      forall value, Nat.size value <= bitBound ->
        (binaryTermCode
          (closedShift 5 (shortBinaryNumeralTerm value))).length <=
            termCode := by
    intro value hvalueSize
    have hbase :=
      binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
    have hshift :=
      closedShift_code_length_le_linear_sameRowsFixed
        (shortBinaryNumeralTerm value)
        (binaryNumeralTermCodeEnvelope bitBound) hbase 5
    dsimp only [termCode]
    unfold sameRowsUniversalSubstitutionTermCodePolynomial
    dsimp only
    omega
  have hbvar0 : (binaryTermCode (#0 : ArithmeticSemiterm Nat 5)).length <=
      termCode := by
    dsimp only [termCode]
    unfold sameRowsUniversalSubstitutionTermCodePolynomial
    dsimp only
    omega
  have hbvar1 : (binaryTermCode (#1 : ArithmeticSemiterm Nat 5)).length <=
      termCode := by
    dsimp only [termCode]
    unfold sameRowsUniversalSubstitutionTermCodePolynomial
    dsimp only
    omega
  have hbvar2 : (binaryTermCode (#2 : ArithmeticSemiterm Nat 5)).length <=
      termCode := by
    dsimp only [termCode]
    unfold sameRowsUniversalSubstitutionTermCodePolynomial
    dsimp only
    omega
  have hbvar3 : (binaryTermCode (#3 : ArithmeticSemiterm Nat 5)).length <=
      termCode := by
    dsimp only [termCode]
    unfold sameRowsUniversalSubstitutionTermCodePolynomial
    dsimp only
    omega
  have hbvar4 : (binaryTermCode (#4 : ArithmeticSemiterm Nat 5)).length <=
      termCode := by
    dsimp only [termCode]
    unfold sameRowsUniversalSubstitutionTermCodePolynomial
    dsimp only
    omega
  have hbvar4Succ :
      (binaryTermCode (‘#4 + 1’ : ArithmeticSemiterm Nat 5)).length <=
        termCode := by
    dsimp only [termCode]
    unfold sameRowsUniversalSubstitutionTermCodePolynomial
    dsimp only
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
      closedShift 5 (shortBinaryNumeralTerm tokenCount), #4, #1]
  let targetRightTerms : Fin 4 -> ArithmeticSemiterm Nat 5 :=
    ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
      closedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’, #0]
  let rowTerms : Fin 7 -> ArithmeticSemiterm Nat 5 :=
    ![closedShift 5 (shortBinaryNumeralTerm tokenTable),
      closedShift 5 (shortBinaryNumeralTerm width),
      closedShift 5 (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]
  have hsourceLeftTerms : forall coordinate,
      (binaryTermCode (sourceLeftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate <;>
      assumption
  have hsourceRightTerms : forall coordinate,
      (binaryTermCode (sourceRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate <;>
      assumption
  have htargetLeftTerms : forall coordinate,
      (binaryTermCode (targetLeftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate <;>
      assumption
  have htargetRightTerms : forall coordinate,
      (binaryTermCode (targetRightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate <;>
      assumption
  have hrowTerms : forall coordinate,
      (binaryTermCode (rowTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate <;>
      assumption
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
  have hsourceLeft : (binaryFormulaCode sourceLeftFormula).length <=
      entryCode := by
    simpa only [sourceLeftFormula, entryCode,
      sameRowsEmbeddedEntryFormulaCodeFromTermPolynomial] using
      embeddedSubstitution_code_length_le_sameRowsFixed
        compactFixedWidthEntryDef.val termCode sourceLeftTerms
        hsourceLeftTerms
  have hsourceRight : (binaryFormulaCode sourceRightFormula).length <=
      entryCode := by
    simpa only [sourceRightFormula, entryCode,
      sameRowsEmbeddedEntryFormulaCodeFromTermPolynomial] using
      embeddedSubstitution_code_length_le_sameRowsFixed
        compactFixedWidthEntryDef.val termCode sourceRightTerms
        hsourceRightTerms
  have htargetLeft : (binaryFormulaCode targetLeftFormula).length <=
      entryCode := by
    simpa only [targetLeftFormula, entryCode,
      sameRowsEmbeddedEntryFormulaCodeFromTermPolynomial] using
      embeddedSubstitution_code_length_le_sameRowsFixed
        compactFixedWidthEntryDef.val termCode targetLeftTerms
        htargetLeftTerms
  have htargetRight : (binaryFormulaCode targetRightFormula).length <=
      entryCode := by
    simpa only [targetRightFormula, entryCode,
      sameRowsEmbeddedEntryFormulaCodeFromTermPolynomial] using
      embeddedSubstitution_code_length_le_sameRowsFixed
        compactFixedWidthEntryDef.val termCode targetRightTerms
        htargetRightTerms
  have hrow : (binaryFormulaCode rowFormula).length <= rowCode := by
    simpa only [rowFormula, rowCode,
      sameRowsEmbeddedRowFormulaCodeFromTermPolynomial] using
      embeddedSubstitution_code_length_le_sameRowsFixed
        compactAdditiveAtomicRowEqDef.val termCode rowTerms hrowTerms
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
        sameRowsUniversalTerminalFormulaCodePolynomial bitBound := by
    change
      (binaryFormulaCode
        (sourceLeftFormula ⋏
          (sourceRightFormula ⋏
            (targetLeftFormula ⋏
              (targetRightFormula ⋏ rowFormula))))).length <=
        4 * entryCode + rowCode + 4 * (binaryNatCode 4).length + 1
    omega
  simpa only [compactAdditiveNatListSameRowsTerminal, sourceLeftFormula,
    sourceRightFormula, targetLeftFormula, targetRightFormula, rowFormula,
    sourceLeftTerms, sourceRightTerms, targetLeftTerms, targetRightTerms,
    rowTerms] using hfinal

def sameRowsLeftEntryFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        (&0 : ValuationTerm) numericBound bitBound))

def sameRowsRightEntryFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate
        (‘&0 + 1’ : ValuationTerm) numericBound bitBound))

def sameRowsTerminalContextFormulaCodeSumEnvelope
    (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length

def sameRowsTerminalAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let leftResource :=
    sameRowsLeftEntryFixedPayloadPolynomial numericBound bitBound
  let rightResource :=
    sameRowsRightEntryFixedPayloadPolynomial numericBound bitBound
  let rowResource :=
    compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
  let contextResource :=
    sameRowsTerminalContextFormulaCodeSumEnvelope numericBound
  let conjunctionTag := (binaryNatCode 4).length
  contextResource +
    8 * (leftResource + rightResource + rowResource + conjunctionTag + 1) + 1

def sameRowsTerminalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let leftResource :=
    sameRowsLeftEntryFixedPayloadPolynomial numericBound bitBound
  let rightResource :=
    sameRowsRightEntryFixedPayloadPolynomial numericBound bitBound
  let rowResource :=
    compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    sameRowsTerminalAssemblySyntaxPolynomial numericBound bitBound
  let targetRightRow :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
      rowResource
  let targetLeftTail :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
      targetRightRow
  let sourceRightTail :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
      targetLeftTail
  hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
    sourceRightTail

private theorem valuationContextFormulaCodeSum_le_sameRowsSingleton
    (valuation : Nat -> Nat) {arity : Nat}
    (formula : ArithmeticSemiformula Nat arity)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext formula.freeVariables valuation) <=
      sameRowsTerminalContextFormulaCodeSumEnvelope numericBound := by
  have hcard : formula.freeVariables.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall index, index ∈ formula.freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact hvaluation
  have htermCodes : forall index, index ∈ formula.freeVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact le_rfl
  have hraw := valuationContext_formulaCodeSum_le_uniform
    formula.freeVariables valuation 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues htermCodes
  simpa only [
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum,
    formulaCodeSum, sameRowsTerminalContextFormulaCodeSumEnvelope] using hraw

private theorem fixedWidthEntryCertificate_payload_and_code_le_sameRowsFixed
    (valuation : Nat -> Nat) (table width value : Nat)
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry table width
      (termValue valuation indexTerm) value) :
    let certificate :=
      compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        indexTerm (shortBinaryNumeralTerm value) (by
          simpa only [termValue_shortBinaryNumeralTerm] using hentry)
    let resource :=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
          (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
            numericBound bitBound))
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm width) indexTerm
          (shortBinaryNumeralTerm value) <= resource ∧
      hybridFormulaStructuralPayloadBound certificate <= resource ∧
      (binaryFormulaCode
        (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
          indexTerm (shortBinaryNumeralTerm value))).length <= resource := by
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      indexTerm (shortBinaryNumeralTerm value) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hentry)
  let resource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
      (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
        (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
          numericBound bitBound))
  have hrawResource :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm table)
            (shortBinaryNumeralTerm width) indexTerm
            (shortBinaryNumeralTerm value) <= resource := by
    dsimp only [resource]
    exact
      compactFixedWidthEntryAtValuationOpenIndexAtIndexTermShortNumeralsStructuralPayloadPolynomial_le_uniform
        valuation table width value indexTerm numericBound bitBound
        hwidthValue hindexValue hvaluation htableSize hwidthSize hindexSize
        hvalueSize hindex
  have hpayload :
      hybridFormulaStructuralPayloadBound certificate <= resource := by
    dsimp only [certificate, resource]
    exact
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        valuation table width value indexTerm numericBound bitBound
        hwidthValue hindexValue hvaluation htableSize hwidthSize hindexSize
        hvalueSize hindex hentry
  have hcodeRaw :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate
  have hcode :
      (binaryFormulaCode
        (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
          indexTerm (shortBinaryNumeralTerm value))).length <= resource := by
    simpa only [certificate] using hcodeRaw.trans hpayload
  exact ⟨hrawResource, hpayload, hcode⟩

private theorem atomicRowCertificate_payload_and_code_le_sameRowsFixed
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount left right otherLeft otherRight
      numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hleft : left <= numericBound)
    (hright : right <= numericBound)
    (hotherLeft : otherLeft <= numericBound)
    (hotherRight : otherRight <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hgraph : CompactAdditiveAtomicRowEq tokenTable width tokenCount left
      right otherLeft otherRight) :
    let certificate :=
      compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm left)
        (shortBinaryNumeralTerm right) (shortBinaryNumeralTerm otherLeft)
        (shortBinaryNumeralTerm otherRight) (by
          simpa only [termValue_shortBinaryNumeralTerm] using hgraph)
    let resource :=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm left)
        (shortBinaryNumeralTerm right) (shortBinaryNumeralTerm otherLeft)
        (shortBinaryNumeralTerm otherRight) <= resource ∧
      hybridFormulaStructuralPayloadBound certificate <= resource ∧
      (binaryFormulaCode
        (compactAdditiveAtomicRowEqAtValuationFormula
          (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm right) (shortBinaryNumeralTerm otherLeft)
          (shortBinaryNumeralTerm otherRight))).length <= resource := by
  let certificate :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm left)
      (shortBinaryNumeralTerm right) (shortBinaryNumeralTerm otherLeft)
      (shortBinaryNumeralTerm otherRight) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hgraph)
  let resource :=
    compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
  have htransparent :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_of_closed
      valuation (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
      (shortBinaryNumeralTerm otherLeft) (shortBinaryNumeralTerm otherRight)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width)
      (shortBinaryNumeralTerm_freeVariables_eq_empty left)
      (shortBinaryNumeralTerm_freeVariables_eq_empty otherLeft)
      (by simpa only [termValue_shortBinaryNumeralTerm] using hgraph)
  have hfixed :=
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope_le_fixed
      valuation tokenTable width tokenCount left right otherLeft otherRight
      numericBound bitBound hwidth htokenCount hleft hright hotherLeft
      hotherRight htableSize hnumericSize
  have hpayload :
      hybridFormulaStructuralPayloadBound certificate <= resource := by
    simpa only [certificate, resource] using htransparent.trans hfixed
  have hcodeRaw :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate
  have hcode :
      (binaryFormulaCode
        (compactAdditiveAtomicRowEqAtValuationFormula
          (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm left)
          (shortBinaryNumeralTerm right) (shortBinaryNumeralTerm otherLeft)
          (shortBinaryNumeralTerm otherRight))).length <= resource := by
    simpa only [certificate] using hcodeRaw.trans hpayload
  exact ⟨hfixed, hpayload, hcode⟩

private theorem fiveLeafTransparentConjunctionEnvelope_le_general
    (valuation : Nat -> Nat)
    (first second third fourth fifth : ValuationFormula)
    (firstSmall secondSmall thirdSmall fourthSmall fifthSmall : Nat)
    (leftResource rightResource rowResource syntaxResource : Nat)
    (hfirst : firstSmall <= leftResource)
    (hsecond : secondSmall <= rightResource)
    (hthird : thirdSmall <= leftResource)
    (hfourth : fourthSmall <= rightResource)
    (hfifth : fifthSmall <= rowResource)
    (hsyntaxOne : 1 <= syntaxResource)
    (hcontext45 :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (fourth ⋏ fifth).freeVariables valuation) <=
        syntaxResource)
    (hcontext345 :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (third ⋏ (fourth ⋏ fifth)).freeVariables
            valuation) <= syntaxResource)
    (hcontext2345 :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext
            (second ⋏ (third ⋏ (fourth ⋏ fifth))).freeVariables valuation) <=
        syntaxResource)
    (hcontext12345 :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext
            (first ⋏ (second ⋏ (third ⋏ (fourth ⋏ fifth)))).freeVariables
            valuation) <= syntaxResource)
    (hfirstCode : (binaryFormulaCode first).length <= syntaxResource)
    (hsecondCode : (binaryFormulaCode second).length <= syntaxResource)
    (hthirdCode : (binaryFormulaCode third).length <= syntaxResource)
    (hfourthCode : (binaryFormulaCode fourth).length <= syntaxResource)
    (hfifthCode : (binaryFormulaCode fifth).length <= syntaxResource)
    (hcode45 : (binaryFormulaCode (fourth ⋏ fifth)).length <= syntaxResource)
    (hcode345 :
      (binaryFormulaCode (third ⋏ (fourth ⋏ fifth))).length <= syntaxResource)
    (hcode2345 :
      (binaryFormulaCode
        (second ⋏ (third ⋏ (fourth ⋏ fifth)))).length <= syntaxResource)
    (hcode12345 :
      (binaryFormulaCode
        (first ⋏ (second ⋏ (third ⋏ (fourth ⋏ fifth))))).length <=
          syntaxResource) :
    transparentHybridConjunctionPayloadEnvelope valuation first
        (second ⋏ (third ⋏ (fourth ⋏ fifth))) firstSmall
        (transparentHybridConjunctionPayloadEnvelope valuation second
          (third ⋏ (fourth ⋏ fifth)) secondSmall
          (transparentHybridConjunctionPayloadEnvelope valuation third
            (fourth ⋏ fifth) thirdSmall
            (transparentHybridConjunctionPayloadEnvelope valuation fourth
              fifth fourthSmall fifthSmall))) <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
            (hybridConjunctionGeneralPayloadEnvelope syntaxResource
              rightResource rowResource))) := by
  let resource45 :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
      rowResource
  let resource345 :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
      resource45
  let resource2345 :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
      resource345
  have hmono45 :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation fourth fifth
      hfourth hfifth
  have hgeneral45 :
      transparentHybridConjunctionPayloadEnvelope valuation fourth fifth
          rightResource rowResource <= resource45 := by
    have hraw := hybridConjunctionStructuralPayloadEnvelope_le_general
      valuation fourth fifth rightResource rowResource syntaxResource
      hsyntaxOne hcontext45 hfourthCode hfifthCode hcode45
    simpa only [transparentHybridConjunctionPayloadEnvelope,
      hybridConjunctionStructuralPayloadEnvelope, resource45] using hraw
  have hmono345 :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation third
      (fourth ⋏ fifth) hthird (hmono45.trans hgeneral45)
  have hgeneral345 :
      transparentHybridConjunctionPayloadEnvelope valuation third
          (fourth ⋏ fifth) leftResource resource45 <= resource345 := by
    have hraw := hybridConjunctionStructuralPayloadEnvelope_le_general
      valuation third (fourth ⋏ fifth) leftResource resource45 syntaxResource
      hsyntaxOne hcontext345 hthirdCode hcode45 hcode345
    simpa only [transparentHybridConjunctionPayloadEnvelope,
      hybridConjunctionStructuralPayloadEnvelope, resource345] using hraw
  have hmono2345 :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation second
      (third ⋏ (fourth ⋏ fifth)) hsecond
      (hmono345.trans hgeneral345)
  have hgeneral2345 :
      transparentHybridConjunctionPayloadEnvelope valuation second
          (third ⋏ (fourth ⋏ fifth)) rightResource resource345 <=
        resource2345 := by
    have hraw := hybridConjunctionStructuralPayloadEnvelope_le_general
      valuation second (third ⋏ (fourth ⋏ fifth)) rightResource resource345
      syntaxResource hsyntaxOne hcontext2345 hsecondCode hcode345 hcode2345
    simpa only [transparentHybridConjunctionPayloadEnvelope,
      hybridConjunctionStructuralPayloadEnvelope, resource2345] using hraw
  have hmono12345 :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation first
      (second ⋏ (third ⋏ (fourth ⋏ fifth))) hfirst
      (hmono2345.trans hgeneral2345)
  have hgeneral12345 :
      transparentHybridConjunctionPayloadEnvelope valuation first
          (second ⋏ (third ⋏ (fourth ⋏ fifth))) leftResource resource2345 <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
          resource2345 := by
    have hraw := hybridConjunctionStructuralPayloadEnvelope_le_general
      valuation first (second ⋏ (third ⋏ (fourth ⋏ fifth))) leftResource
      resource2345 syntaxResource hsyntaxOne hcontext12345 hfirstCode
      hcode2345 hcode12345
    simpa only [transparentHybridConjunctionPayloadEnvelope,
      hybridConjunctionStructuralPayloadEnvelope] using hraw
  simpa only [resource45, resource345, resource2345] using
    hmono12345.trans hgeneral12345

theorem
    compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound : Nat)
    (data : CompactAdditiveNatListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope tokenTable
        width tokenCount sourceBoundary targetBoundary index data <=
      sameRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound := by
  let valuation := extendValuation index sameRowsZeroValuationFixed
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let sourceIndexTerm : ValuationTerm := &0
  let nextIndexTerm : ValuationTerm := ‘&0 + 1’
  let sourceLeftTerm := shortBinaryNumeralTerm data.sourceLeft
  let sourceRightTerm := shortBinaryNumeralTerm data.sourceRight
  let targetLeftTerm := shortBinaryNumeralTerm data.targetLeft
  let targetRightTerm := shortBinaryNumeralTerm data.targetRight
  let sourceLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary) widthTerm sourceIndexTerm
    sourceLeftTerm
  let sourceRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary) widthTerm nextIndexTerm
    sourceRightTerm
  let targetLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary) widthTerm sourceIndexTerm
    targetLeftTerm
  let targetRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary) widthTerm nextIndexTerm
    targetRightTerm
  let rowFormula := compactAdditiveAtomicRowEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    widthTerm sourceLeftTerm sourceRightTerm targetLeftTerm targetRightTerm
  let targetRightRowFormula := targetRightFormula ⋏ rowFormula
  let targetLeftTailFormula := targetLeftFormula ⋏ targetRightRowFormula
  let sourceRightTailFormula :=
    sourceRightFormula ⋏ targetLeftTailFormula
  let leftResource :=
    sameRowsLeftEntryFixedPayloadPolynomial numericBound bitBound
  let rightResource :=
    sameRowsRightEntryFixedPayloadPolynomial numericBound bitBound
  let rowResource :=
    compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    sameRowsTerminalAssemblySyntaxPolynomial numericBound bitBound
  let targetRightRowResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
      rowResource
  let targetLeftTailResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
      targetRightRowResource
  let sourceRightTailResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource rightResource
      targetLeftTailResource
  have hindex : index <= numericBound := by omega
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hindexSize : Nat.size index <= bitBound :=
    (Nat.size_le_size hindex).trans hnumericSize
  have hindexSuccessorSize : Nat.size (index + 1) <= bitBound :=
    (Nat.size_le_size hindexSuccessor).trans hnumericSize
  have hsourceLeftBound : data.sourceLeft <= numericBound :=
    data.sourceLeft_le.trans htokenCount
  have hsourceRightBound : data.sourceRight <= numericBound :=
    data.sourceRight_le.trans htokenCount
  have htargetLeftBound : data.targetLeft <= numericBound :=
    data.targetLeft_le.trans htokenCount
  have htargetRightBound : data.targetRight <= numericBound :=
    data.targetRight_le.trans htokenCount
  have hsourceLeftSize : Nat.size data.sourceLeft <= bitBound :=
    (Nat.size_le_size hsourceLeftBound).trans hnumericSize
  have hsourceRightSize : Nat.size data.sourceRight <= bitBound :=
    (Nat.size_le_size hsourceRightBound).trans hnumericSize
  have htargetLeftSize : Nat.size data.targetLeft <= bitBound :=
    (Nat.size_le_size htargetLeftBound).trans hnumericSize
  have htargetRightSize : Nat.size data.targetRight <= bitBound :=
    (Nat.size_le_size htargetRightBound).trans hnumericSize
  have hzeroValuation : sameRowsZeroValuationFixed =
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation := by
    funext coordinate
    simp [sameRowsZeroValuationFixed,
      FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate.zeroValuation,
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
  have hsourceIndexEvaluation :
      termValue valuation sourceIndexTerm = index := by
    change termValue (extendValuation index sameRowsZeroValuationFixed)
      (&0 : ValuationTerm) = index
    rw [hzeroValuation]
    exact termValue_indexTerm_bvarZero_under_extendValuation index
  have hnextIndexEvaluation :
      termValue valuation nextIndexTerm = index + 1 := by
    change termValue (extendValuation index sameRowsZeroValuationFixed)
      (‘&0 + 1’ : ValuationTerm) = index + 1
    rw [hzeroValuation]
    exact termValue_indexTerm_bvarZeroAddOne_under_extendValuation index
  have hvaluation : valuation 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  have hsourceIndexValue :
      termValue valuation sourceIndexTerm <= numericBound := by
    simpa only [hsourceIndexEvaluation] using hindex
  have hnextIndexValue :
      termValue valuation nextIndexTerm <= numericBound := by
    simpa only [hnextIndexEvaluation] using hindexSuccessor
  have hsourceIndexSize :
      Nat.size (termValue valuation sourceIndexTerm) <= bitBound := by
    simpa only [hsourceIndexEvaluation] using hindexSize
  have hnextIndexSize :
      Nat.size (termValue valuation nextIndexTerm) <= bitBound := by
    simpa only [hnextIndexEvaluation] using hindexSuccessorSize
  have hsourceIndexVariables : sourceIndexTerm.freeVariables ⊆ {0} := by
    simp [sourceIndexTerm]
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables_sameRowsFixed,
      arithmeticOneTerm_freeVariables_sameRowsFixed]
    simp
  have hsourceLeftEntry :
      CompactFixedWidthEntry sourceBoundary tokenCount
        (termValue valuation sourceIndexTerm) data.sourceLeft := by
    simpa only [hsourceIndexEvaluation] using data.sourceLeft_entry
  have hsourceRightEntry :
      CompactFixedWidthEntry sourceBoundary tokenCount
        (termValue valuation nextIndexTerm) data.sourceRight := by
    simpa only [hnextIndexEvaluation] using data.sourceRight_entry
  have htargetLeftEntry :
      CompactFixedWidthEntry targetBoundary tokenCount
        (termValue valuation sourceIndexTerm) data.targetLeft := by
    simpa only [hsourceIndexEvaluation] using data.targetLeft_entry
  have htargetRightEntry :
      CompactFixedWidthEntry targetBoundary tokenCount
        (termValue valuation nextIndexTerm) data.targetRight := by
    simpa only [hnextIndexEvaluation] using data.targetRight_entry
  rcases fixedWidthEntryCertificate_payload_and_code_le_sameRowsFixed
      valuation sourceBoundary tokenCount data.sourceLeft sourceIndexTerm
      numericBound bitBound htokenCount hsourceIndexValue hvaluation
      hsourceBoundarySize htokenCountSize hsourceIndexSize hsourceLeftSize
      hsourceIndexVariables hsourceLeftEntry with
    ⟨hsourceLeftResource, _, hsourceLeftCode⟩
  rcases fixedWidthEntryCertificate_payload_and_code_le_sameRowsFixed
      valuation sourceBoundary tokenCount data.sourceRight nextIndexTerm
      numericBound bitBound htokenCount hnextIndexValue hvaluation
      hsourceBoundarySize htokenCountSize hnextIndexSize hsourceRightSize
      hnextIndexVariables hsourceRightEntry with
    ⟨hsourceRightResource, _, hsourceRightCode⟩
  rcases fixedWidthEntryCertificate_payload_and_code_le_sameRowsFixed
      valuation targetBoundary tokenCount data.targetLeft sourceIndexTerm
      numericBound bitBound htokenCount hsourceIndexValue hvaluation
      htargetBoundarySize htokenCountSize hsourceIndexSize htargetLeftSize
      hsourceIndexVariables htargetLeftEntry with
    ⟨htargetLeftResource, _, htargetLeftCode⟩
  rcases fixedWidthEntryCertificate_payload_and_code_le_sameRowsFixed
      valuation targetBoundary tokenCount data.targetRight nextIndexTerm
      numericBound bitBound htokenCount hnextIndexValue hvaluation
      htargetBoundarySize htokenCountSize hnextIndexSize htargetRightSize
      hnextIndexVariables htargetRightEntry with
    ⟨htargetRightResource, _, htargetRightCode⟩
  rcases atomicRowCertificate_payload_and_code_le_sameRowsFixed valuation
      tokenTable width tokenCount data.sourceLeft data.sourceRight
      data.targetLeft data.targetRight numericBound bitBound hwidth htokenCount
      hsourceLeftBound hsourceRightBound htargetLeftBound htargetRightBound
      htokenTableSize hnumericSize data.row_eq with
    ⟨hrowResource, _, hrowCode⟩
  have hsourceLeftVariables : sourceLeftFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      (shortBinaryNumeralTerm sourceBoundary) widthTerm sourceIndexTerm
      sourceLeftTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty sourceBoundary)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      hsourceIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty data.sourceLeft)
  have hsourceRightVariables : sourceRightFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      (shortBinaryNumeralTerm sourceBoundary) widthTerm nextIndexTerm
      sourceRightTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty sourceBoundary)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      hnextIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty data.sourceRight)
  have htargetLeftVariables : targetLeftFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      (shortBinaryNumeralTerm targetBoundary) widthTerm sourceIndexTerm
      targetLeftTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      hsourceIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty data.targetLeft)
  have htargetRightVariables : targetRightFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      (shortBinaryNumeralTerm targetBoundary) widthTerm nextIndexTerm
      targetRightTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty targetBoundary)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      hnextIndexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty data.targetRight)
  have hrowClosed : rowFormula.freeVariables = ∅ := by
    dsimp only [rowFormula]
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      apply shortBinaryNumeralTerm_freeVariables_eq_empty
  have hrowVariables : rowFormula.freeVariables ⊆ {0} := by
    rw [hrowClosed]
    exact Finset.empty_subset _
  have htargetRightRowVariables :
      targetRightRowFormula.freeVariables ⊆ {0} := by
    dsimp only [targetRightRowFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset htargetRightVariables hrowVariables
  have htargetLeftTailVariables :
      targetLeftTailFormula.freeVariables ⊆ {0} := by
    dsimp only [targetLeftTailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset htargetLeftVariables htargetRightRowVariables
  have hsourceRightTailVariables :
      sourceRightTailFormula.freeVariables ⊆ {0} := by
    dsimp only [sourceRightTailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hsourceRightVariables htargetLeftTailVariables
  have htotalVariables :
      (sourceLeftFormula ⋏ sourceRightTailFormula).freeVariables ⊆ {0} := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hsourceLeftVariables hsourceRightTailVariables
  have hsourceLeftCodeLocal :
      (binaryFormulaCode sourceLeftFormula).length <= leftResource := by
    simpa only [sourceLeftFormula, widthTerm, sourceIndexTerm,
      sourceLeftTerm, leftResource,
      sameRowsLeftEntryFixedPayloadPolynomial] using hsourceLeftCode
  have hsourceRightCodeLocal :
      (binaryFormulaCode sourceRightFormula).length <= rightResource := by
    simpa only [sourceRightFormula, widthTerm, nextIndexTerm,
      sourceRightTerm, rightResource,
      sameRowsRightEntryFixedPayloadPolynomial] using hsourceRightCode
  have htargetLeftCodeLocal :
      (binaryFormulaCode targetLeftFormula).length <= leftResource := by
    simpa only [targetLeftFormula, widthTerm, sourceIndexTerm,
      targetLeftTerm, leftResource,
      sameRowsLeftEntryFixedPayloadPolynomial] using htargetLeftCode
  have htargetRightCodeLocal :
      (binaryFormulaCode targetRightFormula).length <= rightResource := by
    simpa only [targetRightFormula, widthTerm, nextIndexTerm,
      targetRightTerm, rightResource,
      sameRowsRightEntryFixedPayloadPolynomial] using htargetRightCode
  have hrowCodeLocal :
      (binaryFormulaCode rowFormula).length <= rowResource := by
    simpa only [rowFormula, widthTerm, sourceLeftTerm, sourceRightTerm,
      targetLeftTerm, targetRightTerm, rowResource] using hrowCode
  have htargetRightRowCodeRaw :=
    binaryFormulaCode_and_length_le_local targetRightFormula rowFormula
  have htargetRightRowCode :
      (binaryFormulaCode targetRightRowFormula).length <=
        rightResource + rowResource + (binaryNatCode 4).length := by
    dsimp only [targetRightRowFormula] at htargetRightRowCodeRaw ⊢
    omega
  have htargetLeftTailCodeRaw :=
    binaryFormulaCode_and_length_le_local targetLeftFormula
      targetRightRowFormula
  have htargetLeftTailCode :
      (binaryFormulaCode targetLeftTailFormula).length <=
        leftResource + rightResource + rowResource +
          2 * (binaryNatCode 4).length := by
    dsimp only [targetLeftTailFormula] at htargetLeftTailCodeRaw ⊢
    omega
  have hsourceRightTailCodeRaw :=
    binaryFormulaCode_and_length_le_local sourceRightFormula
      targetLeftTailFormula
  have hsourceRightTailCode :
      (binaryFormulaCode sourceRightTailFormula).length <=
        leftResource + 2 * rightResource + rowResource +
          3 * (binaryNatCode 4).length := by
    dsimp only [sourceRightTailFormula] at hsourceRightTailCodeRaw ⊢
    omega
  have htotalCodeRaw :=
    binaryFormulaCode_and_length_le_local sourceLeftFormula
      sourceRightTailFormula
  have htotalCode :
      (binaryFormulaCode
        (sourceLeftFormula ⋏ sourceRightTailFormula)).length <=
        2 * leftResource + 2 * rightResource + rowResource +
          4 * (binaryNatCode 4).length := by
    omega
  have hsyntaxOne : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold sameRowsTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hcontext_le_syntax :
      sameRowsTerminalContextFormulaCodeSumEnvelope numericBound <=
        syntaxResource := by
    dsimp only [syntaxResource]
    unfold sameRowsTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hleft_le_syntax : leftResource <= syntaxResource := by
    dsimp only [leftResource, syntaxResource]
    unfold sameRowsTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hright_le_syntax : rightResource <= syntaxResource := by
    dsimp only [rightResource, syntaxResource]
    unfold sameRowsTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have hrow_le_syntax : rowResource <= syntaxResource := by
    dsimp only [rowResource, syntaxResource]
    unfold sameRowsTerminalAssemblySyntaxPolynomial
    dsimp only
    omega
  have htargetRightRowCodeSyntax :
      (binaryFormulaCode targetRightRowFormula).length <= syntaxResource :=
    htargetRightRowCode.trans (by
      dsimp only [leftResource, rightResource, rowResource, syntaxResource]
      unfold sameRowsTerminalAssemblySyntaxPolynomial
      dsimp only
      omega)
  have htargetLeftTailCodeSyntax :
      (binaryFormulaCode targetLeftTailFormula).length <= syntaxResource :=
    htargetLeftTailCode.trans (by
      dsimp only [leftResource, rightResource, rowResource, syntaxResource]
      unfold sameRowsTerminalAssemblySyntaxPolynomial
      dsimp only
      omega)
  have hsourceRightTailCodeSyntax :
      (binaryFormulaCode sourceRightTailFormula).length <= syntaxResource :=
    hsourceRightTailCode.trans (by
      dsimp only [leftResource, rightResource, rowResource, syntaxResource]
      unfold sameRowsTerminalAssemblySyntaxPolynomial
      dsimp only
      omega)
  have htotalCodeSyntax :
      (binaryFormulaCode
        (sourceLeftFormula ⋏ sourceRightTailFormula)).length <=
          syntaxResource :=
    htotalCode.trans (by
      dsimp only [leftResource, rightResource, rowResource, syntaxResource]
      unfold sameRowsTerminalAssemblySyntaxPolynomial
      dsimp only
      omega)
  have hsourceLeftCodeSyntax :
      (binaryFormulaCode sourceLeftFormula).length <= syntaxResource := by
    exact hsourceLeftCodeLocal.trans hleft_le_syntax
  have hsourceRightCodeSyntax :
      (binaryFormulaCode sourceRightFormula).length <= syntaxResource := by
    exact hsourceRightCodeLocal.trans hright_le_syntax
  have htargetLeftCodeSyntax :
      (binaryFormulaCode targetLeftFormula).length <= syntaxResource := by
    exact htargetLeftCodeLocal.trans hleft_le_syntax
  have htargetRightCodeSyntax :
      (binaryFormulaCode targetRightFormula).length <= syntaxResource := by
    exact htargetRightCodeLocal.trans hright_le_syntax
  have hrowCodeSyntax :
      (binaryFormulaCode rowFormula).length <= syntaxResource := by
    exact hrowCodeLocal.trans hrow_le_syntax
  have htargetRightRowContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext targetRightRowFormula.freeVariables valuation) <=
        syntaxResource :=
    (valuationContextFormulaCodeSum_le_sameRowsSingleton valuation
      targetRightRowFormula numericBound htargetRightRowVariables
      hvaluation).trans hcontext_le_syntax
  have htargetLeftTailContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext targetLeftTailFormula.freeVariables valuation) <=
        syntaxResource :=
    (valuationContextFormulaCodeSum_le_sameRowsSingleton valuation
      targetLeftTailFormula numericBound htargetLeftTailVariables
      hvaluation).trans hcontext_le_syntax
  have hsourceRightTailContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext sourceRightTailFormula.freeVariables valuation) <=
        syntaxResource :=
    (valuationContextFormulaCodeSum_le_sameRowsSingleton valuation
      sourceRightTailFormula numericBound hsourceRightTailVariables
      hvaluation).trans hcontext_le_syntax
  have htotalContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext
            (sourceLeftFormula ⋏ sourceRightTailFormula).freeVariables
            valuation) <= syntaxResource :=
    (valuationContextFormulaCodeSum_le_sameRowsSingleton valuation
      (sourceLeftFormula ⋏ sourceRightTailFormula) numericBound
      htotalVariables hvaluation).trans hcontext_le_syntax
  have hassembly :=
    fiveLeafTransparentConjunctionEnvelope_le_general valuation
      sourceLeftFormula sourceRightFormula targetLeftFormula
      targetRightFormula rowFormula
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm sourceBoundary) widthTerm
          sourceIndexTerm sourceLeftTerm)
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm sourceBoundary) widthTerm
          nextIndexTerm sourceRightTerm)
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
          sourceIndexTerm targetLeftTerm)
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm targetBoundary) widthTerm
          nextIndexTerm targetRightTerm)
      (compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        widthTerm sourceLeftTerm sourceRightTerm targetLeftTerm
          targetRightTerm)
      leftResource rightResource rowResource syntaxResource
      hsourceLeftResource hsourceRightResource htargetLeftResource
      htargetRightResource hrowResource hsyntaxOne htargetRightRowContext
      htargetLeftTailContext hsourceRightTailContext htotalContext
      hsourceLeftCodeSyntax hsourceRightCodeSyntax htargetLeftCodeSyntax
      htargetRightCodeSyntax hrowCodeSyntax htargetRightRowCodeSyntax
      htargetLeftTailCodeSyntax hsourceRightTailCodeSyntax htotalCodeSyntax
  unfold compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope
  dsimp only [valuation, widthTerm, sourceIndexTerm, nextIndexTerm,
    sourceLeftTerm, sourceRightTerm, targetLeftTerm, targetRightTerm,
    sourceLeftFormula, sourceRightFormula, targetLeftFormula,
    targetRightFormula, rowFormula, targetRightRowFormula,
    targetLeftTailFormula, sourceRightTailFormula]
  simpa only [sameRowsTerminalFullyFixedPayloadPolynomial, leftResource,
    rightResource, rowResource, syntaxResource, targetRightRowResource,
    targetLeftTailResource, sourceRightTailResource] using hassembly

def compactAdditiveNatListSameRowsWitnessPrefixFixedEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      terminalResource : Nat) : Nat :=
  let valuation := extendValuation index sameRowsZeroValuationFixed
  let body :=
    compactAdditiveNatListSameRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
    (formulaCodeSum (valuationContext body.freeVariables valuation))
    tokenCount (binaryFormulaCode body).length terminalResource

theorem
    compactAdditiveNatListSameRowsBranchEnvelope_le_witnessPrefixFixed
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope tokenTable
        width tokenCount sourceBoundary targetBoundary index data <=
      compactAdditiveNatListSameRowsWitnessPrefixFixedEnvelope tokenTable width
        tokenCount sourceBoundary targetBoundary index
        (compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary index
          data) := by
  let valuation := extendValuation index sameRowsZeroValuationFixed
  let body :=
    compactAdditiveNatListSameRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact data.targetRight_le
    · exact data.targetLeft_le
    · exact data.sourceRight_le
    · exact data.sourceLeft_le
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity04
      (terminalSmall :=
        compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary index data)
      (terminalLarge :=
        compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary index data)
      valuation
      (formulaCodeSum (valuationContext body.freeVariables valuation))
      tokenCount tokenCount (binaryFormulaCode body).length body values
      hvalues (Nat.le_refl tokenCount) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _)
  simpa only [compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope,
    compactAdditiveNatListSameRowsWitnessPrefixFixedEnvelope, valuation, body,
    values, sameRowsZeroValuationFixed] using hfixed

theorem compactAdditiveNatListSameRowsWitnessPrefixFixedEnvelope_mono_terminal
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    {terminalSmall terminalLarge : Nat}
    (hterminal : terminalSmall <= terminalLarge) :
    compactAdditiveNatListSameRowsWitnessPrefixFixedEnvelope tokenTable width
        tokenCount sourceBoundary targetBoundary index terminalSmall <=
      compactAdditiveNatListSameRowsWitnessPrefixFixedEnvelope tokenTable width
        tokenCount sourceBoundary targetBoundary index terminalLarge := by
  unfold compactAdditiveNatListSameRowsWitnessPrefixFixedEnvelope
    explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
  dsimp only
  omega

def compactAdditiveNatListSameRowsBranchFullyFixedEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound : Nat) : Nat :=
  compactAdditiveNatListSameRowsWitnessPrefixFixedEnvelope tokenTable width
    tokenCount sourceBoundary targetBoundary index
    (sameRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound)

theorem
    compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound : Nat)
    (data : CompactAdditiveNatListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope tokenTable
        width tokenCount sourceBoundary targetBoundary index data <=
      compactAdditiveNatListSameRowsBranchFullyFixedEnvelope tokenTable width
        tokenCount sourceBoundary targetBoundary index numericBound
        bitBound := by
  exact
    (compactAdditiveNatListSameRowsBranchEnvelope_le_witnessPrefixFixed
      tokenTable width tokenCount sourceBoundary targetBoundary index
      data).trans
      ((compactAdditiveNatListSameRowsWitnessPrefixFixedEnvelope_mono_terminal
        tokenTable width tokenCount sourceBoundary targetBoundary index)
        (compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope_le_fullyFixed
          tokenTable width tokenCount sourceBoundary targetBoundary index
          numericBound bitBound data hwidth htokenCount hindexSuccessor
          htokenTableSize hsourceBoundarySize htargetBoundarySize
          hnumericSize))

def compactAdditiveNatListSameRowsUniformBranchPayloadPolynomial
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat) : Nat :=
  let body :=
    compactAdditiveNatListSameRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
    (sameRowsTerminalContextFormulaCodeSumEnvelope numericBound)
    tokenCount (binaryFormulaCode body).length
    (sameRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound)

theorem
    compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope_le_uniform
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound : Nat)
    (data : CompactAdditiveNatListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope tokenTable
        width tokenCount sourceBoundary targetBoundary index data <=
      compactAdditiveNatListSameRowsUniformBranchPayloadPolynomial tokenTable
        width tokenCount sourceBoundary targetBoundary numericBound
        bitBound := by
  let valuation := extendValuation index sameRowsZeroValuationFixed
  let body :=
    compactAdditiveNatListSameRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary
  have hindex : index <= numericBound := by omega
  have hvaluation : valuation 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  have hcontext :
      formulaCodeSum (valuationContext body.freeVariables valuation) <=
        sameRowsTerminalContextFormulaCodeSumEnvelope numericBound := by
    exact valuationContextFormulaCodeSum_le_sameRowsSingleton valuation body
      numericBound
      (compactAdditiveNatListSameRowsBranchTerminal_freeVariables_subset_singleton
        tokenTable width tokenCount sourceBoundary targetBoundary)
      hvaluation
  have hbase :=
    compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound data hwidth htokenCount hindexSuccessor
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hmono :=
    explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04_mono_context
      (numericBound := tokenCount)
      (bodyCodeBound := (binaryFormulaCode body).length)
      (terminalResource :=
        sameRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound)
      hcontext
  exact hbase.trans (by
    simpa only [compactAdditiveNatListSameRowsBranchFullyFixedEnvelope,
      compactAdditiveNatListSameRowsWitnessPrefixFixedEnvelope,
      compactAdditiveNatListSameRowsUniformBranchPayloadPolynomial, valuation,
      body, sameRowsZeroValuationFixed] using hmono)

def compactAdditiveNatListSameRowsUniformBranchSumPayloadPolynomial
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat) : Nat :=
  sourceCount *
    compactAdditiveNatListSameRowsUniformBranchPayloadPolynomial tokenTable
      width tokenCount sourceBoundary targetBoundary numericBound bitBound

theorem compactAdditiveNatListSameRowsBranchPayloadResourceSum_le_uniform
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListSameRowsBranchPayloadResourceSum tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows <=
      compactAdditiveNatListSameRowsUniformBranchSumPayloadPolynomial
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound := by
  let resource :=
    compactAdditiveNatListSameRowsUniformBranchPayloadPolynomial tokenTable
      width tokenCount sourceBoundary targetBoundary numericBound bitBound
  have hsum :
      (∑ index : Fin sourceCount,
        compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope tokenTable
          width tokenCount sourceBoundary targetBoundary index
          (rows index)) <=
        ∑ _index : Fin sourceCount, resource := by
    apply Finset.sum_le_sum
    intro index _
    have hindexSuccessor : index.val + 1 <= numericBound := by
      exact (Nat.succ_le_of_lt index.isLt).trans hsourceCount
    exact
      compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope_le_uniform
        tokenTable width tokenCount sourceBoundary targetBoundary index
        numericBound bitBound (rows index) hwidth htokenCount hindexSuccessor
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  unfold compactAdditiveNatListSameRowsBranchPayloadResourceSum
    compactAdditiveNatListSameRowsUniformBranchSumPayloadPolynomial
  simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul, resource] using hsum

private theorem
    hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf_sameRowsFixed
    (totalBound : Nat) (outerVariables : Finset Nat)
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    {small large : Nat} (hresource : small <= large) :
    forall bound,
      hybridBranchesUniformStructuralPayloadEnvelope totalBound outerVariables
          valuation body small bound <=
        hybridBranchesUniformStructuralPayloadEnvelope totalBound
          outerVariables valuation body large bound
  | 0 => by rfl
  | bound + 1 => by
      simp only [hybridBranchesUniformStructuralPayloadEnvelope]
      have hinduction :=
        hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf_sameRowsFixed
          totalBound outerVariables valuation body hresource bound
      omega

def compactAdditiveNatListSameRowsBranchesFixedPayloadPolynomial
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat) : Nat :=
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue sameRowsZeroValuationFixed
    (shortBinaryNumeralTerm sourceCount)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    sameRowsZeroValuationFixed body
    (compactAdditiveNatListSameRowsUniformBranchSumPayloadPolynomial
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound)
    bound

theorem
    compactAdditiveNatListSameRowsBranchesTransparentEnvelope_le_fixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListSameRowsBranchesTransparentEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows <=
      compactAdditiveNatListSameRowsBranchesFixedPayloadPolynomial tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary numericBound
        bitBound := by
  unfold compactAdditiveNatListSameRowsBranchesTransparentEnvelope
    compactAdditiveNatListSameRowsBranchesFixedPayloadPolynomial
  exact
    hybridBranchesUniformStructuralPayloadEnvelope_mono_leaf_sameRowsFixed
      (termValue sameRowsZeroValuationFixed
        (shortBinaryNumeralTerm sourceCount))
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm sourceCount))
        (compactAdditiveNatListSameRowsBody tokenTable width tokenCount
          sourceBoundary targetBoundary)).freeVariables
      sameRowsZeroValuationFixed
      (compactAdditiveNatListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary)
      (compactAdditiveNatListSameRowsBranchPayloadResourceSum_le_uniform
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound rows hwidth htokenCount hsourceCount
        htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize)
      (termValue sameRowsZeroValuationFixed
        (shortBinaryNumeralTerm sourceCount))

def compactAdditiveNatListSameRowsBranchesClosedPayloadPolynomial
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat) : Nat :=
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let Gamma :=
    (valuationContext outerVariables sameRowsZeroValuationFixed).image
      Rewriting.shift
  contextualHybridUniversalBranchesPayloadPolynomial Gamma sourceCount
    sourceCount body
    (compactAdditiveNatListSameRowsUniformBranchSumPayloadPolynomial
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound)

theorem compactAdditiveNatListSameRowsBranchesFixedPayloadPolynomial_le_closed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat) :
    compactAdditiveNatListSameRowsBranchesFixedPayloadPolynomial tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary numericBound
        bitBound <=
      compactAdditiveNatListSameRowsBranchesClosedPayloadPolynomial tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary numericBound
        bitBound := by
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  have houterVariables : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact
      compactAdditiveNatListSameRowsOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
  have hGammaCard :
      ((valuationContext outerVariables sameRowsZeroValuationFixed).image
        Rewriting.shift).card <= 1 := by
    rw [houterVariables]
    simp [valuationContext]
  have hraw :=
    hybridBranchesUniformStructuralPayloadEnvelope_le_contextualPolynomial
      sourceCount outerVariables sameRowsZeroValuationFixed body
      (compactAdditiveNatListSameRowsUniformBranchSumPayloadPolynomial
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound)
      hGammaCard (caseCount := sourceCount) le_rfl
  simpa only [
    compactAdditiveNatListSameRowsBranchesFixedPayloadPolynomial,
    compactAdditiveNatListSameRowsBranchesClosedPayloadPolynomial,
    termValue_shortBinaryNumeralTerm, body, outerFormula, outerVariables,
    sameRowsZeroValuationFixed] using hraw

def compactAdditiveNatListSameRowsFixedUniversalPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat) : Nat :=
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuationFixed
  let bound := termValue sameRowsZeroValuationFixed boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveNatListSameRowsBranchesFixedPayloadPolynomial tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary numericBound
      bitBound)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource sameRowsZeroValuationFixed
      outerVariables boundTerm)
    branchResource

theorem compactAdditiveNatListSameRowsUniversalPayloadEnvelope_le_fixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveNatListSameRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListSameRowsUniversalPayloadEnvelope tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary rows <=
      compactAdditiveNatListSameRowsFixedUniversalPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary numericBound
        bitBound := by
  let body := compactAdditiveNatListSameRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables sameRowsZeroValuationFixed
  let bound := termValue sameRowsZeroValuationFixed boundTerm
  let oldCore := compactAdditiveNatListSameRowsBranchesTransparentEnvelope
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  let newCore := compactAdditiveNatListSameRowsBranchesFixedPayloadPolynomial
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    numericBound bitBound
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    sameRowsZeroValuationFixed outerVariables boundTerm
  have hcore : oldCore <= newCore :=
    compactAdditiveNatListSameRowsBranchesTransparentEnvelope_le_fixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound rows hwidth htokenCount hsourceCount
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hbranch : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldCore newCore hcore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body
    boundResource oldBranchResource boundResource newBranchResource
    le_rfl hbranch
  simpa only [compactAdditiveNatListSameRowsUniversalPayloadEnvelope,
    compactAdditiveNatListSameRowsFixedUniversalPayloadEnvelope, body,
    boundTerm, outerFormula, outerVariables, Gamma, bound, oldCore, newCore,
    oldBranchResource, newBranchResource, boundResource,
    sameRowsZeroValuationFixed] using htotal

#print axioms
  compactAdditiveNatListSameRowsTerminalStructuralPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveNatListSameRowsBranchEnvelope_le_witnessPrefixFixed
#print axioms
  compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveNatListSameRowsBranchStructuralPayloadEnvelope_le_uniform
#print axioms
  compactAdditiveNatListSameRowsBranchPayloadResourceSum_le_uniform
#print axioms
  compactAdditiveNatListSameRowsBranchesTransparentEnvelope_le_fixed
#print axioms
  compactAdditiveNatListSameRowsBranchesFixedPayloadPolynomial_le_closed
#print axioms
  compactAdditiveNatListSameRowsUniversalPayloadEnvelope_le_fixed

end FoundationCompactNumericListedDirectNatListSameRowsFixedPolynomialBounds
