import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectTokenSlicePostWitnessAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompiler
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-! # Row-independent direct bound for an additive natural-list slice -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectNatListSliceUniformDirectBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSlicePostWitnessAtomicFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      (Rewriting.app right :
        ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
          ArithmeticSemiformula targetVariables targetArity) := by
  cases h
  rfl

private theorem binaryFunctionTerm_freeVariables
    {Variable : Type*} [DecidableEq Variable] {boundArity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ArithmeticSemiterm Variable boundArity) :
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
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticAddTerm_freeVariables
    {Variable : Type*} [DecidableEq Variable] {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ :
      ArithmeticSemiterm Variable boundArity).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  change (LO.FirstOrder.Semiterm.func Language.Add.add
    ![left, right]).freeVariables = _
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

/-- The slice matrix after removing its single bounded witness guard. -/
def compactAdditiveNatListSliceDirectTerminal
    (tokenTable width tokenCount start count finish : Nat) :
    ArithmeticSemiformula Nat 1 :=
  ((Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val) ⇜
      ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
        Rew.bShift (shortBinaryNumeralTerm width),
        Rew.bShift (shortBinaryNumeralTerm tokenCount),
        Rew.bShift (shortBinaryNumeralTerm start),
        Rew.bShift (shortBinaryNumeralTerm count),
        (#0 : ArithmeticSemiterm Nat 1)]) ⋏
    “!!(Rew.bShift (shortBinaryNumeralTerm finish)) =
      #0 + !!(Rew.bShift (shortBinaryNumeralTerm count))”

def compactAdditiveNatListSliceDirectFormula
    (tokenTable width tokenCount start count finish : Nat) :
    ValuationFormula :=
  explicitBoundedWitnessFormula (shortBinaryNumeralTerm tokenCount) 1
    (compactAdditiveNatListSliceDirectTerminal tokenTable width tokenCount
      start count finish)

theorem compactAdditiveNatListSliceDirectFormula_alignment
    (tokenTable width tokenCount start count finish : Nat) :
    compactAdditiveNatListSliceClosedFormula tokenTable width tokenCount start
        count finish =
      compactAdditiveNatListSliceDirectFormula tokenTable width tokenCount
        start count finish := by
  unfold compactAdditiveNatListSliceClosedFormula
    compactAdditiveNatListSliceDirectFormula
    compactAdditiveNatListSliceDirectTerminal
    compactAdditiveNatListSliceDef explicitBoundedWitnessFormula
  simp [Rew.comp_app, LO.FirstOrder.Semiformula.bexsLTSucc,
    LO.FirstOrder.Semiformula.bexsLT,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  · congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactAdditiveNatListSliceDirectTerminal_substitution_alignment
    (tokenTable width tokenCount start count finish bodyStart : Nat) :
    (compactAdditiveNatListSliceDirectTerminal tokenTable width tokenCount
        start count finish) ⇜ ![shortBinaryNumeralTerm bodyStart] =
      (compactAdditiveListHeaderClosedFormula tokenTable width tokenCount
          start count bodyStart ⋏
        “!!(shortBinaryNumeralTerm finish) =
          !!(shortBinaryNumeralTerm bodyStart) +
            !!(shortBinaryNumeralTerm count)”) := by
  unfold compactAdditiveNatListSliceDirectTerminal
    compactAdditiveListHeaderClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  apply arithmeticRewritingApp_congr
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

theorem compactAdditiveNatListSliceDirectTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount start count finish : Nat) :
    (compactAdditiveNatListSliceDirectTerminal tokenTable width tokenCount
      start count finish).freeVariables = ∅ := by
  unfold compactAdditiveNatListSliceDirectTerminal
  rw [LO.FirstOrder.Semiformula.freeVariables_and]
  apply Finset.union_eq_empty.mpr
  constructor
  · apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate
    all_goals
      first
      | exact bShift_freeVariables_eq_empty_of_empty _
          (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      | simp
  · simp [arithmeticAddTerm_freeVariables,
      bShift_freeVariables_eq_empty_of_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]

def compactAdditiveNatListSliceOpenTermCodePolynomial
    (bitBound : Nat) : Nat :=
  3 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length + 1

theorem shiftedShortBinaryNumeralTerm_code_length_le_sliceOpen
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode
      (Rew.bShift (shortBinaryNumeralTerm value) :
        ArithmeticSemiterm Nat 1)).length <=
      compactAdditiveNatListSliceOpenTermCodePolynomial bitBound := by
  have hcode := binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  have hsymbols := termSymbolCount_le_binaryTermCode_length
    (shortBinaryNumeralTerm value)
  have hshift := binaryTermCode_bShift_length_le_add_symbols
    (shortBinaryNumeralTerm value)
  unfold compactAdditiveNatListSliceOpenTermCodePolynomial
  omega

def compactAdditiveNatListSliceOpenHeaderFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (compactAdditiveNatListSliceOpenTermCodePolynomial bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val)).length

theorem compactAdditiveNatListSliceOpenHeaderFormula_code_length_le
    (tokenTable width tokenCount start count bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hcountSize : Nat.size count <= bitBound) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val) ⇜
        ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
          Rew.bShift (shortBinaryNumeralTerm width),
          Rew.bShift (shortBinaryNumeralTerm tokenCount),
          Rew.bShift (shortBinaryNumeralTerm start),
          Rew.bShift (shortBinaryNumeralTerm count),
          (#0 : ArithmeticSemiterm Nat 1)])).length <=
      compactAdditiveNatListSliceOpenHeaderFormulaCodePolynomial bitBound := by
  let terms : Fin 6 -> ArithmeticSemiterm Nat 1 :=
    ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm width),
      Rew.bShift (shortBinaryNumeralTerm tokenCount),
      Rew.bShift (shortBinaryNumeralTerm start),
      Rew.bShift (shortBinaryNumeralTerm count),
      (#0 : ArithmeticSemiterm Nat 1)]
  let rewriting : Rew ℒₒᵣ Nat 6 Nat 1 := Rew.subst terms
  have hrewriting : RewritingImageCodeBound rewriting
      (compactAdditiveNatListSliceOpenTermCodePolynomial bitBound) := by
    constructor
    · intro coordinate
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      fin_cases coordinate
      · exact shiftedShortBinaryNumeralTerm_code_length_le_sliceOpen
          tokenTable bitBound htableSize
      · exact shiftedShortBinaryNumeralTerm_code_length_le_sliceOpen
          width bitBound hwidthSize
      · exact shiftedShortBinaryNumeralTerm_code_length_le_sliceOpen
          tokenCount bitBound htokenCountSize
      · exact shiftedShortBinaryNumeralTerm_code_length_le_sliceOpen
          start bitBound hstartSize
      · exact shiftedShortBinaryNumeralTerm_code_length_le_sliceOpen
          count bitBound hcountSize
      · have hbvar :
            (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length <=
              compactAdditiveNatListSliceOpenTermCodePolynomial bitBound := by
          unfold compactAdditiveNatListSliceOpenTermCodePolynomial
          omega
        simpa [terms] using hbvar
    · intro coordinate
      simp [rewriting]
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (compactAdditiveNatListSliceOpenTermCodePolynomial bitBound) hrewriting
    (Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val)
  simpa only [rewriting, terms,
    compactAdditiveNatListSliceOpenHeaderFormulaCodePolynomial] using hraw

def compactAdditiveNatListSliceOpenAddTermCodePolynomial
    (bitBound : Nat) : Nat :=
  2 * compactAdditiveNatListSliceOpenTermCodePolynomial bitBound +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

private theorem arithmeticAddTerm_code_length_le_open
    {boundArity : Nat}
    (left right : ArithmeticSemiterm Nat boundArity) :
    (binaryTermCode (‘!!left + !!right’ :
      ArithmeticSemiterm Nat boundArity)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Matrix.fun_eq_vec_two, binaryTermCode, binaryFunctionTermCodeOverhead]
  omega

private theorem arithmeticEqualityFormula_code_length_le_open
    {boundArity : Nat}
    (left right : ArithmeticSemiterm Nat boundArity) :
    (binaryFormulaCode (“!!left = !!right” :
      ArithmeticSemiformula Nat boundArity)).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        equalityFormulaCodeOverhead := by
  simp [Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Matrix.fun_eq_vec_two, binaryFormulaCode, equalityFormulaCodeOverhead]
  omega

def compactAdditiveNatListSliceOpenEndpointFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  compactAdditiveNatListSliceOpenTermCodePolynomial bitBound +
    compactAdditiveNatListSliceOpenAddTermCodePolynomial bitBound +
    equalityFormulaCodeOverhead

theorem compactAdditiveNatListSliceOpenEndpointFormula_code_length_le
    (finish count bitBound : Nat)
    (hfinishSize : Nat.size finish <= bitBound)
    (hcountSize : Nat.size count <= bitBound) :
    (binaryFormulaCode
      (“!!(Rew.bShift (shortBinaryNumeralTerm finish)) =
        #0 + !!(Rew.bShift (shortBinaryNumeralTerm count))” :
        ArithmeticSemiformula Nat 1)).length <=
      compactAdditiveNatListSliceOpenEndpointFormulaCodePolynomial
        bitBound := by
  let left : ArithmeticSemiterm Nat 1 :=
    Rew.bShift (shortBinaryNumeralTerm finish)
  let countTerm : ArithmeticSemiterm Nat 1 :=
    Rew.bShift (shortBinaryNumeralTerm count)
  let right : ArithmeticSemiterm Nat 1 := ‘#0 + !!countTerm’
  let termResource :=
    compactAdditiveNatListSliceOpenAddTermCodePolynomial bitBound
  have hleftTight := shiftedShortBinaryNumeralTerm_code_length_le_sliceOpen
    finish bitBound hfinishSize
  have hcount := shiftedShortBinaryNumeralTerm_code_length_le_sliceOpen
    count bitBound hcountSize
  have hcountTerm : (binaryTermCode countTerm).length <=
      compactAdditiveNatListSliceOpenTermCodePolynomial bitBound := by
    simpa only [countTerm] using hcount
  have hbvar : (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length <=
      compactAdditiveNatListSliceOpenTermCodePolynomial bitBound := by
    unfold compactAdditiveNatListSliceOpenTermCodePolynomial
    omega
  have hright : (binaryTermCode right).length <= termResource := by
    have hraw := arithmeticAddTerm_code_length_le_open
      (#0 : ArithmeticSemiterm Nat 1) countTerm
    calc
      (binaryTermCode right).length <=
          (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length +
            (binaryTermCode countTerm).length +
              binaryFunctionTermCodeOverhead Language.Add.add := by
        simpa only [right] using hraw
      _ <= termResource := by
        unfold termResource
          compactAdditiveNatListSliceOpenAddTermCodePolynomial
        omega
  have hleft : (binaryTermCode left).length <=
      compactAdditiveNatListSliceOpenTermCodePolynomial bitBound := by
    simpa only [left] using hleftTight
  have hformula := arithmeticEqualityFormula_code_length_le_open left right
  change (binaryFormulaCode (“!!left = !!right” :
    ArithmeticSemiformula Nat 1)).length <= _
  unfold compactAdditiveNatListSliceOpenEndpointFormulaCodePolynomial
  omega

def compactAdditiveNatListSliceDirectBodyCodePolynomial
    (bitBound : Nat) : Nat :=
  compactAdditiveNatListSliceOpenHeaderFormulaCodePolynomial bitBound +
    compactAdditiveNatListSliceOpenEndpointFormulaCodePolynomial bitBound +
    (binaryNatCode 4).length

theorem compactAdditiveNatListSliceDirectTerminal_code_length_le
    (tokenTable width tokenCount start count finish bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListSliceDirectTerminal tokenTable width tokenCount
        start count finish)).length <=
      compactAdditiveNatListSliceDirectBodyCodePolynomial bitBound := by
  have hheader := compactAdditiveNatListSliceOpenHeaderFormula_code_length_le
    tokenTable width tokenCount start count bitBound htableSize hwidthSize
    htokenCountSize hstartSize hcountSize
  have hendpoint :=
    compactAdditiveNatListSliceOpenEndpointFormula_code_length_le finish count
      bitBound hfinishSize hcountSize
  unfold compactAdditiveNatListSliceDirectTerminal
    compactAdditiveNatListSliceDirectBodyCodePolynomial
  simp only [binaryFormulaCode, List.length_append]
  omega

def compactAdditiveNatListSliceTerminalSyntaxResource
    (numericBound bitBound : Nat) : Nat :=
  compactAdditiveListHeaderUniformFixedPayloadPolynomial numericBound bitBound +
    tokenSlicePostWitnessPositiveAtomicFixedPayloadPolynomial bitBound +
    (binaryNatCode 4).length + 1

def compactAdditiveNatListSliceTerminalCodeResource
    (numericBound bitBound : Nat) : Nat :=
  compactAdditiveListHeaderUniformFixedPayloadPolynomial numericBound bitBound +
    tokenSlicePostWitnessPositiveAtomicFixedPayloadPolynomial bitBound +
    (binaryNatCode 4).length

def compactAdditiveNatListSliceTerminalPayloadResource
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactAdditiveNatListSliceTerminalSyntaxResource numericBound bitBound)
    (compactAdditiveListHeaderUniformFixedPayloadPolynomial numericBound
      bitBound)
    (tokenSlicePostWitnessPositiveAtomicFixedPayloadPolynomial bitBound)

noncomputable def compactAdditiveNatListSliceTerminalFixedBound
    (tokenTable width tokenCount start count finish bodyStart numericBound
      bitBound : Nat)
    (hbodyStart : bodyStart <= tokenCount)
    (hheader : CompactAdditiveListHeader tokenTable width tokenCount start count
      bodyStart)
    (hfinish : finish = bodyStart + count)
    (hwidthBound : width <= numericBound)
    (hstartBound : start <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hbodyStartSize : Nat.size bodyStart <= bitBound) :
    FixedClosedDirectFormulaBound
      (compactAdditiveListHeaderClosedFormula tokenTable width tokenCount start
          count bodyStart ⋏
        “!!(shortBinaryNumeralTerm finish) =
          !!(shortBinaryNumeralTerm bodyStart) +
            !!(shortBinaryNumeralTerm count)”)
      (compactAdditiveNatListSliceTerminalPayloadResource numericBound bitBound)
      (compactAdditiveNatListSliceTerminalCodeResource numericBound
        bitBound) := by
  let headerCertificate := compactAdditiveListHeaderExplicitHybridCertificate
    tokenTable width tokenCount start count bodyStart hheader
  let headerResource :=
    compactAdditiveListHeaderUniformFixedPayloadPolynomial numericBound bitBound
  have hheaderPayload : headerCertificate.compile.payloadLength <=
      headerResource :=
    (compile_payloadLength_le_structuralPayloadBound headerCertificate).trans
      (compactAdditiveListHeaderExplicitHybridCertificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount start count bodyStart numericBound bitBound
        hwidthBound hstartBound htableSize hwidthSize htokenCountSize hstartSize
        hcountSize hbodyStartSize hheader)
  let headerBound := fixedClosedDirectFormulaBoundOfProof
    headerCertificate.compile headerResource hheaderPayload
      (compactAdditiveListHeaderClosedFormula_freeVariables_eq_empty tokenTable
        width tokenCount start count bodyStart)
  let endpointCertificate := tokenSliceAtValuationEndpointCertificate
    parserFixedZeroValuation (shortBinaryNumeralTerm bodyStart)
      (shortBinaryNumeralTerm finish) count (by
        simpa [termValue_shortBinaryNumeralTerm] using hfinish)
  let endpointResource :=
    tokenSlicePostWitnessPositiveAtomicFixedPayloadPolynomial bitBound
  have hendpointPayload : endpointCertificate.compile.payloadLength <=
      endpointResource :=
    (compile_payloadLength_le_structuralPayloadBound endpointCertificate).trans
      ((tokenSliceAtValuationEndpointCertificate_structuralPayloadBound_le_transparent
        parserFixedZeroValuation (shortBinaryNumeralTerm bodyStart)
        (shortBinaryNumeralTerm finish) count (by
          simpa [termValue_shortBinaryNumeralTerm] using hfinish)).trans
        (tokenSliceAtValuationEndpointStructuralEnvelope_le_fixed
          parserFixedZeroValuation bodyStart finish count bitBound
          hbodyStartSize hfinishSize hcountSize))
  have hendpointClosed :
      (“!!(shortBinaryNumeralTerm finish) =
        !!(shortBinaryNumeralTerm bodyStart) +
          !!(shortBinaryNumeralTerm count)” : ValuationFormula).freeVariables =
        ∅ := by
    simp [show
      (‘!!(shortBinaryNumeralTerm bodyStart) +
        !!(shortBinaryNumeralTerm count)’ : ValuationTerm) =
        addTerm
          (shortBinaryNumeralTerm bodyStart)
          (shortBinaryNumeralTerm count) by rfl,
      appendSourcePrefixAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
  let endpointBound := fixedClosedDirectFormulaBoundOfProof
    endpointCertificate.compile endpointResource hendpointPayload
      hendpointClosed
  let syntaxResource :=
    compactAdditiveNatListSliceTerminalSyntaxResource numericBound bitBound
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource compactAdditiveNatListSliceTerminalSyntaxResource
    omega
  have hheaderSyntax : headerResource <= syntaxResource := by
    unfold syntaxResource compactAdditiveNatListSliceTerminalSyntaxResource
      headerResource
    omega
  have hendpointSyntax : endpointResource <= syntaxResource := by
    unfold syntaxResource compactAdditiveNatListSliceTerminalSyntaxResource
      endpointResource
    omega
  have hconjunctionSyntax :
      headerResource + endpointResource + (binaryNatCode 4).length <=
        syntaxResource := by
    unfold syntaxResource compactAdditiveNatListSliceTerminalSyntaxResource
      headerResource endpointResource
    omega
  simpa only [compactAdditiveNatListSliceTerminalPayloadResource,
    compactAdditiveNatListSliceTerminalCodeResource, syntaxResource,
    headerResource, endpointResource] using
    FixedClosedDirectFormulaBound.conjunction headerBound endpointBound
      syntaxResource hpositive hheaderSyntax hendpointSyntax
      hconjunctionSyntax

def compactAdditiveNatListSliceUniformDirectPayloadResource
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 1 0 numericBound
    (compactAdditiveNatListSliceDirectBodyCodePolynomial bitBound)
    (compactAdditiveNatListSliceTerminalPayloadResource numericBound bitBound)

noncomputable def compactAdditiveNatListSliceUniformDirectBound
    (tokenTable width tokenCount start count finish bodyStart numericBound
      bitBound : Nat)
    (hbodyStart : bodyStart <= tokenCount)
    (hheader : CompactAdditiveListHeader tokenTable width tokenCount start count
      bodyStart)
    (hfinish : finish = bodyStart + count)
    (htokenCountBound : tokenCount <= numericBound)
    (hwidthBound : width <= numericBound)
    (hstartBound : start <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hbodyStartSize : Nat.size bodyStart <= bitBound) :
    FixedClosedDirectFormulaBound
      (compactAdditiveNatListSliceClosedFormula tokenTable width tokenCount
        start count finish)
      (compactAdditiveNatListSliceUniformDirectPayloadResource numericBound
        bitBound)
      (compactAdditiveNatListSliceUniformDirectPayloadResource numericBound
        bitBound) := by
  let body := compactAdditiveNatListSliceDirectTerminal tokenTable width
    tokenCount start count finish
  let values : Fin 1 -> Nat := ![bodyStart]
  let terminalBound := compactAdditiveNatListSliceTerminalFixedBound tokenTable
    width tokenCount start count finish bodyStart numericBound bitBound
    hbodyStart hheader hfinish hwidthBound hstartBound htableSize hwidthSize
    htokenCountSize hstartSize hcountSize hfinishSize hbodyStartSize
  have hterminalFormula :
      (compactAdditiveListHeaderClosedFormula tokenTable width tokenCount start
          count bodyStart ⋏
        “!!(shortBinaryNumeralTerm finish) =
          !!(shortBinaryNumeralTerm bodyStart) +
            !!(shortBinaryNumeralTerm count)”) =
      body ⇜ fun coordinate => shortBinaryNumeralTerm (values coordinate) := by
    dsimp only [body, values]
    rw [show (fun coordinate : Fin 1 =>
      shortBinaryNumeralTerm (![bodyStart] coordinate)) =
        ![shortBinaryNumeralTerm bodyStart] by
          funext coordinate
          fin_cases coordinate
          rfl]
    exact (compactAdditiveNatListSliceDirectTerminal_substitution_alignment
      tokenTable width tokenCount start count finish bodyStart).symm
  let terminalAtZero := castValuationContextProof hterminalFormula
    terminalBound.proof
  have hterminal : terminalAtZero.payloadLength <=
      compactAdditiveNatListSliceTerminalPayloadResource numericBound
        bitBound := by
    dsimp only [terminalAtZero]
    rw [castValuationContextProof_payloadLength_eq]
    exact terminalBound.payloadLength_le
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    exact hbodyStart
  have hbody : (binaryFormulaCode body).length <=
      compactAdditiveNatListSliceDirectBodyCodePolynomial bitBound :=
    compactAdditiveNatListSliceDirectTerminal_code_length_le tokenTable width
      tokenCount start count finish bitBound htableSize hwidthSize
      htokenCountSize hstartSize hcountSize hfinishSize
  have hcontext : formulaCodeSum
      (valuationContext body.freeVariables parserFixedZeroValuation) <=
        0 := by
    dsimp only [body]
    rw [compactAdditiveNatListSliceDirectTerminal_freeVariables_eq_empty]
    simp [valuationContext, formulaCodeSum]
  let compilation :=
    compileExplicitBoundedWitnessDirectPublicWithUniformResource
      0 tokenCount numericBound
      (compactAdditiveNatListSliceDirectBodyCodePolynomial bitBound)
      htokenCountBound body values hvalues hbody hcontext
      (compactAdditiveNatListSliceTerminalPayloadResource numericBound bitBound)
      terminalAtZero hterminal
  have hcoordinates :
      compilation.formula = explicitBoundedWitnessFormula
          (shortBinaryNumeralTerm tokenCount) 1 body ∧
        compilation.payloadResource =
          explicitBoundedWitnessDirectPublicPayloadEnvelope 1 0 numericBound
            (compactAdditiveNatListSliceDirectBodyCodePolynomial bitBound)
            (compactAdditiveNatListSliceTerminalPayloadResource numericBound
              bitBound) := by
    constructor <;> rfl
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm tokenCount) 1 body
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactAdditiveNatListSliceClosedFormula tokenTable width tokenCount start
        count finish := by
    exact (compactAdditiveNatListSliceDirectFormula_alignment tokenTable width
      tokenCount start count finish).symm
  let proof := castValuationContextProof hformula rawProof
  let resource := compactAdditiveNatListSliceUniformDirectPayloadResource
    numericBound bitBound
  have hpayload : proof.payloadLength <= resource := by
    dsimp only [proof]
    rw [castValuationContextProof_payloadLength_eq]
    apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
      hcoordinates.1
    simpa only [resource,
      compactAdditiveNatListSliceUniformDirectPayloadResource] using
      hcoordinates.2
  have hclosed :
      (compactAdditiveNatListSliceClosedFormula tokenTable width tokenCount
        start count finish).freeVariables = ∅ := by
    unfold compactAdditiveNatListSliceClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _
  exact fixedClosedDirectFormulaBoundOfProof proof resource hpayload hclosed

#print axioms compactAdditiveNatListSliceDirectFormula_alignment
#print axioms compactAdditiveNatListSliceDirectTerminal_substitution_alignment
#print axioms compactAdditiveNatListSliceUniformDirectBound

end FoundationCompactNumericListedDirectNatListSliceUniformDirectBound
