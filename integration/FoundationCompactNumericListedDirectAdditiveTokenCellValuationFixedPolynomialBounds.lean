import integration.FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed-polynomial resource bound for one additive token cell

This file removes the concrete closed numerals from the resource coordinate of
one token-cell certificate.  The resulting ceiling depends only on a numeric
bound and a common binary-width bound; it does not enumerate represented table
values.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol ![left, right]).freeVariables =
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
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem hybridConjunctionStructuralPayloadEnvelope_mono
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    {leftSmall leftLarge rightSmall rightLarge : Nat}
    (hleft : leftSmall <= leftLarge)
    (hright : rightSmall <= rightLarge) :
    hybridConjunctionStructuralPayloadEnvelope valuation left right
        leftSmall rightSmall <=
      hybridConjunctionStructuralPayloadEnvelope valuation left right
        leftLarge rightLarge := by
  unfold hybridConjunctionStructuralPayloadEnvelope
  dsimp only
  omega

def additiveTokenCellAtValuationResourceEnvelope
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm)
    (cursorResource successorResource entryResource : Nat) : Nat :=
  compactAdditiveTokenCellAtValuationStructuralPayloadEnvelope tokenTableTerm
    widthTerm tokenCountTerm cursorTerm valueTerm nextTerm cursorResource
    successorResource entryResource

theorem additiveTokenCellAtValuationResourceEnvelope_mono
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm)
    {cursorSmall cursorLarge successorSmall successorLarge entrySmall entryLarge :
      Nat}
    (hcursor : cursorSmall <= cursorLarge)
    (hsuccessor : successorSmall <= successorLarge)
    (hentry : entrySmall <= entryLarge) :
    additiveTokenCellAtValuationResourceEnvelope tokenTableTerm widthTerm
        tokenCountTerm cursorTerm valueTerm nextTerm cursorSmall successorSmall
          entrySmall <=
      additiveTokenCellAtValuationResourceEnvelope tokenTableTerm widthTerm
        tokenCountTerm cursorTerm valueTerm nextTerm cursorLarge successorLarge
          entryLarge := by
  unfold additiveTokenCellAtValuationResourceEnvelope
  exact hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hcursor
    (hybridConjunctionStructuralPayloadEnvelope_mono _ _ _ hsuccessor hentry)

def compactAdditiveTokenCellAtValuationOpenEntryStructuralPayloadPolynomial
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm) : Nat :=
  additiveTokenCellAtValuationResourceEnvelope tokenTableTerm widthTerm
    tokenCountTerm cursorTerm valueTerm nextTerm
    (compilePositiveRelationPayloadPolynomial zeroValuation
      Language.ORing.Rel.lt ![cursorTerm, tokenCountTerm])
    (compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq
      ![nextTerm, (‘!!cursorTerm + 1’ : ValuationTerm)])
    (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      zeroValuation tokenTableTerm widthTerm cursorTerm valueTerm)

theorem
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openEntry
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm)
    (htable : tokenTableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (htokenCount : tokenCountTerm.freeVariables = ∅)
    (hcursor : cursorTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅)
    (hnext : nextTerm.freeVariables = ∅)
    (hcell : CompactAdditiveTokenCell
      (termValue zeroValuation tokenTableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation tokenCountTerm)
      (termValue zeroValuation cursorTerm)
      (termValue zeroValuation valueTerm)
      (termValue zeroValuation nextTerm)) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm
          hcell) <=
      compactAdditiveTokenCellAtValuationOpenEntryStructuralPayloadPolynomial
        tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm := by
  let successorTerm : ValuationTerm := ‘!!cursorTerm + 1’
  let cursorCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![cursorTerm, tokenCountTerm]
      hcell.1
  let successorCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![nextTerm, successorTerm] (by
        change termValue zeroValuation nextTerm =
          termValue zeroValuation successorTerm
        simpa [successorTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne] using hcell.2.1)
  let entryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
      tokenTableTerm widthTerm cursorTerm valueTerm hcell.2.2
  have hcursorVars : cursorTerm.freeVariables ⊆ {0} := by
    rw [hcursor]
    simp
  have htokenCountVars : tokenCountTerm.freeVariables ⊆ {0} := by
    rw [htokenCount]
    simp
  have hnextVars : nextTerm.freeVariables ⊆ {0} := by
    rw [hnext]
    simp
  have hsuccessorClosed : successorTerm.freeVariables = ∅ := by
    dsimp only [successorTerm]
    rw [arithmeticAddTerm_freeVariables, hcursor,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hsuccessorVars : successorTerm.freeVariables ⊆ {0} := by
    rw [hsuccessorClosed]
    simp
  have hcursorResource :=
    compilePositiveRelationPayloadResource_le_publicPolynomial zeroValuation
      Language.ORing.Rel.lt ![cursorTerm, tokenCountTerm]
      hcursorVars htokenCountVars
  have hsuccessorResource :=
    compilePositiveRelationPayloadResource_le_publicPolynomial zeroValuation
      Language.Eq.eq ![nextTerm, successorTerm]
      hnextVars hsuccessorVars
  have hentryResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      zeroValuation tokenTableTerm widthTerm cursorTerm valueTerm
      htable hwidth hcursorVars hvalue hcell.2.2
  have hinner := hybridConjunctionStructuralPayloadBound_le_envelope
    (CheckedHybridValuationBoundedFormulaCertificate.cast
      (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm
      successorCertificate)
    entryCertificate
    (compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq
      ![nextTerm, successorTerm])
    (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      zeroValuation tokenTableTerm widthTerm cursorTerm valueTerm)
    (by
      simpa only [hybridFormulaStructuralPayloadBound,
        successorCertificate] using hsuccessorResource)
    hentryResource
  have hparts := hybridConjunctionStructuralPayloadBound_le_envelope
    (CheckedHybridValuationBoundedFormulaCertificate.cast
      (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm cursorCertificate)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm
        successorCertificate)
      entryCertificate)
    (compilePositiveRelationPayloadPolynomial zeroValuation
      Language.ORing.Rel.lt ![cursorTerm, tokenCountTerm])
    (hybridConjunctionStructuralPayloadEnvelope zeroValuation
      (“!!nextTerm = !!cursorTerm + 1” : ValuationFormula)
      (compactFixedWidthEntryAtValuationFormula
        tokenTableTerm widthTerm cursorTerm valueTerm)
      (compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq
        ![nextTerm, successorTerm])
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        zeroValuation tokenTableTerm widthTerm cursorTerm valueTerm))
    (by
      simpa only [hybridFormulaStructuralPayloadBound,
        cursorCertificate] using hcursorResource)
    hinner
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (CheckedHybridValuationBoundedFormulaCertificate.cast
          (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm
          cursorCertificate)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (CheckedHybridValuationBoundedFormulaCertificate.cast
            (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm
            successorCertificate)
          entryCertificate)) <= _
  unfold compactAdditiveTokenCellAtValuationOpenEntryStructuralPayloadPolynomial
    additiveTokenCellAtValuationResourceEnvelope
    compactAdditiveTokenCellAtValuationStructuralPayloadEnvelope
  dsimp only
  exact hparts

/-- A common term-code ceiling for the two atomic token-cell relations. -/
def additiveTokenCellAtomicTermCodeCeiling (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def additiveTokenCellAtomicFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial numericBound
    (additiveTokenCellAtomicTermCodeCeiling bitBound)

def additiveTokenCellAtomicFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  orderAtomicFormulaCodeEnvelope
    (additiveTokenCellAtomicTermCodeCeiling bitBound)

def additiveTokenCellEntryFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def additiveTokenCellClosedValueFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val)).length

/-- A uniform code ceiling for the four fixed-width-entry inputs and all terms
generated from them. -/
def additiveTokenCellFixedWidthEntryTermCodeCeiling (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let rowIndexCode := (binaryTermCode (&0 : ValuationTerm)).length
  let productCode := numeralCode + numeralCode +
    binaryFunctionTermCodeOverhead Language.Mul.mul
  let leftIndexCode := 2 * productCode + rowIndexCode +
    binaryFunctionTermCodeOverhead Language.Add.add
  numeralCode + numeralCode + leftIndexCode + 2 * numeralCode +
    (binaryTermCode fixedWidthRightBitIndexTerm).length +
    2 * numeralCode + 1

def additiveTokenCellFixedWidthEntryCoordinate
    (numericBound bitBound : Nat) : Nat :=
  numericBound + bitBound +
    additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound + 1

def additiveTokenCellFixedWidthEntryPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (additiveTokenCellFixedWidthEntryCoordinate numericBound bitBound))

def additiveTokenCellContextFormulaCodeSumEnvelope
    (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length

def additiveTokenCellAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let atomicResource :=
    additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound
  let entryResource :=
    additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound
  let atomicCode := additiveTokenCellAtomicFormulaCodeEnvelope bitBound
  let entryCode := additiveTokenCellEntryFormulaCodeEnvelope bitBound
  let contextResource :=
    additiveTokenCellContextFormulaCodeSumEnvelope numericBound
  let conjunctionTag := (binaryNatCode 4).length
  contextResource + 4 *
    (2 * atomicResource + entryResource + 2 * atomicCode + entryCode +
      conjunctionTag + 1) + 1

def additiveTokenCellFullyUniformPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let atomicResource :=
    additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound
  let entryResource :=
    additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    additiveTokenCellAssemblySyntaxPolynomial numericBound bitBound
  2 * atomicResource + entryResource +
    6 * generalContextAssemblyEnvelope syntaxResource

theorem valuationContextFormulaCodeSum_le_tokenCellEnvelope
    (valuation : Nat -> Nat) (formula : ValuationFormula)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext formula.freeVariables valuation) <=
      additiveTokenCellContextFormulaCodeSumEnvelope numericBound := by
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
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum,
    additiveTokenCellContextFormulaCodeSumEnvelope] using hraw

private theorem shortNumeralCode_le_atomicCeiling
    (value bitBound : Nat) (hsize : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      additiveTokenCellAtomicTermCodeCeiling bitBound := by
  have hcode := binaryNumeralTerm_code_length_le_envelope value bitBound hsize
  exact hcode.trans (by
    unfold additiveTokenCellAtomicTermCodeCeiling
    omega)

private theorem additiveTokenCellSuccessorCode_le_atomicCeiling
    (cursor bitBound : Nat) (hcursorSize : Nat.size cursor <= bitBound) :
    (binaryTermCode
      (‘!!(shortBinaryNumeralTerm cursor) + 1’ : ValuationTerm)).length <=
      additiveTokenCellAtomicTermCodeCeiling bitBound := by
  have hcursorCode := binaryNumeralTerm_code_length_le_envelope cursor bitBound
    hcursorSize
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm cursor) (‘1’ : ValuationTerm)
  change (binaryTermCode
    (paAddTerm (shortBinaryNumeralTerm cursor) (‘1’ : ValuationTerm))).length <= _
  exact hraw.trans (by
    unfold additiveTokenCellAtomicTermCodeCeiling
    omega)

theorem additiveTokenCellCursorPayloadPolynomial_le_fixed
    (cursor tokenCount numericBound bitBound : Nat)
    (hcursorSize : Nat.size cursor <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound) :
    compilePositiveRelationPayloadPolynomial zeroValuation
        Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm cursor,
          shortBinaryNumeralTerm tokenCount] <=
      additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound := by
  let args : Fin 2 -> ValuationTerm :=
    ![shortBinaryNumeralTerm cursor, shortBinaryNumeralTerm tokenCount]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm cursor).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm tokenCount).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hzero : zeroValuation 0 <= numericBound := by
    simp [zeroValuation,
      FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation]
  have hfirstCode := shortNumeralCode_le_atomicCeiling cursor bitBound
    hcursorSize
  have hsecondCode := shortNumeralCode_le_atomicCeiling tokenCount bitBound
    htokenCountSize
  have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed
    zeroValuation Language.ORing.Rel.lt args numericBound
      (additiveTokenCellAtomicTermCodeCeiling bitBound)
      hfirst hsecond hzero hfirstCode hsecondCode
  simpa only [args, additiveTokenCellAtomicFixedPayloadPolynomial] using hfixed

theorem additiveTokenCellSuccessorPayloadPolynomial_le_fixed
    (cursor next numericBound bitBound : Nat)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hnextSize : Nat.size next <= bitBound) :
    compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq
        ![shortBinaryNumeralTerm next,
          (‘!!(shortBinaryNumeralTerm cursor) + 1’ : ValuationTerm)] <=
      additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound := by
  let successorTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm cursor) + 1’
  let args : Fin 2 -> ValuationTerm :=
    ![shortBinaryNumeralTerm next, successorTerm]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm next).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change successorTerm.freeVariables ⊆ {0}
    rw [show successorTerm.freeVariables = ∅ by
      dsimp only [successorTerm]
      rw [arithmeticAddTerm_freeVariables,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        arithmeticOneTerm_freeVariables_eq_empty]
      simp]
    simp
  have hzero : zeroValuation 0 <= numericBound := by
    simp [zeroValuation,
      FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation]
  have hfirstCode := shortNumeralCode_le_atomicCeiling next bitBound hnextSize
  have hsecondCode := additiveTokenCellSuccessorCode_le_atomicCeiling cursor
    bitBound hcursorSize
  have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed
    zeroValuation Language.Eq.eq args numericBound
      (additiveTokenCellAtomicTermCodeCeiling bitBound)
      hfirst hsecond hzero hfirstCode hsecondCode
  simpa only [args, successorTerm,
    additiveTokenCellAtomicFixedPayloadPolynomial] using hfixed

theorem additiveTokenCellGuardPayloadPolynomial_le_fixed
    (value bound numericBound bitBound : Nat)
    (hvalueSize : Nat.size value <= bitBound)
    (hboundSize : Nat.size bound <= bitBound) :
    compilePositiveRelationPayloadPolynomial zeroValuation
        Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm value,
          (‘!!(shortBinaryNumeralTerm bound) + 1’ : ValuationTerm)] <=
      additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound := by
  let successorTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  let args : Fin 2 -> ValuationTerm :=
    ![shortBinaryNumeralTerm value, successorTerm]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm value).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change successorTerm.freeVariables ⊆ {0}
    rw [show successorTerm.freeVariables = ∅ by
      dsimp only [successorTerm]
      rw [arithmeticAddTerm_freeVariables,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        arithmeticOneTerm_freeVariables_eq_empty]
      simp]
    simp
  have hzero : zeroValuation 0 <= numericBound := by
    simp [zeroValuation,
      FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation]
  have hfirstCode := shortNumeralCode_le_atomicCeiling value bitBound
    hvalueSize
  have hsecondCode := additiveTokenCellSuccessorCode_le_atomicCeiling bound
    bitBound hboundSize
  have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed
    zeroValuation Language.ORing.Rel.lt args numericBound
      (additiveTokenCellAtomicTermCodeCeiling bitBound)
      hfirst hsecond hzero hfirstCode hsecondCode
  simpa only [args, successorTerm,
    additiveTokenCellAtomicFixedPayloadPolynomial] using hfixed

theorem additiveTokenCellCursorFormula_code_length_le_uniform
    (cursor tokenCount bitBound : Nat)
    (hcursorSize : Nat.size cursor <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm cursor) <
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound := by
  have hcursorCode := shortNumeralCode_le_atomicCeiling cursor bitBound
    hcursorSize
  have hcountCode := shortNumeralCode_le_atomicCeiling tokenCount bitBound
    htokenCountSize
  have hraw := lessThanFormula_code_le_orderAtomic
    (shortBinaryNumeralTerm cursor) (shortBinaryNumeralTerm tokenCount)
    (additiveTokenCellAtomicTermCodeCeiling bitBound) hcursorCode hcountCode
  simpa only [additiveTokenCellAtomicFormulaCodeEnvelope] using hraw

theorem additiveTokenCellSuccessorFormula_code_length_le_uniform
    (cursor next bitBound : Nat)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hnextSize : Nat.size next <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm next) =
        !!(shortBinaryNumeralTerm cursor) + 1” : ValuationFormula)).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound := by
  let successorTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm cursor) + 1’
  have hnextCode := shortNumeralCode_le_atomicCeiling next bitBound hnextSize
  have hsuccessorCode := additiveTokenCellSuccessorCode_le_atomicCeiling cursor
    bitBound hcursorSize
  have hraw := equalityFormula_code_le_orderAtomic
    (shortBinaryNumeralTerm next) successorTerm
    (additiveTokenCellAtomicTermCodeCeiling bitBound) hnextCode hsuccessorCode
  simpa only [successorTerm,
    additiveTokenCellAtomicFormulaCodeEnvelope] using hraw

theorem additiveTokenCellGuardFormula_code_length_le_uniform
    (value bound bitBound : Nat)
    (hvalueSize : Nat.size value <= bitBound)
    (hboundSize : Nat.size bound <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm value) <
        !!(shortBinaryNumeralTerm bound) + 1” : ValuationFormula)).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound := by
  let successorTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  have hvalueCode := shortNumeralCode_le_atomicCeiling value bitBound hvalueSize
  have hsuccessorCode := additiveTokenCellSuccessorCode_le_atomicCeiling bound
    bitBound hboundSize
  have hraw := lessThanFormula_code_le_orderAtomic
    (shortBinaryNumeralTerm value) successorTerm
    (additiveTokenCellAtomicTermCodeCeiling bitBound) hvalueCode hsuccessorCode
  simpa only [successorTerm,
    additiveTokenCellAtomicFormulaCodeEnvelope] using hraw

theorem additiveTokenCellEntryFormula_code_length_le_uniform
    (tokenTable width cursor value bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    (binaryFormulaCode
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm cursor)
        (shortBinaryNumeralTerm value))).length <=
      additiveTokenCellEntryFormulaCodeEnvelope bitBound := by
  let rewriting : Rew ℒₒᵣ Nat 4 Nat 0 := Rew.subst
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm cursor, shortBinaryNumeralTerm value]
  have hrewriting : RewritingImageCodeBound rewriting
      (binaryNumeralTermCodeEnvelope bitBound) := by
    constructor
    · intro index
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      fin_cases index
      · exact binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
          htableSize
      · exact binaryNumeralTerm_code_length_le_envelope width bitBound
          hwidthSize
      · exact binaryNumeralTerm_code_length_le_envelope cursor bitBound
          hcursorSize
      · exact binaryNumeralTerm_code_length_le_envelope value bitBound
          hvalueSize
    · intro index
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (binaryNumeralTermCodeEnvelope bitBound) hrewriting
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
  simpa only [compactFixedWidthEntryAtValuationFormula,
    additiveTokenCellEntryFormulaCodeEnvelope, rewriting] using hraw

theorem additiveTokenCellEntryAtClosedValueTermFormula_code_length_le_uniform
    (tokenTable width cursor bitBound : Nat)
    (valueTerm : ValuationTerm)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound) :
    (binaryFormulaCode
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm cursor) valueTerm)).length <=
      additiveTokenCellEntryFormulaCodeEnvelope bitBound := by
  let rewriting : Rew ℒₒᵣ Nat 4 Nat 0 := Rew.subst
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm cursor, valueTerm]
  have hrewriting : RewritingImageCodeBound rewriting
      (binaryNumeralTermCodeEnvelope bitBound) := by
    constructor
    · intro index
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      fin_cases index
      · exact binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
          htableSize
      · exact binaryNumeralTerm_code_length_le_envelope width bitBound
          hwidthSize
      · exact binaryNumeralTerm_code_length_le_envelope cursor bitBound
          hcursorSize
      · exact hvalueCode
    · intro index
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (binaryNumeralTermCodeEnvelope bitBound) hrewriting
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)
  simpa only [compactFixedWidthEntryAtValuationFormula,
    additiveTokenCellEntryFormulaCodeEnvelope, rewriting] using hraw

theorem
    compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
    (tokenTable width tokenCount cursor next bitBound : Nat)
    (valueTerm : ValuationTerm)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hnextSize : Nat.size next <= bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound) :
    (binaryFormulaCode
      (compactAdditiveTokenCellAtValuationFormula
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm cursor) valueTerm
        (shortBinaryNumeralTerm next))).length <=
      additiveTokenCellClosedValueFormulaCodeEnvelope bitBound := by
  let rewriting : Rew ℒₒᵣ Nat 6 Nat 0 := Rew.subst
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm cursor,
      valueTerm, shortBinaryNumeralTerm next]
  have hrewriting : RewritingImageCodeBound rewriting
      (binaryNumeralTermCodeEnvelope bitBound) := by
    constructor
    · intro index
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      fin_cases index
      · exact binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
          htableSize
      · exact binaryNumeralTerm_code_length_le_envelope width bitBound
          hwidthSize
      · exact binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
          htokenCountSize
      · exact binaryNumeralTerm_code_length_le_envelope cursor bitBound
          hcursorSize
      · exact hvalueCode
      · exact binaryNumeralTerm_code_length_le_envelope next bitBound
          hnextSize
    · intro index
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (binaryNumeralTermCodeEnvelope bitBound) hrewriting
    (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val)
  simpa only [compactAdditiveTokenCellAtValuationFormula,
    additiveTokenCellClosedValueFormulaCodeEnvelope, rewriting] using hraw

@[simp] theorem
    compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
    (tokenTable width tokenCount cursor next : Nat)
    (valueTerm : ValuationTerm)
    (hvalueClosed : valueTerm.freeVariables = ∅) :
    (compactAdditiveTokenCellAtValuationFormula
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm cursor) valueTerm
      (shortBinaryNumeralTerm next)).freeVariables = ∅ := by
  unfold compactAdditiveTokenCellAtValuationFormula
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    compactAdditiveTokenCellDef.val
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm cursor,
      valueTerm, shortBinaryNumeralTerm next] (by
        intro coordinate
        fin_cases coordinate
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty cursor
        · exact hvalueClosed
        · exact shortBinaryNumeralTerm_freeVariables_eq_empty next)

theorem additiveTokenCellFixedWidthEntryPayloadPolynomial_le_fixed
    (tokenTable width cursor value numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hcursorValue : cursor <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        zeroValuation (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm cursor)
          (shortBinaryNumeralTerm value) <=
      additiveTokenCellFixedWidthEntryPayloadPolynomial
        numericBound bitBound := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let indexTerm := shortBinaryNumeralTerm cursor
  let valueTerm := shortBinaryNumeralTerm value
  let productTerm := fixedWidthIndexWidthTerm widthTerm indexTerm
  let coordinate := additiveTokenCellFixedWidthEntryCoordinate
    numericBound bitBound
  have htableCode : (binaryTermCode tableTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope tokenTable bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hindexCode : (binaryTermCode indexTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope cursor bitBound hcursorSize
  have hvalueCode : (binaryTermCode valueTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalueSize
  have hproductCode : (binaryTermCode productTerm).length <=
      numeralCode + numeralCode +
        binaryFunctionTermCodeOverhead Language.Mul.mul := by
    have hraw := paMulTerm_code_length_le indexTerm widthTerm
    simpa only [productTerm, fixedWidthIndexWidthTerm] using
      hraw.trans (by omega)
  have hleftIndexCodeRaw := paAddTerm_code_length_le
    (Rew.shift productTerm) (&0 : ValuationTerm)
  have hleftIndexCode :
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
      2 * (numeralCode + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) +
        (binaryTermCode (&0 : ValuationTerm)).length +
          binaryFunctionTermCodeOverhead Language.Add.add := by
    unfold fixedWidthLeftBitIndexTerm
    change (binaryTermCode
      (paAddTerm (Rew.shift productTerm) (&0 : ValuationTerm))).length <= _
    exact hleftIndexCodeRaw.trans (by
      have hshifted := binaryTermCode_shift_length_le productTerm
      omega)
  have hleftValueCode :
      (binaryTermCode (fixedWidthLeftBitValueTerm tableTerm)).length <=
        2 * numeralCode := by
    unfold fixedWidthLeftBitValueTerm
    exact (binaryTermCode_shift_length_le tableTerm).trans
      (Nat.mul_le_mul_left 2 htableCode)
  have hrightValueCode :
      (binaryTermCode (fixedWidthRightBitValueTerm valueTerm)).length <=
        2 * numeralCode := by
    unfold fixedWidthRightBitValueTerm
    exact (binaryTermCode_shift_length_le valueTerm).trans
      (Nat.mul_le_mul_left 2 hvalueCode)
  have hcodeCeilings :
      numeralCode <= additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
          additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <=
          additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound /\
      (binaryTermCode fixedWidthRightBitIndexTerm).length <=
          additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <=
          additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound := by
    unfold additiveTokenCellFixedWidthEntryTermCodeCeiling
    dsimp only [numeralCode]
    constructor
    · omega
    constructor
    · exact hleftIndexCode.trans (by omega)
    constructor
    · exact hleftValueCode.trans (by omega)
    constructor
    · omega
    · exact hrightValueCode.trans (by omega)
  apply
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_uniformCeiling
      zeroValuation tableTerm widthTerm indexTerm valueTerm coordinate
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthValue.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · simpa only [indexTerm, termValue_shortBinaryNumeralTerm] using
      hcursorValue.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · simp [zeroValuation,
      FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation]
  · simpa only [tableTerm, termValue_shortBinaryNumeralTerm] using
      htableSize.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthSize.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · simpa only [indexTerm, termValue_shortBinaryNumeralTerm] using
      hcursorSize.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · simpa only [valueTerm, termValue_shortBinaryNumeralTerm] using
      hvalueSize.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · exact hcodeCeilings.2.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega)
  · exact hcodeCeilings.2.2.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega)
  · exact hcodeCeilings.2.2.2.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega)
  · exact hcodeCeilings.2.2.2.2.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega)
  · exact htableCode.trans (hcodeCeilings.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega))
  · exact hwidthCode.trans (hcodeCeilings.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega))
  · exact hindexCode.trans (hcodeCeilings.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega))
  · exact hvalueCode.trans (hcodeCeilings.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega))
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  · rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value

theorem
    additiveTokenCellFixedWidthEntryAtClosedValueTermPayloadPolynomial_le_fixed
    (tokenTable width cursor numericBound bitBound : Nat)
    (valueTerm : ValuationTerm)
    (hwidthValue : width <= numericBound)
    (hcursorValue : cursor <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size (termValue zeroValuation valueTerm) <= bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound)
    (hvalueClosed : valueTerm.freeVariables = ∅) :
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        zeroValuation (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm cursor)
          valueTerm <=
      additiveTokenCellFixedWidthEntryPayloadPolynomial
        numericBound bitBound := by
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let indexTerm := shortBinaryNumeralTerm cursor
  let productTerm := fixedWidthIndexWidthTerm widthTerm indexTerm
  let coordinate := additiveTokenCellFixedWidthEntryCoordinate
    numericBound bitBound
  have htableCode : (binaryTermCode tableTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope tokenTable bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope width bitBound hwidthSize
  have hindexCode : (binaryTermCode indexTerm).length <= numeralCode :=
    binaryNumeralTerm_code_length_le_envelope cursor bitBound hcursorSize
  have hproductCode : (binaryTermCode productTerm).length <=
      numeralCode + numeralCode +
        binaryFunctionTermCodeOverhead Language.Mul.mul := by
    have hraw := paMulTerm_code_length_le indexTerm widthTerm
    simpa only [productTerm, fixedWidthIndexWidthTerm] using
      hraw.trans (by omega)
  have hleftIndexCodeRaw := paAddTerm_code_length_le
    (Rew.shift productTerm) (&0 : ValuationTerm)
  have hleftIndexCode :
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
      2 * (numeralCode + numeralCode +
          binaryFunctionTermCodeOverhead Language.Mul.mul) +
        (binaryTermCode (&0 : ValuationTerm)).length +
          binaryFunctionTermCodeOverhead Language.Add.add := by
    unfold fixedWidthLeftBitIndexTerm
    change (binaryTermCode
      (paAddTerm (Rew.shift productTerm) (&0 : ValuationTerm))).length <= _
    exact hleftIndexCodeRaw.trans (by
      have hshifted := binaryTermCode_shift_length_le productTerm
      omega)
  have hleftValueCode :
      (binaryTermCode (fixedWidthLeftBitValueTerm tableTerm)).length <=
        2 * numeralCode := by
    unfold fixedWidthLeftBitValueTerm
    exact (binaryTermCode_shift_length_le tableTerm).trans
      (Nat.mul_le_mul_left 2 htableCode)
  have hrightValueCode :
      (binaryTermCode (fixedWidthRightBitValueTerm valueTerm)).length <=
        2 * numeralCode := by
    unfold fixedWidthRightBitValueTerm
    exact (binaryTermCode_shift_length_le valueTerm).trans
      (Nat.mul_le_mul_left 2 hvalueCode)
  have hcodeCeilings :
      numeralCode <= additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitIndexTerm widthTerm indexTerm)).length <=
          additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthLeftBitValueTerm tableTerm)).length <=
          additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound /\
      (binaryTermCode fixedWidthRightBitIndexTerm).length <=
          additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound /\
      (binaryTermCode
        (fixedWidthRightBitValueTerm valueTerm)).length <=
          additiveTokenCellFixedWidthEntryTermCodeCeiling bitBound := by
    unfold additiveTokenCellFixedWidthEntryTermCodeCeiling
    dsimp only [numeralCode]
    constructor
    · omega
    constructor
    · exact hleftIndexCode.trans (by omega)
    constructor
    · exact hleftValueCode.trans (by omega)
    constructor
    · omega
    · exact hrightValueCode.trans (by omega)
  apply
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_uniformCeiling
      zeroValuation tableTerm widthTerm indexTerm valueTerm coordinate
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthValue.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · simpa only [indexTerm, termValue_shortBinaryNumeralTerm] using
      hcursorValue.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · simp [zeroValuation,
      FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation]
  · simpa only [tableTerm, termValue_shortBinaryNumeralTerm] using
      htableSize.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · simpa only [widthTerm, termValue_shortBinaryNumeralTerm] using
      hwidthSize.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · simpa only [indexTerm, termValue_shortBinaryNumeralTerm] using
      hcursorSize.trans (by
        unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
        omega)
  · exact hvalueSize.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega)
  · exact hcodeCeilings.2.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega)
  · exact hcodeCeilings.2.2.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega)
  · exact hcodeCeilings.2.2.2.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega)
  · exact hcodeCeilings.2.2.2.2.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega)
  · exact htableCode.trans (hcodeCeilings.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega))
  · exact hwidthCode.trans (hcodeCeilings.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega))
  · exact hindexCode.trans (hcodeCeilings.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega))
  · exact hvalueCode.trans (hcodeCeilings.1.trans (by
      unfold coordinate additiveTokenCellFixedWidthEntryCoordinate
      omega))
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  · rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  · exact hvalueClosed

theorem additiveTokenCellThreeLeafAssembly_le_fullyUniform
    (numericBound bitBound : Nat)
    (cursorFormula successorFormula entryFormula : ValuationFormula)
    (hcursorVariables : cursorFormula.freeVariables ⊆ {0})
    (hsuccessorVariables : successorFormula.freeVariables ⊆ {0})
    (hentryVariables : entryFormula.freeVariables ⊆ {0})
    (hcursorCode : (binaryFormulaCode cursorFormula).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hsuccessorCode : (binaryFormulaCode successorFormula).length <=
      additiveTokenCellAtomicFormulaCodeEnvelope bitBound)
    (hentryCode : (binaryFormulaCode entryFormula).length <=
      additiveTokenCellEntryFormulaCodeEnvelope bitBound) :
    hybridConjunctionStructuralPayloadEnvelope zeroValuation cursorFormula
        (successorFormula ⋏ entryFormula)
        (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
        (hybridConjunctionStructuralPayloadEnvelope zeroValuation
          successorFormula entryFormula
          (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
          (additiveTokenCellFixedWidthEntryPayloadPolynomial
            numericBound bitBound)) <=
      additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound := by
  let innerFormula := successorFormula ⋏ entryFormula
  let atomicResource :=
    additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound
  let entryResource :=
    additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound
  let atomicCode := additiveTokenCellAtomicFormulaCodeEnvelope bitBound
  let entryCode := additiveTokenCellEntryFormulaCodeEnvelope bitBound
  let contextResource :=
    additiveTokenCellContextFormulaCodeSumEnvelope numericBound
  let syntaxResource :=
    additiveTokenCellAssemblySyntaxPolynomial numericBound bitBound
  let innerResource := hybridConjunctionStructuralPayloadEnvelope zeroValuation
    successorFormula entryFormula atomicResource entryResource
  have hinnerVariables : innerFormula.freeVariables ⊆ {0} := by
    dsimp only [innerFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hsuccessorVariables hentryVariables
  have houterVariables :
      (cursorFormula ⋏ innerFormula).freeVariables ⊆ {0} := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hcursorVariables hinnerVariables
  have hzero : zeroValuation 0 <= numericBound := by
    simp [zeroValuation,
      FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation]
  have hinnerContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext innerFormula.freeVariables zeroValuation) <=
        contextResource := by
    simpa only [contextResource] using
      valuationContextFormulaCodeSum_le_tokenCellEnvelope zeroValuation
        innerFormula numericBound hinnerVariables hzero
  have houterContext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (cursorFormula ⋏ innerFormula).freeVariables
            zeroValuation) <= contextResource := by
    simpa only [contextResource] using
      valuationContextFormulaCodeSum_le_tokenCellEnvelope zeroValuation
        (cursorFormula ⋏ innerFormula) numericBound houterVariables hzero
  have hinnerCodeRaw := binaryFormulaCode_and_length_le_local
    successorFormula entryFormula
  have hinnerCode : (binaryFormulaCode innerFormula).length <=
      atomicCode + entryCode + (binaryNatCode 4).length := by
    dsimp only [innerFormula] at hinnerCodeRaw ⊢
    omega
  have houterCodeRaw := binaryFormulaCode_and_length_le_local
    cursorFormula innerFormula
  have houterCode :
      (binaryFormulaCode (cursorFormula ⋏ innerFormula)).length <=
        2 * atomicCode + entryCode +
          2 * (binaryNatCode 4).length := by
    omega
  have hsyntaxOne : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold additiveTokenCellAssemblySyntaxPolynomial
    dsimp only
    omega
  have hcontextResource_le_syntax : contextResource <= syntaxResource := by
    dsimp only [contextResource, syntaxResource]
    unfold additiveTokenCellAssemblySyntaxPolynomial
    dsimp only
    omega
  have hatomicCode_le_syntax : atomicCode <= syntaxResource := by
    dsimp only [atomicCode, syntaxResource]
    unfold additiveTokenCellAssemblySyntaxPolynomial
    dsimp only
    omega
  have hentryCode_le_syntax : entryCode <= syntaxResource := by
    dsimp only [entryCode, syntaxResource]
    unfold additiveTokenCellAssemblySyntaxPolynomial
    dsimp only
    omega
  have hinnerCode_le_syntax :
      (binaryFormulaCode innerFormula).length <= syntaxResource :=
    hinnerCode.trans (by
      dsimp only [atomicCode, entryCode, syntaxResource]
      unfold additiveTokenCellAssemblySyntaxPolynomial
      dsimp only
      omega)
  have houterCode_le_syntax :
      (binaryFormulaCode (cursorFormula ⋏ innerFormula)).length <=
        syntaxResource :=
    houterCode.trans (by
      dsimp only [atomicCode, entryCode, syntaxResource]
      unfold additiveTokenCellAssemblySyntaxPolynomial
      dsimp only
      omega)
  have hinnerGeneral : innerResource <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
        entryResource := by
    dsimp only [innerResource]
    exact hybridConjunctionStructuralPayloadEnvelope_le_general zeroValuation
      successorFormula entryFormula atomicResource entryResource syntaxResource
      hsyntaxOne (hinnerContext.trans hcontextResource_le_syntax)
      (hsuccessorCode.trans hatomicCode_le_syntax)
      (hentryCode.trans hentryCode_le_syntax) hinnerCode_le_syntax
  have houterGeneral :
      hybridConjunctionStructuralPayloadEnvelope zeroValuation cursorFormula
          innerFormula atomicResource innerResource <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
          innerResource := by
    exact hybridConjunctionStructuralPayloadEnvelope_le_general zeroValuation
      cursorFormula innerFormula atomicResource innerResource syntaxResource
      hsyntaxOne (houterContext.trans hcontextResource_le_syntax)
      (hcursorCode.trans hatomicCode_le_syntax) hinnerCode_le_syntax
      houterCode_le_syntax
  change hybridConjunctionStructuralPayloadEnvelope zeroValuation cursorFormula
      innerFormula atomicResource innerResource <=
    additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound
  apply houterGeneral.trans
  unfold hybridConjunctionGeneralPayloadEnvelope at hinnerGeneral
  unfold hybridConjunctionGeneralPayloadEnvelope
    additiveTokenCellFullyUniformPayloadPolynomial
  dsimp only [atomicResource, entryResource, syntaxResource, innerResource]
    at hinnerGeneral ⊢
  omega

def additiveTokenCellShortNumeralsFixedChildrenEnvelope
    (tokenTable width tokenCount cursor value next numericBound bitBound : Nat) :
    Nat :=
  additiveTokenCellAtValuationResourceEnvelope
    (shortBinaryNumeralTerm tokenTable)
    (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm cursor)
    (shortBinaryNumeralTerm value)
    (shortBinaryNumeralTerm next)
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound)
    (additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound)

theorem
    compactAdditiveTokenCellShortNumeralsOpenEntryStructuralPayloadPolynomial_le_fixedChildren
    (tokenTable width tokenCount cursor value next numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hcursorValue : cursor <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hnextSize : Nat.size next <= bitBound) :
    compactAdditiveTokenCellAtValuationOpenEntryStructuralPayloadPolynomial
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm cursor)
        (shortBinaryNumeralTerm value)
        (shortBinaryNumeralTerm next) <=
      additiveTokenCellShortNumeralsFixedChildrenEnvelope tokenTable width
        tokenCount cursor value next numericBound bitBound := by
  unfold compactAdditiveTokenCellAtValuationOpenEntryStructuralPayloadPolynomial
    additiveTokenCellShortNumeralsFixedChildrenEnvelope
  apply additiveTokenCellAtValuationResourceEnvelope_mono
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm cursor)
    (shortBinaryNumeralTerm value) (shortBinaryNumeralTerm next)
  · exact additiveTokenCellCursorPayloadPolynomial_le_fixed cursor tokenCount
      numericBound bitBound hcursorSize htokenCountSize
  · exact additiveTokenCellSuccessorPayloadPolynomial_le_fixed cursor next
      numericBound bitBound hcursorSize hnextSize
  · exact additiveTokenCellFixedWidthEntryPayloadPolynomial_le_fixed
      tokenTable width cursor value numericBound bitBound hwidthValue hcursorValue
      htableSize hwidthSize hcursorSize hvalueSize

theorem additiveTokenCellShortNumeralsFixedChildrenEnvelope_le_fullyUniform
    (tokenTable width tokenCount cursor value next numericBound bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hnextSize : Nat.size next <= bitBound) :
    additiveTokenCellShortNumeralsFixedChildrenEnvelope tokenTable width
        tokenCount cursor value next numericBound bitBound <=
      additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let countTerm := shortBinaryNumeralTerm tokenCount
  let cursorTerm := shortBinaryNumeralTerm cursor
  let valueTerm := shortBinaryNumeralTerm value
  let nextTerm := shortBinaryNumeralTerm next
  let cursorFormula : ValuationFormula := “!!cursorTerm < !!countTerm”
  let successorFormula : ValuationFormula :=
    “!!nextTerm = !!cursorTerm + 1”
  let entryFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm cursorTerm valueTerm
  have hcursorCode :
      (binaryFormulaCode cursorFormula).length <=
        additiveTokenCellAtomicFormulaCodeEnvelope bitBound := by
    simpa only [cursorFormula, cursorTerm, countTerm] using
      additiveTokenCellCursorFormula_code_length_le_uniform cursor tokenCount
        bitBound hcursorSize htokenCountSize
  have hsuccessorCode :
      (binaryFormulaCode successorFormula).length <=
        additiveTokenCellAtomicFormulaCodeEnvelope bitBound := by
    simpa only [successorFormula, nextTerm, cursorTerm] using
      additiveTokenCellSuccessorFormula_code_length_le_uniform cursor next
        bitBound hcursorSize hnextSize
  have hentryCode :
      (binaryFormulaCode entryFormula).length <=
        additiveTokenCellEntryFormulaCodeEnvelope bitBound := by
    simpa only [entryFormula, tableTerm, widthTerm, cursorTerm, valueTerm] using
      additiveTokenCellEntryFormula_code_length_le_uniform tokenTable width
        cursor value bitBound htableSize hwidthSize hcursorSize hvalueSize
  have hcursorClosed : cursorTerm.freeVariables = ∅ := by
    dsimp only [cursorTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty cursor
  have hcountClosed : countTerm.freeVariables = ∅ := by
    dsimp only [countTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hcursorVariables : cursorFormula.freeVariables ⊆ {0} := by
    have hclosed : cursorFormula.freeVariables = ∅ := by
      dsimp only [cursorFormula]
      simp [hcursorClosed, hcountClosed]
    rw [hclosed]
    exact Finset.empty_subset _
  have hsuccessorVariables : successorFormula.freeVariables ⊆ {0} := by
    have hnextClosed : nextTerm.freeVariables = ∅ := by
      dsimp only [nextTerm]
      exact shortBinaryNumeralTerm_freeVariables_eq_empty next
    have hclosed : successorFormula.freeVariables = ∅ := by
      dsimp only [successorFormula]
      simp [hnextClosed, arithmeticAddTerm_freeVariables, hcursorClosed,
        arithmeticOneTerm_freeVariables_eq_empty]
    rw [hclosed]
    exact Finset.empty_subset _
  have hentryVariables : entryFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      tableTerm widthTerm cursorTerm valueTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width) (by
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp)
      (shortBinaryNumeralTerm_freeVariables_eq_empty value)
  have hassembly := additiveTokenCellThreeLeafAssembly_le_fullyUniform
    numericBound bitBound cursorFormula successorFormula entryFormula
    hcursorVariables hsuccessorVariables hentryVariables hcursorCode
    hsuccessorCode hentryCode
  unfold additiveTokenCellShortNumeralsFixedChildrenEnvelope
    additiveTokenCellAtValuationResourceEnvelope
    compactAdditiveTokenCellAtValuationStructuralPayloadEnvelope
  dsimp only [tableTerm, widthTerm, countTerm, cursorTerm, valueTerm, nextTerm,
    cursorFormula, successorFormula, entryFormula]
  exact hassembly

theorem
    compactAdditiveTokenCellShortNumeralsOpenEntryStructuralPayloadPolynomial_le_fullyUniform
    (tokenTable width tokenCount cursor value next numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hcursorValue : cursor <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hnextSize : Nat.size next <= bitBound) :
    compactAdditiveTokenCellAtValuationOpenEntryStructuralPayloadPolynomial
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm cursor)
        (shortBinaryNumeralTerm value)
        (shortBinaryNumeralTerm next) <=
      additiveTokenCellFullyUniformPayloadPolynomial
        numericBound bitBound := by
  exact
    (compactAdditiveTokenCellShortNumeralsOpenEntryStructuralPayloadPolynomial_le_fixedChildren
      tokenTable width tokenCount cursor value next numericBound bitBound
      hwidthValue hcursorValue htableSize hwidthSize htokenCountSize hcursorSize
      hvalueSize hnextSize).trans
    (additiveTokenCellShortNumeralsFixedChildrenEnvelope_le_fullyUniform
      tokenTable width tokenCount cursor value next numericBound bitBound
      htableSize hwidthSize htokenCountSize hcursorSize hvalueSize hnextSize)

theorem
    compactAdditiveTokenCellShortNumeralsAtValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount cursor value next numericBound bitBound : Nat)
    (valueTerm : ValuationTerm)
    (hvalueTerm : valueTerm = shortBinaryNumeralTerm value)
    (hwidthValue : width <= numericBound)
    (hcursorValue : cursor <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hnextSize : Nat.size next <= bitBound)
    (hcell : CompactAdditiveTokenCell
      (termValue zeroValuation (shortBinaryNumeralTerm tokenTable))
      (termValue zeroValuation (shortBinaryNumeralTerm width))
      (termValue zeroValuation (shortBinaryNumeralTerm tokenCount))
      (termValue zeroValuation (shortBinaryNumeralTerm cursor))
      (termValue zeroValuation valueTerm)
      (termValue zeroValuation (shortBinaryNumeralTerm next))) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm cursor) valueTerm
          (shortBinaryNumeralTerm next) hcell) <=
      additiveTokenCellFullyUniformPayloadPolynomial
        numericBound bitBound := by
  have hvalueClosed : valueTerm.freeVariables = ∅ := by
    rw [hvalueTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty value
  have hopenEntry :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openEntry
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm cursor) valueTerm
      (shortBinaryNumeralTerm next)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty cursor)
      hvalueClosed (shortBinaryNumeralTerm_freeVariables_eq_empty next) hcell
  have hresource :=
    compactAdditiveTokenCellShortNumeralsOpenEntryStructuralPayloadPolynomial_le_fullyUniform
      tokenTable width tokenCount cursor value next numericBound bitBound
      hwidthValue hcursorValue htableSize hwidthSize htokenCountSize hcursorSize
      hvalueSize hnextSize
  have hresourceAtTerm :
      compactAdditiveTokenCellAtValuationOpenEntryStructuralPayloadPolynomial
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm cursor) valueTerm
          (shortBinaryNumeralTerm next) <=
        additiveTokenCellFullyUniformPayloadPolynomial
          numericBound bitBound := by
    simpa only [hvalueTerm] using hresource
  exact hopenEntry.trans hresourceAtTerm

theorem
    compactAdditiveTokenCellShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount cursor value next numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (hcursorValue : cursor <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hnextSize : Nat.size next <= bitBound)
    (hcell : CompactAdditiveTokenCell tokenTable width tokenCount cursor value next) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm cursor)
          (shortBinaryNumeralTerm value)
          (shortBinaryNumeralTerm next) (by
            simpa only [termValue_shortBinaryNumeralTerm] using hcell)) <=
      additiveTokenCellFullyUniformPayloadPolynomial
        numericBound bitBound := by
  have hopenEntry :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openEntry
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm cursor)
      (shortBinaryNumeralTerm value)
      (shortBinaryNumeralTerm next)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty cursor)
      (shortBinaryNumeralTerm_freeVariables_eq_empty value)
      (shortBinaryNumeralTerm_freeVariables_eq_empty next) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hcell)
  exact hopenEntry.trans
    (compactAdditiveTokenCellShortNumeralsOpenEntryStructuralPayloadPolynomial_le_fullyUniform
      tokenTable width tokenCount cursor value next numericBound bitBound
      hwidthValue hcursorValue htableSize hwidthSize htokenCountSize hcursorSize
      hvalueSize hnextSize)

theorem
    compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
    (tokenTable width tokenCount cursor next numericBound bitBound : Nat)
    (valueTerm : ValuationTerm)
    (hwidthValue : width <= numericBound)
    (hcursorValue : cursor <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size (termValue zeroValuation valueTerm) <= bitBound)
    (hnextSize : Nat.size next <= bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound)
    (hvalueClosed : valueTerm.freeVariables = ∅)
    (hcell : CompactAdditiveTokenCell
      (termValue zeroValuation (shortBinaryNumeralTerm tokenTable))
      (termValue zeroValuation (shortBinaryNumeralTerm width))
      (termValue zeroValuation (shortBinaryNumeralTerm tokenCount))
      (termValue zeroValuation (shortBinaryNumeralTerm cursor))
      (termValue zeroValuation valueTerm)
      (termValue zeroValuation (shortBinaryNumeralTerm next))) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
          (shortBinaryNumeralTerm tokenTable)
          (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm cursor) valueTerm
          (shortBinaryNumeralTerm next) hcell) <=
      additiveTokenCellFullyUniformPayloadPolynomial
        numericBound bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let countTerm := shortBinaryNumeralTerm tokenCount
  let cursorTerm := shortBinaryNumeralTerm cursor
  let nextTerm := shortBinaryNumeralTerm next
  let cursorFormula : ValuationFormula := “!!cursorTerm < !!countTerm”
  let successorFormula : ValuationFormula :=
    “!!nextTerm = !!cursorTerm + 1”
  let entryFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm cursorTerm valueTerm
  let atomicResource :=
    additiveTokenCellAtomicFixedPayloadPolynomial numericBound bitBound
  let entryResource :=
    additiveTokenCellFixedWidthEntryPayloadPolynomial numericBound bitBound
  have hopenEntry :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openEntry
      tableTerm widthTerm countTerm cursorTerm valueTerm nextTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty cursor)
      hvalueClosed (shortBinaryNumeralTerm_freeVariables_eq_empty next) hcell
  have hcursorResource :=
    additiveTokenCellCursorPayloadPolynomial_le_fixed cursor tokenCount
      numericBound bitBound hcursorSize htokenCountSize
  have hsuccessorResource :=
    additiveTokenCellSuccessorPayloadPolynomial_le_fixed cursor next
      numericBound bitBound hcursorSize hnextSize
  have hentryResource :=
    additiveTokenCellFixedWidthEntryAtClosedValueTermPayloadPolynomial_le_fixed
      tokenTable width cursor numericBound bitBound valueTerm hwidthValue
      hcursorValue htableSize hwidthSize hcursorSize hvalueSize hvalueCode
      hvalueClosed
  have hchildren :
      compactAdditiveTokenCellAtValuationOpenEntryStructuralPayloadPolynomial
          tableTerm widthTerm countTerm cursorTerm valueTerm nextTerm <=
        additiveTokenCellAtValuationResourceEnvelope tableTerm widthTerm
          countTerm cursorTerm valueTerm nextTerm atomicResource
          atomicResource entryResource := by
    unfold compactAdditiveTokenCellAtValuationOpenEntryStructuralPayloadPolynomial
    exact additiveTokenCellAtValuationResourceEnvelope_mono tableTerm
      widthTerm countTerm cursorTerm valueTerm nextTerm hcursorResource
      hsuccessorResource hentryResource
  have hcursorCode :
      (binaryFormulaCode cursorFormula).length <=
        additiveTokenCellAtomicFormulaCodeEnvelope bitBound := by
    simpa only [cursorFormula, cursorTerm, countTerm] using
      additiveTokenCellCursorFormula_code_length_le_uniform cursor tokenCount
        bitBound hcursorSize htokenCountSize
  have hsuccessorCode :
      (binaryFormulaCode successorFormula).length <=
        additiveTokenCellAtomicFormulaCodeEnvelope bitBound := by
    simpa only [successorFormula, nextTerm, cursorTerm] using
      additiveTokenCellSuccessorFormula_code_length_le_uniform cursor next
        bitBound hcursorSize hnextSize
  have hentryCode :
      (binaryFormulaCode entryFormula).length <=
        additiveTokenCellEntryFormulaCodeEnvelope bitBound := by
    simpa only [entryFormula, tableTerm, widthTerm, cursorTerm] using
      additiveTokenCellEntryAtClosedValueTermFormula_code_length_le_uniform
        tokenTable width cursor bitBound valueTerm htableSize hwidthSize
        hcursorSize hvalueCode
  have hcursorVariables : cursorFormula.freeVariables ⊆ {0} := by
    have hclosed : cursorFormula.freeVariables = ∅ := by
      dsimp only [cursorFormula, cursorTerm, countTerm]
      simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
    rw [hclosed]
    simp
  have hsuccessorVariables : successorFormula.freeVariables ⊆ {0} := by
    have hclosed : successorFormula.freeVariables = ∅ := by
      dsimp only [successorFormula, nextTerm, cursorTerm]
      simp [shortBinaryNumeralTerm_freeVariables_eq_empty,
        arithmeticAddTerm_freeVariables,
        arithmeticOneTerm_freeVariables_eq_empty]
    rw [hclosed]
    simp
  have hentryVariables : entryFormula.freeVariables ⊆ {0} := by
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      tableTerm widthTerm cursorTerm valueTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width) (by
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp)
      hvalueClosed
  have hassembly := additiveTokenCellThreeLeafAssembly_le_fullyUniform
    numericBound bitBound cursorFormula successorFormula entryFormula
    hcursorVariables hsuccessorVariables hentryVariables hcursorCode
    hsuccessorCode hentryCode
  apply hopenEntry.trans
  apply hchildren.trans
  unfold additiveTokenCellAtValuationResourceEnvelope
    compactAdditiveTokenCellAtValuationStructuralPayloadEnvelope
  simpa only [tableTerm, widthTerm, countTerm, cursorTerm, nextTerm,
    cursorFormula, successorFormula, entryFormula, atomicResource,
    entryResource] using hassembly

#print axioms additiveTokenCellCursorPayloadPolynomial_le_fixed
#print axioms additiveTokenCellSuccessorPayloadPolynomial_le_fixed
#print axioms additiveTokenCellCursorFormula_code_length_le_uniform
#print axioms additiveTokenCellSuccessorFormula_code_length_le_uniform
#print axioms additiveTokenCellEntryFormula_code_length_le_uniform
#print axioms
  additiveTokenCellEntryAtClosedValueTermFormula_code_length_le_uniform
#print axioms
  compactAdditiveTokenCellAtClosedValueTermFormula_code_length_le_uniform
#print axioms
  compactAdditiveTokenCellAtClosedValueTermFormula_freeVariables_eq_empty
#print axioms additiveTokenCellFixedWidthEntryPayloadPolynomial_le_fixed
#print axioms
  additiveTokenCellFixedWidthEntryAtClosedValueTermPayloadPolynomial_le_fixed
#print axioms additiveTokenCellThreeLeafAssembly_le_fullyUniform
#print axioms
  compactAdditiveTokenCellShortNumeralsOpenEntryStructuralPayloadPolynomial_le_fullyUniform
#print axioms
  compactAdditiveTokenCellShortNumeralsAtValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
#print axioms
  compactAdditiveTokenCellShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
#print axioms
  compactAdditiveTokenCellShortNumeralsAtClosedValueTermExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform

end FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
