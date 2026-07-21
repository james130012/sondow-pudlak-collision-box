import integration.FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds

/-!
# Public structural resources for closed additive list headers

The header consists of one additive token cell and one closed addition bound.
Both children are compiled directly from the concrete layout graph.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds

private abbrev headerZeroValuation : Nat -> Nat :=
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

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (left right : ValuationTerm) :
    termValue headerZeroValuation ‘!!left + !!right’ =
      termValue headerZeroValuation left +
        termValue headerZeroValuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add headerZeroValuation ![left, right]

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

def parseValuationLeStructuralPayloadPolynomial
    (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables headerZeroValuation
  compilePositiveRelationPayloadPolynomial
      headerZeroValuation Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial
      headerZeroValuation Language.ORing.Rel.lt args +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert equalityFormula Gamma) +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert strictFormula Gamma) +
    FoundationCompactCertifiedContextProof.CertifiedPAContextProof.disjunctionFullAssemblyCost
      Gamma equalityFormula strictFormula

theorem valuationLeCertificate_structuralPayloadBound_le_public
    (leftTerm rightTerm : ValuationTerm)
    (hleft : leftTerm.freeVariables = ∅)
    (hright : rightTerm.freeVariables = ∅)
    (hle : termValue headerZeroValuation leftTerm <=
      termValue headerZeroValuation rightTerm) :
    hybridFormulaStructuralPayloadBound
        (valuationLeCertificate leftTerm rightTerm hle) <=
      parseValuationLeStructuralPayloadPolynomial leftTerm rightTerm := by
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change leftTerm.freeVariables ⊆ {0}
    rw [hleft]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change rightTerm.freeVariables ⊆ {0}
    rw [hright]
    simp
  have hequality :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      headerZeroValuation Language.Eq.eq args hfirst hsecond
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      headerZeroValuation Language.ORing.Rel.lt args hfirst hsecond
  by_cases heq : termValue headerZeroValuation leftTerm =
      termValue headerZeroValuation rightTerm
  · simp only [valuationLeCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold parseValuationLeStructuralPayloadPolynomial
    dsimp only [args, headerZeroValuation] at hequality hstrict ⊢
    omega
  · simp only [valuationLeCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold parseValuationLeStructuralPayloadPolynomial
    dsimp only [args, headerZeroValuation] at hequality hstrict ⊢
    omega

def compactAdditiveTokenCellClosedStructuralPayloadPolynomial
    (tokenTable width tokenCount cursor value next : Nat) : Nat :=
  compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
    (shortBinaryNumeralTerm tokenTable)
    (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm cursor)
    (shortBinaryNumeralTerm value)
    (shortBinaryNumeralTerm next)

theorem compactAdditiveTokenCellExplicitHybridCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount cursor value next : Nat)
    (hcell : CompactAdditiveTokenCell
      tokenTable width tokenCount cursor value next) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveTokenCellExplicitHybridCertificate
          tokenTable width tokenCount cursor value next hcell) <=
      compactAdditiveTokenCellClosedStructuralPayloadPolynomial
        tokenTable width tokenCount cursor value next := by
  let tokenTableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let tokenCountTerm := shortBinaryNumeralTerm tokenCount
  let cursorTerm := shortBinaryNumeralTerm cursor
  let valueTerm := shortBinaryNumeralTerm value
  let nextTerm := shortBinaryNumeralTerm next
  have hclosed (number : Nat) :
      (shortBinaryNumeralTerm number).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty number
  have hcellTerms : CompactAdditiveTokenCell
      (termValue headerZeroValuation tokenTableTerm)
      (termValue headerZeroValuation widthTerm)
      (termValue headerZeroValuation tokenCountTerm)
      (termValue headerZeroValuation cursorTerm)
      (termValue headerZeroValuation valueTerm)
      (termValue headerZeroValuation nextTerm) := by
    simpa only [tokenTableTerm, widthTerm, tokenCountTerm, cursorTerm,
      valueTerm, nextTerm, termValue_shortBinaryNumeralTerm] using hcell
  have hpublic :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm
      (hclosed tokenTable) (hclosed width) (hclosed tokenCount)
      (hclosed cursor) (hclosed value) (hclosed next) hcellTerms
  change hybridFormulaStructuralPayloadBound
      (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
        tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm
        hcellTerms) <= _
  unfold compactAdditiveTokenCellClosedStructuralPayloadPolynomial
  dsimp only [tokenTableTerm, widthTerm, tokenCountTerm, cursorTerm,
    valueTerm, nextTerm] at hpublic ⊢
  exact hpublic

def compactAdditiveListHeaderStructuralPayloadPolynomial
    (tokenTable width tokenCount start count bodyStart : Nat) : Nat :=
  let cellFormula := compactAdditiveTokenCellClosedFormula
    tokenTable width tokenCount start count bodyStart
  let leftTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bodyStart) +
      !!(shortBinaryNumeralTerm count)’
  let boundFormula : ValuationFormula :=
    “!!leftTerm ≤ !!(shortBinaryNumeralTerm tokenCount)”
  hybridConjunctionStructuralPayloadEnvelope headerZeroValuation
    cellFormula boundFormula
    (compactAdditiveTokenCellClosedStructuralPayloadPolynomial
      tokenTable width tokenCount start count bodyStart)
    (parseValuationLeStructuralPayloadPolynomial leftTerm
      (shortBinaryNumeralTerm tokenCount))

theorem compactAdditiveListHeaderExplicitHybridCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount start count bodyStart : Nat)
    (hheader : CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveListHeaderExplicitHybridCertificate
          tokenTable width tokenCount start count bodyStart hheader) <=
      compactAdditiveListHeaderStructuralPayloadPolynomial
        tokenTable width tokenCount start count bodyStart := by
  let leftTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bodyStart) +
      !!(shortBinaryNumeralTerm count)’
  let cellCertificate := compactAdditiveTokenCellExplicitHybridCertificate
    tokenTable width tokenCount start count bodyStart hheader.1
  have hle : termValue headerZeroValuation leftTerm <=
      termValue headerZeroValuation (shortBinaryNumeralTerm tokenCount) := by
    simpa [leftTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd]
      using hheader.2
  let boundCertificate := valuationLeCertificate leftTerm
    (shortBinaryNumeralTerm tokenCount) hle
  have hleft : leftTerm.freeVariables = ∅ := by
    dsimp only [leftTerm]
    rw [arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright :
      (shortBinaryNumeralTerm tokenCount).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hcell :=
    compactAdditiveTokenCellExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount start count bodyStart hheader.1
  have hbound := valuationLeCertificate_structuralPayloadBound_le_public
    leftTerm (shortBinaryNumeralTerm tokenCount) hleft hright hle
  have hparts := hybridConjunctionStructuralPayloadBound_le_envelope
    cellCertificate boundCertificate _ _ hcell hbound
  simpa only [compactAdditiveListHeaderExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveListHeaderStructuralPayloadPolynomial,
    leftTerm, cellCertificate, boundCertificate] using hparts

#print axioms valuationLeCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveTokenCellExplicitHybridCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveListHeaderExplicitHybridCertificate_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds
