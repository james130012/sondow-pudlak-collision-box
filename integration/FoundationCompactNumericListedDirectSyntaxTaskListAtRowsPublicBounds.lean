import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutPublicBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for one selected syntax-task row

The index guard, two boundary-table entries, three-cell task layout, and two
bounded cursor witnesses are exposed as a proof-free structural envelope.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayoutPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
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
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (left right : ValuationTerm) :
    termValue atRowsZeroValuation ‘!!left + !!right’ =
      termValue atRowsZeroValuation left +
        termValue atRowsZeroValuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add atRowsZeroValuation ![left, right]

private theorem termValue_arithmeticOne :
    termValue atRowsZeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one atRowsZeroValuation ![]

def compactAdditiveSyntaxTaskListAtRowsGuardPayloadPolynomial
    (count : Nat) (indexTerm : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadPolynomial atRowsZeroValuation
    Language.ORing.Rel.lt
    ![indexTerm, shortBinaryNumeralTerm count]

theorem strictCertificate_structuralPayloadBound_le_public
    (count : Nat) (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hstrict : termValue atRowsZeroValuation indexTerm < count) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.strictCertificate
          indexTerm (shortBinaryNumeralTerm count) (by
            simpa [termValue_shortBinaryNumeralTerm] using hstrict)) ≤
      compactAdditiveSyntaxTaskListAtRowsGuardPayloadPolynomial count
        indexTerm := by
  have hleft : indexTerm.freeVariables ⊆ {0} := by
    rw [hindexClosed]
    simp
  have hright :
      (shortBinaryNumeralTerm count).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      atRowsZeroValuation Language.ORing.Rel.lt
      ![indexTerm, shortBinaryNumeralTerm count] hleft hright
  simpa only [
    FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.strictCertificate,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveSyntaxTaskListAtRowsGuardPayloadPolynomial] using hpublic

noncomputable def
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope
    (tokenTable width tokenCount boundaryTable count index
      kind binderArity repeatCount : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount) : Nat := by
  let left := Classical.choose hgraph.2
  have hleftData := Classical.choose_spec hgraph.2
  let right := Classical.choose hleftData.2
  have hrightData := Classical.choose_spec hleftData.2
  let boundaryTerm := shortBinaryNumeralTerm boundaryTable
  let countTerm := shortBinaryNumeralTerm tokenCount
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let nextIndexTerm := successorIndexTerm indexTerm
  let leftFormula := compactFixedWidthEntryAtValuationFormula boundaryTerm
    countTerm indexTerm leftTerm
  let rightFormula := compactFixedWidthEntryAtValuationFormula boundaryTerm
    countTerm nextIndexTerm rightTerm
  let layoutFormula := compactSyntaxTaskDirectLayoutAtValuationTermsFormula
    tokenTable width tokenCount left right kindTerm binderArityTerm
    repeatCountTerm
  let leftResource :=
    compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
      atRowsZeroValuation boundaryTerm countTerm indexTerm leftTerm
  let rightResource :=
    compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
      atRowsZeroValuation boundaryTerm countTerm nextIndexTerm rightTerm
  let layoutResource :=
    compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope tokenTable
      width tokenCount left right kind binderArity repeatCount kindTerm
      binderArityTerm repeatCountTerm hrightData.2.2.2
  let rightLayoutResource := transparentHybridConjunctionPayloadEnvelope
    atRowsZeroValuation rightFormula layoutFormula rightResource
    layoutResource
  let terminalResource := transparentHybridConjunctionPayloadEnvelope
    atRowsZeroValuation leftFormula (rightFormula ⋏ layoutFormula)
    leftResource rightLayoutResource
  let values : Fin 2 -> Nat := ![right, left]
  let witnessResource := explicitBoundedWitnessHybridStructuralPayloadEnvelope
    atRowsZeroValuation tokenCount
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
      width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
      repeatCountTerm) values terminalResource
  let guardFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm count)”
  let witnessFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable
      width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
      repeatCountTerm
  exact transparentHybridConjunctionPayloadEnvelope atRowsZeroValuation
    guardFormula witnessFormula
    (compactAdditiveSyntaxTaskListAtRowsGuardPayloadPolynomial count indexTerm)
    witnessResource

theorem
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount boundaryTable count index
      kind binderArity repeatCount : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hkindClosed : kindTerm.freeVariables = ∅)
    (hbinderClosed : binderArityTerm.freeVariables = ∅)
    (hrepeatClosed : repeatCountTerm.freeVariables = ∅)
    (hindexValue : termValue atRowsZeroValuation indexTerm = index)
    (hkindValue : ∀ valuation, termValue valuation kindTerm = kind)
    (hbinderArityValue : ∀ valuation,
      termValue valuation binderArityTerm = binderArity)
    (hrepeatCountValue : ∀ valuation,
      termValue valuation repeatCountTerm = repeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount boundaryTable count index kind
          binderArity repeatCount indexTerm kindTerm binderArityTerm
          repeatCountTerm hindexValue hkindValue hbinderArityValue
          hrepeatCountValue hgraph) ≤
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope
        tokenTable width tokenCount boundaryTable count index kind binderArity
        repeatCount indexTerm kindTerm binderArityTerm repeatCountTerm
        hgraph := by
  let left := Classical.choose hgraph.2
  have hleftData := Classical.choose_spec hgraph.2
  let right := Classical.choose hleftData.2
  have hrightData := Classical.choose_spec hleftData.2
  have hleftLe := hleftData.1
  have hrightLe := hrightData.1
  have hleftEntry := hrightData.2.1
  have hrightEntry := hrightData.2.2.1
  have hlayout := hrightData.2.2.2
  let boundaryTerm := shortBinaryNumeralTerm boundaryTable
  let countTerm := shortBinaryNumeralTerm tokenCount
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let nextIndexTerm := successorIndexTerm indexTerm
  let leftCertificate :
      CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
        (compactFixedWidthEntryAtValuationFormula boundaryTerm countTerm
          indexTerm leftTerm) :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsZeroValuation boundaryTerm countTerm indexTerm leftTerm (by
        simpa [left, right, boundaryTerm, countTerm, leftTerm,
          termValue_shortBinaryNumeralTerm, hindexValue,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using hleftEntry)
  let rightCertificate :
      CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
        (compactFixedWidthEntryAtValuationFormula boundaryTerm countTerm
          nextIndexTerm rightTerm) :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      atRowsZeroValuation boundaryTerm countTerm nextIndexTerm rightTerm (by
        simpa [left, right, boundaryTerm, countTerm, rightTerm,
          nextIndexTerm, successorIndexTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne, hindexValue,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using hrightEntry)
  let layoutCertificate :
      CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
        (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
          tokenCount left right kindTerm binderArityTerm repeatCountTerm) :=
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
      tokenTable width tokenCount left right kind binderArity repeatCount
      kindTerm binderArityTerm repeatCountTerm hkindValue hbinderArityValue
      hrepeatCountValue (by simpa [left, right] using hlayout)
  have hboundary : boundaryTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  have hcountTerm : countTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hleftTerm : leftTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty left
  have hrightTerm : rightTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty right
  have hnextIndex : nextIndexTerm.freeVariables = ∅ := by
    dsimp only [nextIndexTerm, successorIndexTerm]
    rw [arithmeticAddTerm_freeVariables, hindexClosed,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hleftResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      atRowsZeroValuation boundaryTerm countTerm indexTerm leftTerm hboundary
      hcountTerm hindexClosed hleftTerm (by
        simpa [left, right, boundaryTerm, countTerm, leftTerm,
          termValue_shortBinaryNumeralTerm, hindexValue,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using hleftEntry)
  have hrightResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      atRowsZeroValuation boundaryTerm countTerm nextIndexTerm rightTerm
      hboundary hcountTerm hnextIndex hrightTerm (by
        simpa [left, right, boundaryTerm, countTerm, rightTerm,
          nextIndexTerm, successorIndexTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne, hindexValue,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using hrightEntry)
  have hlayoutResource :=
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout_structuralPayloadBound_le_public
      tokenTable width tokenCount left right kind binderArity repeatCount
      kindTerm binderArityTerm repeatCountTerm hkindClosed hbinderClosed
      hrepeatClosed hkindValue hbinderArityValue hrepeatCountValue
      (by simpa [left, right] using hlayout)
  let rightLayout :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      rightCertificate layoutCertificate
  have hrightLayout := transparentHybridConjunctionPayloadBound_le
    rightCertificate layoutCertificate _ _ hrightResource hlayoutResource
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      leftCertificate rightLayout
  have hterminalParts := transparentHybridConjunctionPayloadBound_le
    leftCertificate rightLayout _ _ hleftResource hrightLayout
  let values : Fin 2 -> Nat := ![right, left]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm right, shortBinaryNumeralTerm left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal :
      CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
        ((compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal
          tokenTable width tokenCount boundaryTable indexTerm kindTerm
          binderArityTerm repeatCountTerm) ⇜
            fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal_substitution_alignment
          tokenTable width tokenCount boundaryTable left right indexTerm
          kindTerm binderArityTerm repeatCountTerm).symm) terminalParts
  let terminalResource :=
    transparentHybridConjunctionPayloadEnvelope atRowsZeroValuation
        (compactFixedWidthEntryAtValuationFormula boundaryTerm countTerm
          indexTerm leftTerm)
        (compactFixedWidthEntryAtValuationFormula boundaryTerm countTerm
            nextIndexTerm rightTerm ⋏
          compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
            tokenCount left right kindTerm binderArityTerm repeatCountTerm)
        (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
          atRowsZeroValuation boundaryTerm countTerm indexTerm leftTerm)
        (transparentHybridConjunctionPayloadEnvelope atRowsZeroValuation
          (compactFixedWidthEntryAtValuationFormula boundaryTerm countTerm
            nextIndexTerm rightTerm)
          (compactSyntaxTaskDirectLayoutAtValuationTermsFormula tokenTable width
            tokenCount left right kindTerm binderArityTerm repeatCountTerm)
          (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
            atRowsZeroValuation boundaryTerm countTerm nextIndexTerm rightTerm)
          (compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope
            tokenTable width tokenCount left right kind binderArity repeatCount
            kindTerm binderArityTerm repeatCountTerm
            (by simpa [left, right] using hlayout)))
  have hterminal : hybridFormulaStructuralPayloadBound terminal ≤
      terminalResource := by
    simpa only [terminal, hybridFormulaStructuralPayloadBound, boundaryTerm,
      countTerm, leftTerm, rightTerm, nextIndexTerm, leftCertificate,
      rightCertificate, layoutCertificate, rightLayout, terminalParts] using
      hterminalParts
  have hbounds : ∀ coordinate, values coordinate ≤ tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact hrightLe
    · exact hleftLe
  have hinstalled :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
        width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
        repeatCountTerm)
      values hbounds terminal terminalResource hterminal
  let witness :
      CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
          tokenTable width tokenCount boundaryTable indexTerm kindTerm
          binderArityTerm repeatCountTerm) :=
    .cast (by
      unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
      rw [explicitBoundedWitnessFormula_two_eq])
      (buildExplicitBoundedWitnessHybridCertificate tokenCount
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
          width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
          repeatCountTerm) values hbounds terminal)
  have hwitness : hybridFormulaStructuralPayloadBound witness ≤
      explicitBoundedWitnessHybridStructuralPayloadEnvelope
        atRowsZeroValuation tokenCount
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
          width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
          repeatCountTerm) values terminalResource := by
    simpa only [witness, hybridFormulaStructuralPayloadBound] using hinstalled
  let guard :=
    FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.strictCertificate
      indexTerm (shortBinaryNumeralTerm count) (by
        simpa [termValue_shortBinaryNumeralTerm, hindexValue] using hgraph.1)
  have hguard := strictCertificate_structuralPayloadBound_le_public count
    indexTerm hindexClosed (by simpa [hindexValue] using hgraph.1)
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    guard witness
  have hparts := transparentHybridConjunctionPayloadBound_le
    guard witness _ _ hguard hwitness
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment
          tokenTable width tokenCount boundaryTable count indexTerm kindTerm
          binderArityTerm repeatCountTerm).symm parts) ≤ _
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, left, right, boundaryTerm,
    countTerm, leftTerm, rightTerm, nextIndexTerm, leftCertificate,
    rightCertificate, layoutCertificate, rightLayout, terminalParts, values,
    terminal, terminalResource, witness, guard, parts] using hparts

#print axioms strictCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds
