import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerLeafPublicBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerPublicBounds

/-!
# Public bounded-universal resource for fixed-width entries
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerLeafPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAUnaryAtomicTransport

private theorem binaryFunctionTerm_freeVariables
    {boundArity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
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

private theorem paMulTerm_freeVariables
    (left right : ValuationTerm) :
    (paMulTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  exact binaryFunctionTerm_freeVariables Language.Mul.mul left right

private theorem binaryRelationFormula_freeVariables
    {boundArity : Nat}
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem bShiftTerm_freeVariables_eq
    {boundArity : Nat}
    (term : LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    (Rew.bShift term).freeVariables = term.freeVariables := by
  ext candidate
  exact LO.FirstOrder.Semiterm.fvar?_bShift

private theorem embeddedSubstitution_freeVariables_subset_of_term_subset
    {arity boundArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty arity)
    (terms : Fin arity ->
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity)
    (vars : Finset Nat)
    (hterms : ∀ coordinate, (terms coordinate).freeVariables ⊆ vars) :
    ((Rewriting.emb (ξ := Nat) formula) ⇜ terms).freeVariables ⊆ vars := by
  intro candidate hcandidate
  have hsource := embeddedSubstitution_freeVariables_subset_atArity
    formula terms hcandidate
  rcases Finset.mem_biUnion.mp hsource with
    ⟨coordinate, _, hcoordinate⟩
  exact hterms coordinate hcoordinate

theorem fixedWidthBitBody_freeVariables_eq_empty_of_closed
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅) :
    (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm).freeVariables =
      ∅ := by
  let indexWidth := fixedWidthIndexWidthTerm widthTerm indexTerm
  let leftIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    LO.FirstOrder.Semiterm.func Language.ORing.Func.add
      ![Rew.bShift indexWidth, #0]
  let leftValue : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift tableTerm
  let rightIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
  let rightValue : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift valueTerm
  have hindexWidth : indexWidth.freeVariables = ∅ := by
    dsimp only [indexWidth]
    rw [fixedWidthIndexWidthTerm, paMulTerm_freeVariables, hindex, hwidth]
    simp
  have hshiftIndexWidth : (Rew.bShift indexWidth).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty indexWidth hindexWidth
  have hleftIndex : leftIndex.freeVariables = ∅ := by
    dsimp only [leftIndex]
    rw [binaryFunctionTerm_freeVariables, hshiftIndexWidth]
    simp
  have hleftValue : leftValue.freeVariables = ∅ := by
    dsimp only [leftValue]
    exact bShift_freeVariables_eq_empty_of_empty tableTerm htable
  have hrightIndex : rightIndex.freeVariables = ∅ := by
    simp [rightIndex]
  have hrightValue : rightValue.freeVariables = ∅ := by
    dsimp only [rightValue]
    exact bShift_freeVariables_eq_empty_of_empty valueTerm hvalue
  have hleftAtom :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      bitDef.val ![leftIndex, leftValue] (by
        intro coordinate
        cases coordinate using Fin.cases with
        | zero => exact hleftIndex
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero => exact hleftValue
            | succ coordinate => exact Fin.elim0 coordinate)
  have hrightAtom :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      bitDef.val ![rightIndex, rightValue] (by
        intro coordinate
        cases coordinate using Fin.cases with
        | zero => exact hrightIndex
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero => exact hrightValue
            | succ coordinate => exact Fin.elim0 coordinate)
  unfold fixedWidthBitBody binaryBitAtomAtTerms
  dsimp only [indexWidth, leftIndex, leftValue, rightIndex, rightValue] at hleftAtom hrightAtom ⊢
  simp only [LogicalConnective.iff,
    LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_imp,
    hleftAtom, hrightAtom, Finset.empty_union]

theorem fixedWidthBitBody_freeVariables_subset_singleton_of_openIndex
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    (fixedWidthBitBody tableTerm widthTerm indexTerm
      valueTerm).freeVariables ⊆ {0} := by
  let indexWidth := fixedWidthIndexWidthTerm widthTerm indexTerm
  let leftIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    LO.FirstOrder.Semiterm.func Language.ORing.Func.add
      ![Rew.bShift indexWidth, #0]
  let leftValue : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift tableTerm
  let rightIndex : LO.FirstOrder.ArithmeticSemiterm Nat 1 := #0
  let rightValue : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    Rew.bShift valueTerm
  have hindexWidth : indexWidth.freeVariables ⊆ {0} := by
    dsimp only [indexWidth]
    rw [fixedWidthIndexWidthTerm, paMulTerm_freeVariables, hwidth]
    simpa using hindex
  have hleftIndex : leftIndex.freeVariables ⊆ {0} := by
    dsimp only [leftIndex]
    rw [binaryFunctionTerm_freeVariables, bShiftTerm_freeVariables_eq]
    exact Finset.union_subset hindexWidth (by simp)
  have hleftValue : leftValue.freeVariables ⊆ {0} := by
    dsimp only [leftValue]
    rw [bShiftTerm_freeVariables_eq, htable]
    simp
  have hrightIndex : rightIndex.freeVariables ⊆ {0} := by
    simp [rightIndex]
  have hrightValue : rightValue.freeVariables ⊆ {0} := by
    dsimp only [rightValue]
    rw [bShiftTerm_freeVariables_eq, hvalue]
    simp
  have hleftAtom :=
    embeddedSubstitution_freeVariables_subset_of_term_subset
      bitDef.val ![leftIndex, leftValue] ({0} : Finset Nat) (by
        intro coordinate
        cases coordinate using Fin.cases with
        | zero => exact hleftIndex
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero => exact hleftValue
            | succ coordinate => exact Fin.elim0 coordinate)
  have hrightAtom :=
    embeddedSubstitution_freeVariables_subset_of_term_subset
      bitDef.val ![rightIndex, rightValue] ({0} : Finset Nat) (by
        intro coordinate
        cases coordinate using Fin.cases with
        | zero => exact hrightIndex
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero => exact hrightValue
            | succ coordinate => exact Fin.elim0 coordinate)
  unfold fixedWidthBitBody binaryBitAtomAtTerms
  dsimp only [indexWidth, leftIndex, leftValue, rightIndex, rightValue] at hleftAtom hrightAtom ⊢
  simpa only [LogicalConnective.iff,
    LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_imp] using
      Finset.union_subset
        (Finset.union_subset hleftAtom hrightAtom)
        (Finset.union_subset hrightAtom hleftAtom)

#print axioms fixedWidthBitBody_freeVariables_eq_empty_of_closed

theorem fixedWidthUniversalOuterFormula_freeVariables_eq_empty_of_closed
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅) :
    (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm)
      (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm)).freeVariables =
      ∅ := by
  have hshiftWidth : (Rew.bShift widthTerm).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty widthTerm hwidth
  have hbody := fixedWidthBitBody_freeVariables_eq_empty_of_closed
    tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  simp only [LO.FirstOrder.Semiformula.freeVariables_all,
    termBoundedUniversalBody, LO.FirstOrder.Semiformula.freeVariables_imp,
    termBoundFormula, finiteCaseLessThanFormula,
    binaryRelationFormula_freeVariables, hshiftWidth, hbody]
  simp

theorem
    fixedWidthUniversalOuterFormula_freeVariables_subset_singleton_of_openIndex
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm)
      (fixedWidthBitBody tableTerm widthTerm indexTerm
        valueTerm)).freeVariables ⊆ {0} := by
  have hshiftWidth : (Rew.bShift widthTerm).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty widthTerm hwidth
  have hbody :=
    fixedWidthBitBody_freeVariables_subset_singleton_of_openIndex
      tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  simp only [LO.FirstOrder.Semiformula.freeVariables_all,
    termBoundedUniversalBody, LO.FirstOrder.Semiformula.freeVariables_imp,
    termBoundFormula, finiteCaseLessThanFormula,
    binaryRelationFormula_freeVariables, hshiftWidth,
    Finset.empty_union]
  simpa using hbody

theorem fixedWidthUniversalShiftedOuterContext_card_le_one_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    let outerFormula := ∀⁰ termBoundedUniversalBody
      (Rew.bShift widthTerm)
      (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm)
    ((valuationContext outerFormula.freeVariables valuation).image
      Rewriting.shift).card <= 1 := by
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm)
    (fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm)
  have houterVars : outerFormula.freeVariables ⊆ {0} := by
    dsimp only [outerFormula]
    exact
      fixedWidthUniversalOuterFormula_freeVariables_subset_singleton_of_openIndex
        tableTerm widthTerm indexTerm valueTerm
        htable hwidth hindex hvalue
  have houterCard : outerFormula.freeVariables.card <= 1 := by
    have hcard := Finset.card_le_card houterVars
    simpa only [Finset.card_singleton] using hcard
  have hcontextCard :
      (valuationContext outerFormula.freeVariables valuation).card <=
        outerFormula.freeVariables.card := by
    unfold valuationContext
    exact Finset.card_image_le
  have hshiftedCard :
      ((valuationContext outerFormula.freeVariables valuation).image
        Rewriting.shift).card <=
        (valuationContext outerFormula.freeVariables valuation).card :=
    Finset.card_image_le
  exact hshiftedCard.trans (hcontextCard.trans houterCard)

#print axioms fixedWidthUniversalOuterFormula_freeVariables_eq_empty_of_closed
#print axioms
  fixedWidthUniversalOuterFormula_freeVariables_subset_singleton_of_openIndex
#print axioms
  fixedWidthUniversalShiftedOuterContext_card_le_one_of_openIndex

theorem contextualBranchesUnderBoundPayloadEnvelope_mono
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat)
    (target : LO.FirstOrder.ArithmeticProposition)
    (oldResource newResource : Nat)
    (hresource : oldResource ≤ newResource) :
    contextualBranchesUnderBoundPayloadEnvelope Gamma bound target oldResource ≤
      contextualBranchesUnderBoundPayloadEnvelope Gamma bound target newResource := by
  unfold contextualBranchesUnderBoundPayloadEnvelope
  omega

theorem compileContextualTermBoundedUniversalPayloadEnvelope_mono
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat)
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (oldBoundResource oldBranchResource
      newBoundResource newBranchResource : Nat)
    (hbound : oldBoundResource ≤ newBoundResource)
    (hbranch : oldBranchResource ≤ newBranchResource) :
    compileContextualTermBoundedUniversalPayloadEnvelope Gamma bound boundTerm
        body oldBoundResource oldBranchResource ≤
      compileContextualTermBoundedUniversalPayloadEnvelope Gamma bound boundTerm
        body newBoundResource newBranchResource := by
  unfold compileContextualTermBoundedUniversalPayloadEnvelope
    relationTransportImplicationStructuralPayloadBound
  dsimp only
  omega

#print axioms contextualBranchesUnderBoundPayloadEnvelope_mono
#print axioms compileContextualTermBoundedUniversalPayloadEnvelope_mono

def fixedWidthUniversalStructuralPayloadPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (fixedWidthBitBranchesStructuralPayloadPolynomial valuation tableTerm
      widthTerm indexTerm valueTerm)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift widthTerm) body
    (compileClosedShiftedBoundEqualityPayloadPolynomial valuation widthTerm)
    branchResource

theorem
    fixedWidthUniversalHybridCertificate_structuralPayloadBound_le_publicPolynomial
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tableTerm).testBit
          (termValue valuation indexTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation valueTerm).testBit bitIndex) :
    hybridFormulaStructuralPayloadBound
        (fixedWidthUniversalHybridCertificate valuation tableTerm widthTerm
          indexTerm valueTerm hbits) ≤
      fixedWidthUniversalStructuralPayloadPolynomial valuation tableTerm
        widthTerm indexTerm valueTerm := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift widthTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let bound := termValue valuation widthTerm
  let branches := fixedWidthBitHybridBranches valuation tableTerm widthTerm
    indexTerm valueTerm bound hbits
  let oldBranchCore := hybridBranchesStructuralPayloadEnvelope
    bound outerVariables branches
  let newBranchCore := fixedWidthBitBranchesStructuralPayloadPolynomial
    valuation tableTerm widthTerm indexTerm valueTerm
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldBranchCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newBranchCore
  let oldBoundResource := compileShiftedBoundEqualityPayloadResource
    valuation outerVariables widthTerm
  let newBoundResource := compileClosedShiftedBoundEqualityPayloadPolynomial
    valuation widthTerm
  have houter : outerVariables = ∅ := by
    dsimp only [outerVariables, outerFormula, body]
    exact fixedWidthUniversalOuterFormula_freeVariables_eq_empty_of_closed
      tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hboundResource : oldBoundResource ≤ newBoundResource := by
    dsimp only [oldBoundResource, newBoundResource]
    rw [houter]
    exact compileShiftedBoundEqualityPayloadResource_le_closedPolynomial
      valuation widthTerm hwidth
  have hbranchCore : oldBranchCore ≤ newBranchCore := by
    dsimp only [oldBranchCore, newBranchCore, bound, branches]
    rw [houter]
    exact
      fixedWidthBitBranchesStructuralPayloadEnvelope_le_publicPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm htable hwidth
        hindex hvalue hbits
  have hbranchResource : oldBranchResource ≤ newBranchResource := by
    exact contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldBranchCore newBranchCore hbranchCore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift widthTerm) body
    oldBoundResource oldBranchResource newBoundResource newBranchResource
    hboundResource hbranchResource
  simpa only [fixedWidthUniversalHybridCertificate,
    hybridFormulaStructuralPayloadBound,
    fixedWidthUniversalStructuralPayloadPolynomial,
    body, outerFormula, outerVariables, Gamma, bound, branches,
    oldBranchCore, newBranchCore, oldBranchResource, newBranchResource,
    oldBoundResource, newBoundResource] using htotal

#print axioms
  fixedWidthUniversalHybridCertificate_structuralPayloadBound_le_publicPolynomial

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
