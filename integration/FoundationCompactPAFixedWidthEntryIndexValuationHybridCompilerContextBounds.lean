import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerBounds

/-!
# Small-context bounds for fixed-width bit leaves

The fixed-width bit leaf has four literal compiler resources and thirteen
small context assemblies.  This file bounds every assembly directly by one
syntax resource, with no proof payload as an input coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerBounds
open FoundationCompactPAContextCostPolynomialBounds

def formulaCodeSum
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) : Nat :=
  Gamma.sum fun formula => (binaryFormulaCode formula).length

theorem formulaCode_le_formulaCodeSum
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition}
    (hformula : formula ∈ Gamma) :
    (binaryFormulaCode formula).length <= formulaCodeSum Gamma := by
  unfold formulaCodeSum
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le (binaryFormulaCode candidate).length)
    hformula

private theorem shiftedTerm_freeVariables_eq_empty
    (term : ValuationTerm)
    (hclosed : term.freeVariables = ∅) :
    (Rew.shift term).freeVariables = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro candidate hcandidate
  rcases mem_freeVariables_shiftTerm term hcandidate with
    ⟨sourceIndex, hsource, _⟩
  rw [hclosed] at hsource
  simp at hsource

theorem shiftedTerm_freeVariables_subset_one
    (term : ValuationTerm)
    (hvars : term.freeVariables ⊆ {0}) :
    (Rew.shift term).freeVariables ⊆ {1} := by
  intro candidate hcandidate
  rcases mem_freeVariables_shiftTerm term hcandidate with
    ⟨sourceIndex, hsource, hcandidateEq⟩
  have hsourceZero : sourceIndex = 0 := by
    simpa only [Finset.mem_singleton] using hvars hsource
  subst sourceIndex
  simpa only [Finset.mem_singleton] using hcandidateEq

private theorem binaryFunction_freeVariables
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

private theorem paAddTerm_freeVariables
    (left right : ValuationTerm) :
    (paAddTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseAddTerm_eq_paAddTerm]
  exact binaryFunction_freeVariables Language.Add.add left right

private theorem paMulTerm_freeVariables
    (left right : ValuationTerm) :
    (paMulTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  exact binaryFunction_freeVariables Language.Mul.mul left right

theorem fixedWidthBitTerms_freeVariables_of_closed
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅) :
    (fixedWidthLeftBitIndexTerm widthTerm indexTerm).freeVariables = {0} ∧
      (fixedWidthLeftBitValueTerm tableTerm).freeVariables = ∅ ∧
      fixedWidthRightBitIndexTerm.freeVariables = {0} ∧
      (fixedWidthRightBitValueTerm valueTerm).freeVariables = ∅ := by
  have hindexWidth :
      (fixedWidthIndexWidthTerm widthTerm indexTerm).freeVariables = ∅ := by
    rw [fixedWidthIndexWidthTerm, paMulTerm_freeVariables, hindex, hwidth]
    simp
  have hshiftIndexWidth := shiftedTerm_freeVariables_eq_empty
    (fixedWidthIndexWidthTerm widthTerm indexTerm) hindexWidth
  have hshiftTable := shiftedTerm_freeVariables_eq_empty tableTerm htable
  have hshiftValue := shiftedTerm_freeVariables_eq_empty valueTerm hvalue
  constructor
  · rw [fixedWidthLeftBitIndexTerm, paAddTerm_freeVariables,
      hshiftIndexWidth]
    simp
  constructor
  · simpa [fixedWidthLeftBitValueTerm] using hshiftTable
  constructor
  · simp [fixedWidthRightBitIndexTerm]
  · simpa [fixedWidthRightBitValueTerm] using hshiftValue

theorem fixedWidthBitTerms_freeVariables_of_openIndex
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    (fixedWidthLeftBitIndexTerm widthTerm indexTerm).freeVariables ⊆
        ({0, 1} : Finset Nat) ∧
      (fixedWidthLeftBitValueTerm tableTerm).freeVariables = ∅ ∧
      fixedWidthRightBitIndexTerm.freeVariables = {0} ∧
      (fixedWidthRightBitValueTerm valueTerm).freeVariables = ∅ := by
  have hindexWidth :
      (fixedWidthIndexWidthTerm widthTerm indexTerm).freeVariables ⊆ {0} := by
    rw [fixedWidthIndexWidthTerm, paMulTerm_freeVariables, hwidth]
    simpa using hindex
  have hshiftIndexWidth :
      (Rew.shift (fixedWidthIndexWidthTerm widthTerm indexTerm)).freeVariables
        ⊆ {1} :=
    shiftedTerm_freeVariables_subset_one
      (fixedWidthIndexWidthTerm widthTerm indexTerm) hindexWidth
  have hshiftTable := shiftedTerm_freeVariables_eq_empty tableTerm htable
  have hshiftValue := shiftedTerm_freeVariables_eq_empty valueTerm hvalue
  constructor
  · rw [fixedWidthLeftBitIndexTerm, paAddTerm_freeVariables]
    exact Finset.union_subset
      (hshiftIndexWidth.trans (by simp)) (by simp)
  constructor
  · simpa [fixedWidthLeftBitValueTerm] using hshiftTable
  constructor
  · simp [fixedWidthRightBitIndexTerm]
  · simpa [fixedWidthRightBitValueTerm] using hshiftValue

private theorem valuationContext_card_le_four_of_subset_singleton
    (vars : Finset Nat) (valuation : Nat -> Nat)
    (hvars : vars ⊆ {0}) :
    (valuationContext vars valuation).card <= 4 := by
  have himage : (valuationContext vars valuation).card <= vars.card := by
    unfold valuationContext
    exact Finset.card_image_le
  have hcard : vars.card <= ({0} : Finset Nat).card :=
    Finset.card_le_card hvars
  simp only [Finset.card_singleton] at hcard
  omega

private theorem valuationContext_card_le_four_of_subset_pair
    (vars : Finset Nat) (valuation : Nat -> Nat)
    (hvars : vars ⊆ ({0, 1} : Finset Nat)) :
    (valuationContext vars valuation).card <= 4 := by
  have himage : (valuationContext vars valuation).card <= vars.card := by
    unfold valuationContext
    exact Finset.card_image_le
  have hcard : vars.card <= ({0, 1} : Finset Nat).card :=
    Finset.card_le_card hvars
  norm_num at hcard
  omega

def fixedWidthBitLeafSmallContextSyntaxResource
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat) : Nat :=
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
  let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm leftValueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm leftValueTerm
  let rightTrue := binaryBitAtValuationFormula true rightIndexTerm rightValueTerm
  let rightFalse := binaryBitAtValuationFormula false rightIndexTerm rightValueTerm
  let forward := (∼leftAtom ⋎ rightAtom)
  let backward := (∼rightAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  let leftTrueContext := valuationContext leftTrue.freeVariables branchValuation
  let leftFalseContext := valuationContext leftFalse.freeVariables branchValuation
  let rightTrueContext := valuationContext rightTrue.freeVariables branchValuation
  let rightFalseContext := valuationContext rightFalse.freeVariables branchValuation
  let forwardContext := valuationContext forward.freeVariables branchValuation
  let backwardContext := valuationContext backward.freeVariables branchValuation
  let targetContext := valuationContext target.freeVariables branchValuation
  formulaCodeSum leftTrueContext + formulaCodeSum leftFalseContext +
    formulaCodeSum rightTrueContext + formulaCodeSum rightFalseContext +
    formulaCodeSum forwardContext + formulaCodeSum backwardContext +
    formulaCodeSum targetContext +
    (binaryFormulaCode leftTrue).length +
    (binaryFormulaCode leftFalse).length +
    (binaryFormulaCode rightTrue).length +
    (binaryFormulaCode rightFalse).length +
    (binaryFormulaCode leftAtom).length +
    (binaryFormulaCode rightAtom).length +
    (binaryFormulaCode forward).length +
    (binaryFormulaCode backward).length +
    (binaryFormulaCode target).length

theorem fixedWidthBitLeafSmallContextCards_of_closed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅) :
    let branchValuation := extendValuation bitIndex valuation
    let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
    let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
    let rightIndexTerm := fixedWidthRightBitIndexTerm
    let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
    let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
    let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
    let leftTrue := binaryBitAtValuationFormula true leftIndexTerm leftValueTerm
    let leftFalse := binaryBitAtValuationFormula false leftIndexTerm leftValueTerm
    let rightTrue := binaryBitAtValuationFormula true rightIndexTerm rightValueTerm
    let rightFalse := binaryBitAtValuationFormula false rightIndexTerm rightValueTerm
    let forward := (∼leftAtom ⋎ rightAtom)
    let backward := (∼rightAtom ⋎ leftAtom)
    let target := forward ⋏ backward
    (valuationContext leftTrue.freeVariables branchValuation).card <= 4 ∧
      (valuationContext leftFalse.freeVariables branchValuation).card <= 4 ∧
      (valuationContext rightTrue.freeVariables branchValuation).card <= 4 ∧
      (valuationContext rightFalse.freeVariables branchValuation).card <= 4 ∧
      (valuationContext forward.freeVariables branchValuation).card <= 4 ∧
      (valuationContext backward.freeVariables branchValuation).card <= 4 ∧
      (valuationContext target.freeVariables branchValuation).card <= 4 := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
  let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm leftValueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm leftValueTerm
  let rightTrue := binaryBitAtValuationFormula true rightIndexTerm rightValueTerm
  let rightFalse := binaryBitAtValuationFormula false rightIndexTerm rightValueTerm
  let forward := (∼leftAtom ⋎ rightAtom)
  let backward := (∼rightAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  have hterms := fixedWidthBitTerms_freeVariables_of_closed
    tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hleftTrueVars := binaryBitAtValuationFormula_freeVariables_subset
    true leftIndexTerm leftValueTerm
  have hleftFalseVars := binaryBitAtValuationFormula_freeVariables_subset
    false leftIndexTerm leftValueTerm
  have hrightTrueVars := binaryBitAtValuationFormula_freeVariables_subset
    true rightIndexTerm rightValueTerm
  have hrightFalseVars := binaryBitAtValuationFormula_freeVariables_subset
    false rightIndexTerm rightValueTerm
  have hleftTerms :
      leftIndexTerm.freeVariables ∪ leftValueTerm.freeVariables = {0} := by
    dsimp only [leftIndexTerm, leftValueTerm]
    rw [hterms.1, hterms.2.1]
    simp
  have hrightTerms :
      rightIndexTerm.freeVariables ∪ rightValueTerm.freeVariables = {0} := by
    dsimp only [rightIndexTerm, rightValueTerm]
    rw [hterms.2.2.1, hterms.2.2.2]
    simp
  rw [hleftTerms] at hleftTrueVars hleftFalseVars
  rw [hrightTerms] at hrightTrueVars hrightFalseVars
  have hleftAtomVars : leftAtom.freeVariables ⊆ {0} := by
    simpa [leftAtom, leftTrue, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using hleftTrueVars
  have hrightAtomVars : rightAtom.freeVariables ⊆ {0} := by
    simpa [rightAtom, rightTrue, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using hrightTrueVars
  have hforwardVars : forward.freeVariables ⊆ {0} := by
    simpa [forward] using
      (Finset.union_subset hleftAtomVars hrightAtomVars)
  have hbackwardVars : backward.freeVariables ⊆ {0} := by
    simpa [backward] using
      (Finset.union_subset hrightAtomVars hleftAtomVars)
  have htargetVars : target.freeVariables ⊆ {0} := by
    simpa [target] using
      (Finset.union_subset hforwardVars hbackwardVars)
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
    rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
    rightFalse, forward, backward, target]
  exact ⟨
    valuationContext_card_le_four_of_subset_singleton _ _ hleftTrueVars,
    valuationContext_card_le_four_of_subset_singleton _ _ hleftFalseVars,
    valuationContext_card_le_four_of_subset_singleton _ _ hrightTrueVars,
    valuationContext_card_le_four_of_subset_singleton _ _ hrightFalseVars,
    valuationContext_card_le_four_of_subset_singleton _ _ hforwardVars,
    valuationContext_card_le_four_of_subset_singleton _ _ hbackwardVars,
    valuationContext_card_le_four_of_subset_singleton _ _ htargetVars⟩

theorem fixedWidthBitTermUnionCards_of_openIndex
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    ((fixedWidthLeftBitIndexTerm widthTerm indexTerm).freeVariables ∪
        (fixedWidthLeftBitValueTerm tableTerm).freeVariables).card <= 4 ∧
      (fixedWidthRightBitIndexTerm.freeVariables ∪
        (fixedWidthRightBitValueTerm valueTerm).freeVariables).card <= 4 := by
  have hterms := fixedWidthBitTerms_freeVariables_of_openIndex
    tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hleftSubset :
      (fixedWidthLeftBitIndexTerm widthTerm indexTerm).freeVariables ∪
          (fixedWidthLeftBitValueTerm tableTerm).freeVariables ⊆
        ({0, 1} : Finset Nat) := by
    exact Finset.union_subset hterms.1 (by
      rw [hterms.2.1]
      simp)
  have hrightSubset :
      fixedWidthRightBitIndexTerm.freeVariables ∪
          (fixedWidthRightBitValueTerm valueTerm).freeVariables ⊆
        ({0, 1} : Finset Nat) := by
    rw [hterms.2.2.1, hterms.2.2.2]
    simp
  have hleftCard := Finset.card_le_card hleftSubset
  have hrightCard := Finset.card_le_card hrightSubset
  norm_num at hleftCard hrightCard
  omega

theorem fixedWidthBitLeafSmallContextCards_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    let branchValuation := extendValuation bitIndex valuation
    let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
    let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
    let rightIndexTerm := fixedWidthRightBitIndexTerm
    let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
    let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
    let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
    let leftTrue := binaryBitAtValuationFormula true leftIndexTerm leftValueTerm
    let leftFalse := binaryBitAtValuationFormula false leftIndexTerm leftValueTerm
    let rightTrue := binaryBitAtValuationFormula true rightIndexTerm rightValueTerm
    let rightFalse := binaryBitAtValuationFormula false rightIndexTerm rightValueTerm
    let forward := (∼leftAtom ⋎ rightAtom)
    let backward := (∼rightAtom ⋎ leftAtom)
    let target := forward ⋏ backward
    (valuationContext leftTrue.freeVariables branchValuation).card <= 4 ∧
      (valuationContext leftFalse.freeVariables branchValuation).card <= 4 ∧
      (valuationContext rightTrue.freeVariables branchValuation).card <= 4 ∧
      (valuationContext rightFalse.freeVariables branchValuation).card <= 4 ∧
      (valuationContext forward.freeVariables branchValuation).card <= 4 ∧
      (valuationContext backward.freeVariables branchValuation).card <= 4 ∧
      (valuationContext target.freeVariables branchValuation).card <= 4 := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
  let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm leftValueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm leftValueTerm
  let rightTrue := binaryBitAtValuationFormula true rightIndexTerm rightValueTerm
  let rightFalse := binaryBitAtValuationFormula false rightIndexTerm rightValueTerm
  let forward := (∼leftAtom ⋎ rightAtom)
  let backward := (∼rightAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  have hterms := fixedWidthBitTerms_freeVariables_of_openIndex
    tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hleftTerms :
      leftIndexTerm.freeVariables ∪ leftValueTerm.freeVariables ⊆
        ({0, 1} : Finset Nat) := by
    dsimp only [leftIndexTerm, leftValueTerm]
    exact Finset.union_subset hterms.1 (by
      rw [hterms.2.1]
      simp)
  have hrightTerms :
      rightIndexTerm.freeVariables ∪ rightValueTerm.freeVariables ⊆
        ({0, 1} : Finset Nat) := by
    dsimp only [rightIndexTerm, rightValueTerm]
    rw [hterms.2.2.1, hterms.2.2.2]
    simp
  have hleftTrueVars :=
    (binaryBitAtValuationFormula_freeVariables_subset
      true leftIndexTerm leftValueTerm).trans hleftTerms
  have hleftFalseVars :=
    (binaryBitAtValuationFormula_freeVariables_subset
      false leftIndexTerm leftValueTerm).trans hleftTerms
  have hrightTrueVars :=
    (binaryBitAtValuationFormula_freeVariables_subset
      true rightIndexTerm rightValueTerm).trans hrightTerms
  have hrightFalseVars :=
    (binaryBitAtValuationFormula_freeVariables_subset
      false rightIndexTerm rightValueTerm).trans hrightTerms
  have hleftAtomVars : leftAtom.freeVariables ⊆ ({0, 1} : Finset Nat) := by
    simpa [leftAtom, leftTrue, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using hleftTrueVars
  have hrightAtomVars : rightAtom.freeVariables ⊆ ({0, 1} : Finset Nat) := by
    simpa [rightAtom, rightTrue, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using hrightTrueVars
  have hforwardVars : forward.freeVariables ⊆ ({0, 1} : Finset Nat) := by
    simpa [forward] using
      (Finset.union_subset hleftAtomVars hrightAtomVars)
  have hbackwardVars : backward.freeVariables ⊆ ({0, 1} : Finset Nat) := by
    simpa [backward] using
      (Finset.union_subset hrightAtomVars hleftAtomVars)
  have htargetVars : target.freeVariables ⊆ ({0, 1} : Finset Nat) := by
    simpa [target] using
      (Finset.union_subset hforwardVars hbackwardVars)
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
    rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
    rightFalse, forward, backward, target]
  exact ⟨
    valuationContext_card_le_four_of_subset_pair _ _ hleftTrueVars,
    valuationContext_card_le_four_of_subset_pair _ _ hleftFalseVars,
    valuationContext_card_le_four_of_subset_pair _ _ hrightTrueVars,
    valuationContext_card_le_four_of_subset_pair _ _ hrightFalseVars,
    valuationContext_card_le_four_of_subset_pair _ _ hforwardVars,
    valuationContext_card_le_four_of_subset_pair _ _ hbackwardVars,
    valuationContext_card_le_four_of_subset_pair _ _ htargetVars⟩

#print axioms fixedWidthBitLeafSmallContextCards_of_closed
#print axioms fixedWidthBitTermUnionCards_of_openIndex
#print axioms fixedWidthBitLeafSmallContextCards_of_openIndex

theorem fixedWidthBitLeafUniformStructuralEnvelope_le_smallContextAssemblyEnvelope
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (hleftTrueCard :
      (valuationContext
        (binaryBitAtValuationFormula true
          (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
          (fixedWidthLeftBitValueTerm tableTerm)).freeVariables
        (extendValuation bitIndex valuation)).card <= 4)
    (hleftFalseCard :
      (valuationContext
        (binaryBitAtValuationFormula false
          (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
          (fixedWidthLeftBitValueTerm tableTerm)).freeVariables
        (extendValuation bitIndex valuation)).card <= 4)
    (hrightTrueCard :
      (valuationContext
        (binaryBitAtValuationFormula true fixedWidthRightBitIndexTerm
          (fixedWidthRightBitValueTerm valueTerm)).freeVariables
        (extendValuation bitIndex valuation)).card <= 4)
    (hrightFalseCard :
      (valuationContext
        (binaryBitAtValuationFormula false fixedWidthRightBitIndexTerm
          (fixedWidthRightBitValueTerm valueTerm)).freeVariables
        (extendValuation bitIndex valuation)).card <= 4)
    (hforwardCard :
      (valuationContext
        (∼binaryBitAtomAtTerms
            (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
            (fixedWidthLeftBitValueTerm tableTerm) ⋎
          binaryBitAtomAtTerms fixedWidthRightBitIndexTerm
            (fixedWidthRightBitValueTerm valueTerm)).freeVariables
        (extendValuation bitIndex valuation)).card <= 4)
    (hbackwardCard :
      (valuationContext
        (∼binaryBitAtomAtTerms fixedWidthRightBitIndexTerm
            (fixedWidthRightBitValueTerm valueTerm) ⋎
          binaryBitAtomAtTerms
            (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
            (fixedWidthLeftBitValueTerm tableTerm)).freeVariables
        (extendValuation bitIndex valuation)).card <= 4)
    (htargetCard :
      (valuationContext
        ((∼binaryBitAtomAtTerms
            (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
            (fixedWidthLeftBitValueTerm tableTerm) ⋎
          binaryBitAtomAtTerms fixedWidthRightBitIndexTerm
            (fixedWidthRightBitValueTerm valueTerm)) ⋏
          (∼binaryBitAtomAtTerms fixedWidthRightBitIndexTerm
            (fixedWidthRightBitValueTerm valueTerm) ⋎
          binaryBitAtomAtTerms
            (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
            (fixedWidthLeftBitValueTerm tableTerm))).freeVariables
        (extendValuation bitIndex valuation)).card <= 4) :
    fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex <=
      compileBinaryBitLiteralAtValuationPayloadResource true
          (extendValuation bitIndex valuation)
          (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
          (fixedWidthLeftBitValueTerm tableTerm) +
        compileBinaryBitLiteralAtValuationPayloadResource false
          (extendValuation bitIndex valuation)
          (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
          (fixedWidthLeftBitValueTerm tableTerm) +
        compileBinaryBitLiteralAtValuationPayloadResource true
          (extendValuation bitIndex valuation) fixedWidthRightBitIndexTerm
          (fixedWidthRightBitValueTerm valueTerm) +
        compileBinaryBitLiteralAtValuationPayloadResource false
          (extendValuation bitIndex valuation) fixedWidthRightBitIndexTerm
          (fixedWidthRightBitValueTerm valueTerm) +
        13 * smallContextAssemblyEnvelope
          (fixedWidthBitLeafSmallContextSyntaxResource valuation tableTerm
            widthTerm indexTerm valueTerm bitIndex) := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := fixedWidthLeftBitIndexTerm widthTerm indexTerm
  let leftValueTerm := fixedWidthLeftBitValueTerm tableTerm
  let rightIndexTerm := fixedWidthRightBitIndexTerm
  let rightValueTerm := fixedWidthRightBitValueTerm valueTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm leftValueTerm
  let rightAtom := binaryBitAtomAtTerms rightIndexTerm rightValueTerm
  let leftTrue := binaryBitAtValuationFormula true leftIndexTerm leftValueTerm
  let leftFalse := binaryBitAtValuationFormula false leftIndexTerm leftValueTerm
  let rightTrue := binaryBitAtValuationFormula true rightIndexTerm rightValueTerm
  let rightFalse := binaryBitAtValuationFormula false rightIndexTerm rightValueTerm
  let forward := (∼leftAtom ⋎ rightAtom)
  let backward := (∼rightAtom ⋎ leftAtom)
  let target := forward ⋏ backward
  let leftTrueContext := valuationContext leftTrue.freeVariables branchValuation
  let leftFalseContext := valuationContext leftFalse.freeVariables branchValuation
  let rightTrueContext := valuationContext rightTrue.freeVariables branchValuation
  let rightFalseContext := valuationContext rightFalse.freeVariables branchValuation
  let forwardContext := valuationContext forward.freeVariables branchValuation
  let backwardContext := valuationContext backward.freeVariables branchValuation
  let targetContext := valuationContext target.freeVariables branchValuation
  let resource := fixedWidthBitLeafSmallContextSyntaxResource valuation
    tableTerm widthTerm indexTerm valueTerm bitIndex
  have hleftTrueContext : FormulaCodeBound leftTrueContext resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext] at hsum ⊢
    omega
  have hleftFalseContext : FormulaCodeBound leftFalseContext resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext] at hsum ⊢
    omega
  have hrightTrueContext : FormulaCodeBound rightTrueContext resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext] at hsum ⊢
    omega
  have hrightFalseContext : FormulaCodeBound rightFalseContext resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext] at hsum ⊢
    omega
  have hforwardContext : FormulaCodeBound forwardContext resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext] at hsum ⊢
    omega
  have hbackwardContext : FormulaCodeBound backwardContext resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext] at hsum ⊢
    omega
  have htargetContext : FormulaCodeBound targetContext resource := by
    intro formula hformula
    have hsum := formulaCode_le_formulaCodeSum hformula
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext] at hsum ⊢
    omega
  have hleftTrueCode : (binaryFormulaCode leftTrue).length <= resource := by
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext]
    omega
  have hleftFalseCode : (binaryFormulaCode leftFalse).length <= resource := by
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext]
    omega
  have hrightTrueCode : (binaryFormulaCode rightTrue).length <= resource := by
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext]
    omega
  have hrightFalseCode : (binaryFormulaCode rightFalse).length <= resource := by
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext]
    omega
  have hleftAtomCode : (binaryFormulaCode leftAtom).length <= resource := by
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext]
    omega
  have hrightAtomCode : (binaryFormulaCode rightAtom).length <= resource := by
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext]
    omega
  have hforwardCode : (binaryFormulaCode forward).length <= resource := by
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext]
    omega
  have hbackwardCode : (binaryFormulaCode backward).length <= resource := by
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext]
    omega
  have htargetCode : (binaryFormulaCode target).length <= resource := by
    dsimp only [resource]
    unfold fixedWidthBitLeafSmallContextSyntaxResource
    dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
      rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
      rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
      rightTrueContext, rightFalseContext, forwardContext, backwardContext,
      targetContext]
    omega
  have hleftTrueInsertCard : (insert leftTrue leftTrueContext).card <= 8 := by
    have hinsert := Finset.card_insert_le leftTrue leftTrueContext
    dsimp only [leftTrueContext, leftTrue, leftIndexTerm, leftValueTerm,
      branchValuation] at hinsert hleftTrueCard ⊢
    omega
  have hleftFalseInsertCard : (insert leftFalse leftFalseContext).card <= 8 := by
    have hinsert := Finset.card_insert_le leftFalse leftFalseContext
    dsimp only [leftFalseContext, leftFalse, leftIndexTerm, leftValueTerm,
      branchValuation] at hinsert hleftFalseCard ⊢
    omega
  have hrightTrueInsertCard : (insert rightTrue rightTrueContext).card <= 8 := by
    have hinsert := Finset.card_insert_le rightTrue rightTrueContext
    dsimp only [rightTrueContext, rightTrue, rightIndexTerm, rightValueTerm,
      branchValuation] at hinsert hrightTrueCard ⊢
    omega
  have hrightFalseInsertCard : (insert rightFalse rightFalseContext).card <= 8 := by
    have hinsert := Finset.card_insert_le rightFalse rightFalseContext
    dsimp only [rightFalseContext, rightFalse, rightIndexTerm, rightValueTerm,
      branchValuation] at hinsert hrightFalseCard ⊢
    omega
  have hforwardLeftInsertCard : (insert leftFalse forwardContext).card <= 8 := by
    have hinsert := Finset.card_insert_le leftFalse forwardContext
    dsimp only [forwardContext, forward, leftFalse, leftAtom, rightAtom,
      leftIndexTerm, leftValueTerm, rightIndexTerm, rightValueTerm,
      branchValuation] at hinsert hforwardCard ⊢
    omega
  have hforwardRightInsertCard : (insert rightTrue forwardContext).card <= 8 := by
    have hinsert := Finset.card_insert_le rightTrue forwardContext
    dsimp only [forwardContext, forward, rightTrue, leftAtom, rightAtom,
      leftIndexTerm, leftValueTerm, rightIndexTerm, rightValueTerm,
      branchValuation] at hinsert hforwardCard ⊢
    omega
  have hbackwardRightInsertCard : (insert rightFalse backwardContext).card <= 8 := by
    have hinsert := Finset.card_insert_le rightFalse backwardContext
    dsimp only [backwardContext, backward, rightFalse, leftAtom, rightAtom,
      leftIndexTerm, leftValueTerm, rightIndexTerm, rightValueTerm,
      branchValuation] at hinsert hbackwardCard ⊢
    omega
  have hbackwardLeftInsertCard : (insert leftTrue backwardContext).card <= 8 := by
    have hinsert := Finset.card_insert_le leftTrue backwardContext
    dsimp only [backwardContext, backward, leftTrue, leftAtom, rightAtom,
      leftIndexTerm, leftValueTerm, rightIndexTerm, rightValueTerm,
      branchValuation] at hinsert hbackwardCard ⊢
    omega
  have htargetForwardInsertCard : (insert forward targetContext).card <= 8 := by
    have hinsert := Finset.card_insert_le forward targetContext
    dsimp only [targetContext, target, forward, backward, leftAtom, rightAtom,
      leftIndexTerm, leftValueTerm, rightIndexTerm, rightValueTerm,
      branchValuation] at hinsert htargetCard ⊢
    omega
  have htargetBackwardInsertCard : (insert backward targetContext).card <= 8 := by
    have hinsert := Finset.card_insert_le backward targetContext
    dsimp only [targetContext, target, forward, backward, leftAtom, rightAtom,
      leftIndexTerm, leftValueTerm, rightIndexTerm, rightValueTerm,
      branchValuation] at hinsert htargetCard ⊢
    omega
  have hweakLeftTrue := weakeningFullAssemblyCost_le_small
    (insert leftTrue leftTrueContext) resource hleftTrueInsertCard
      (hleftTrueContext.insert hleftTrueCode)
  have hweakLeftFalse := weakeningFullAssemblyCost_le_small
    (insert leftFalse leftFalseContext) resource hleftFalseInsertCard
      (hleftFalseContext.insert hleftFalseCode)
  have hweakRightTrue := weakeningFullAssemblyCost_le_small
    (insert rightTrue rightTrueContext) resource hrightTrueInsertCard
      (hrightTrueContext.insert hrightTrueCode)
  have hweakRightFalse := weakeningFullAssemblyCost_le_small
    (insert rightFalse rightFalseContext) resource hrightFalseInsertCard
      (hrightFalseContext.insert hrightFalseCode)
  have hweakForwardLeft := weakeningFullAssemblyCost_le_small
    (insert leftFalse forwardContext) resource hforwardLeftInsertCard
      (hforwardContext.insert hleftFalseCode)
  have hweakForwardRight := weakeningFullAssemblyCost_le_small
    (insert rightTrue forwardContext) resource hforwardRightInsertCard
      (hforwardContext.insert hrightTrueCode)
  have hweakBackwardRight := weakeningFullAssemblyCost_le_small
    (insert rightFalse backwardContext) resource hbackwardRightInsertCard
      (hbackwardContext.insert hrightFalseCode)
  have hweakBackwardLeft := weakeningFullAssemblyCost_le_small
    (insert leftTrue backwardContext) resource hbackwardLeftInsertCard
      (hbackwardContext.insert hleftTrueCode)
  have hforwardDisjunction := disjunctionFullAssemblyCost_le_small
    forwardContext (∼leftAtom) rightAtom resource hforwardCard hforwardContext
      (by simpa [leftFalse, binaryBitAtValuationFormula,
        binaryBitLiteralAtTerms] using hleftFalseCode)
      hrightAtomCode hforwardCode
  have hbackwardDisjunction := disjunctionFullAssemblyCost_le_small
    backwardContext (∼rightAtom) leftAtom resource hbackwardCard hbackwardContext
      (by simpa [rightFalse, binaryBitAtValuationFormula,
        binaryBitLiteralAtTerms] using hrightFalseCode)
      hleftAtomCode hbackwardCode
  have hweakTargetForward := weakeningFullAssemblyCost_le_small
    (insert forward targetContext) resource htargetForwardInsertCard
      (htargetContext.insert hforwardCode)
  have hweakTargetBackward := weakeningFullAssemblyCost_le_small
    (insert backward targetContext) resource htargetBackwardInsertCard
      (htargetContext.insert hbackwardCode)
  have htargetConjunction := conjunctionFullAssemblyCost_le_small
    targetContext forward backward resource htargetCard htargetContext
      hforwardCode hbackwardCode htargetCode
  simp only [fixedWidthBitLeafUniformStructuralEnvelope]
  dsimp only [branchValuation, leftIndexTerm, leftValueTerm, rightIndexTerm,
    rightValueTerm, leftAtom, rightAtom, leftTrue, leftFalse, rightTrue,
    rightFalse, forward, backward, target, leftTrueContext, leftFalseContext,
    rightTrueContext, rightFalseContext, forwardContext, backwardContext,
    targetContext, resource] at *
  omega

#print axioms fixedWidthBitLeafUniformStructuralEnvelope_le_smallContextAssemblyEnvelope

def fixedWidthBitLeafSmallContextPayloadEnvelope
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat) : Nat :=
  compileBinaryBitLiteralAtValuationPayloadResource true
      (extendValuation bitIndex valuation)
      (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
      (fixedWidthLeftBitValueTerm tableTerm) +
    compileBinaryBitLiteralAtValuationPayloadResource false
      (extendValuation bitIndex valuation)
      (fixedWidthLeftBitIndexTerm widthTerm indexTerm)
      (fixedWidthLeftBitValueTerm tableTerm) +
    compileBinaryBitLiteralAtValuationPayloadResource true
      (extendValuation bitIndex valuation) fixedWidthRightBitIndexTerm
      (fixedWidthRightBitValueTerm valueTerm) +
    compileBinaryBitLiteralAtValuationPayloadResource false
      (extendValuation bitIndex valuation) fixedWidthRightBitIndexTerm
      (fixedWidthRightBitValueTerm valueTerm) +
    13 * smallContextAssemblyEnvelope
      (fixedWidthBitLeafSmallContextSyntaxResource valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex)

theorem fixedWidthBitLeafUniformStructuralEnvelope_le_smallContext_of_closed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables = ∅)
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafSmallContextPayloadEnvelope valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex := by
  have hcards := fixedWidthBitLeafSmallContextCards_of_closed valuation
    tableTerm widthTerm indexTerm valueTerm bitIndex htable hwidth hindex hvalue
  dsimp only at hcards
  simpa only [fixedWidthBitLeafSmallContextPayloadEnvelope] using
    fixedWidthBitLeafUniformStructuralEnvelope_le_smallContextAssemblyEnvelope
      valuation tableTerm widthTerm indexTerm valueTerm bitIndex
      hcards.1 hcards.2.1 hcards.2.2.1 hcards.2.2.2.1
      hcards.2.2.2.2.1 hcards.2.2.2.2.2.1 hcards.2.2.2.2.2.2

theorem fixedWidthBitLeafUniformStructuralEnvelope_le_smallContext_of_openIndex
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (bitIndex : Nat)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthBitLeafUniformStructuralEnvelope valuation tableTerm widthTerm
        indexTerm valueTerm bitIndex <=
      fixedWidthBitLeafSmallContextPayloadEnvelope valuation tableTerm
        widthTerm indexTerm valueTerm bitIndex := by
  have hcards := fixedWidthBitLeafSmallContextCards_of_openIndex valuation
    tableTerm widthTerm indexTerm valueTerm bitIndex
    htable hwidth hindex hvalue
  dsimp only at hcards
  simpa only [fixedWidthBitLeafSmallContextPayloadEnvelope] using
    fixedWidthBitLeafUniformStructuralEnvelope_le_smallContextAssemblyEnvelope
      valuation tableTerm widthTerm indexTerm valueTerm bitIndex
      hcards.1 hcards.2.1 hcards.2.2.1 hcards.2.2.2.1
      hcards.2.2.2.2.1 hcards.2.2.2.2.2.1 hcards.2.2.2.2.2.2

#print axioms
  fixedWidthBitLeafUniformStructuralEnvelope_le_smallContext_of_closed
#print axioms
  fixedWidthBitLeafUniformStructuralEnvelope_le_smallContext_of_openIndex

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds
