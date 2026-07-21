import integration.FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds

/-!
# Public structural bounds for the negation-tag graph

The graph branch is retained as explicit Type-valued data.  Every atomic leaf
is charged to the public valuation-compiler polynomial before the witness and
propositional assembly costs are added.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNegationFormulaTagPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationTermCompiler

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    formula

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

private theorem arithmeticMulTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Mul.mul left right

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticTwoTerm_freeVariables_eq_empty :
    (‘2’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem arithmeticFourTerm_freeVariables_eq_empty :
    (‘4’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem arithmeticEightTerm_freeVariables_eq_empty :
    (‘8’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem termValue_arithmeticEight (valuation : Nat -> Nat) :
    termValue valuation (‘8’ : ValuationTerm) = 8 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

def pairLtFourStructuralPayloadPolynomial (pair : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm pair, (‘4’ : ValuationTerm)]

theorem pairLtFourCertificate_structuralPayloadBound_le_public
    (pair : Nat) (hpair : pair < 4) :
    hybridFormulaStructuralPayloadBound
        (pairLtFourCertificate pair hpair) <=
      pairLtFourStructuralPayloadPolynomial pair := by
  change compilePositiveRelationPayloadResource
      FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
      Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm pair, (‘4’ : ValuationTerm)] <= _
  unfold pairLtFourStructuralPayloadPolynomial
  apply compilePositiveRelationPayloadResource_le_publicPolynomial
  · simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
  · change (‘4’ : ValuationTerm).freeVariables ⊆ {0}
    rw [arithmeticFourTerm_freeVariables_eq_empty]
    simp

def tagLtEightStructuralPayloadPolynomial (tag : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm tag, (‘8’ : ValuationTerm)]

theorem tagLtEightCertificate_structuralPayloadBound_le_public
    (tag : Nat) (htag : tag < 8) :
    hybridFormulaStructuralPayloadBound
        (tagLtEightCertificate tag htag) <=
      tagLtEightStructuralPayloadPolynomial tag := by
  change compilePositiveRelationPayloadResource
      FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
      Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm tag, (‘8’ : ValuationTerm)] <= _
  unfold tagLtEightStructuralPayloadPolynomial
  apply compilePositiveRelationPayloadResource_le_publicPolynomial
  · simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
  · change (‘8’ : ValuationTerm).freeVariables ⊆ {0}
    rw [arithmeticEightTerm_freeVariables_eq_empty]
    simp

def evenTagEqualityStructuralPayloadPolynomial (tag pair : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm tag,
      (‘2 * !!(shortBinaryNumeralTerm pair)’ : ValuationTerm)]

theorem evenTagEqualityCertificate_structuralPayloadBound_le_public
    (tag pair : Nat) (htag : tag = 2 * pair) :
    hybridFormulaStructuralPayloadBound
        (evenTagEqualityCertificate tag pair htag) <=
      evenTagEqualityStructuralPayloadPolynomial tag pair := by
  change compilePositiveRelationPayloadResource
      FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm tag,
        (‘2 * !!(shortBinaryNumeralTerm pair)’ : ValuationTerm)] <= _
  unfold evenTagEqualityStructuralPayloadPolynomial
  apply compilePositiveRelationPayloadResource_le_publicPolynomial
  · simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
  · change (‘2 * !!(shortBinaryNumeralTerm pair)’ :
        ValuationTerm).freeVariables ⊆ {0}
    rw [arithmeticMulTerm_freeVariables,
      arithmeticTwoTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp

def oddTagEqualityStructuralPayloadPolynomial (tag pair : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm tag,
      (‘2 * !!(shortBinaryNumeralTerm pair) + 1’ : ValuationTerm)]

theorem oddTagEqualityCertificate_structuralPayloadBound_le_public
    (tag pair : Nat) (htag : tag = 2 * pair + 1) :
    hybridFormulaStructuralPayloadBound
        (oddTagEqualityCertificate tag pair htag) <=
      oddTagEqualityStructuralPayloadPolynomial tag pair := by
  change compilePositiveRelationPayloadResource
      FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm tag,
        (‘2 * !!(shortBinaryNumeralTerm pair) + 1’ : ValuationTerm)] <= _
  unfold oddTagEqualityStructuralPayloadPolynomial
  apply compilePositiveRelationPayloadResource_le_publicPolynomial
  · simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
  · change (‘2 * !!(shortBinaryNumeralTerm pair) + 1’ :
        ValuationTerm).freeVariables ⊆ {0}
    rw [arithmeticAddTerm_freeVariables, arithmeticMulTerm_freeVariables,
      arithmeticTwoTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp

def mappedSuccessorStructuralPayloadPolynomial (tag mapped : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm mapped,
      (‘!!(shortBinaryNumeralTerm tag) + 1’ : ValuationTerm)]

theorem mappedSuccessorCertificate_structuralPayloadBound_le_public
    (tag mapped : Nat) (hmapped : mapped = tag + 1) :
    hybridFormulaStructuralPayloadBound
        (mappedSuccessorCertificate tag mapped hmapped) <=
      mappedSuccessorStructuralPayloadPolynomial tag mapped := by
  change compilePositiveRelationPayloadResource
      FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm mapped,
        (‘!!(shortBinaryNumeralTerm tag) + 1’ : ValuationTerm)] <= _
  unfold mappedSuccessorStructuralPayloadPolynomial
  apply compilePositiveRelationPayloadResource_le_publicPolynomial
  · simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
  · change (‘!!(shortBinaryNumeralTerm tag) + 1’ :
        ValuationTerm).freeVariables ⊆ {0}
    rw [arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp

def tagMappedSuccessorStructuralPayloadPolynomial (tag mapped : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm tag,
      (‘!!(shortBinaryNumeralTerm mapped) + 1’ : ValuationTerm)]

theorem tagMappedSuccessorCertificate_structuralPayloadBound_le_public
    (tag mapped : Nat) (htag : tag = mapped + 1) :
    hybridFormulaStructuralPayloadBound
        (tagMappedSuccessorCertificate tag mapped htag) <=
      tagMappedSuccessorStructuralPayloadPolynomial tag mapped := by
  change compilePositiveRelationPayloadResource
      FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm tag,
        (‘!!(shortBinaryNumeralTerm mapped) + 1’ : ValuationTerm)] <= _
  unfold tagMappedSuccessorStructuralPayloadPolynomial
  apply compilePositiveRelationPayloadResource_le_publicPolynomial
  · simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
  · change (‘!!(shortBinaryNumeralTerm mapped) + 1’ :
        ValuationTerm).freeVariables ⊆ {0}
    rw [arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp

def mappedTagEqualityStructuralPayloadPolynomial (tag mapped : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm mapped, shortBinaryNumeralTerm tag]

theorem mappedTagEqualityCertificate_structuralPayloadBound_le_public
    (tag mapped : Nat) (hmapped : mapped = tag) :
    hybridFormulaStructuralPayloadBound
        (mappedTagEqualityCertificate tag mapped hmapped) <=
      mappedTagEqualityStructuralPayloadPolynomial tag mapped := by
  change compilePositiveRelationPayloadResource
      FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm mapped, shortBinaryNumeralTerm tag] <= _
  unfold mappedTagEqualityStructuralPayloadPolynomial
  apply compilePositiveRelationPayloadResource_le_publicPolynomial
  · simp [shortBinaryNumeralTerm_freeVariables_eq_empty]
  · simp [shortBinaryNumeralTerm_freeVariables_eq_empty]

def eightLeTagEqualityPayloadPolynomial (tag : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    Language.Eq.eq
    ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag]

def eightLeTagStrictPayloadPolynomial (tag : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    Language.ORing.Rel.lt
    ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag]

def eightLeTagStructuralPayloadEnvelope (tag : Nat) : Nat :=
  let args : Fin 2 -> ValuationTerm :=
    ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
  eightLeTagEqualityPayloadPolynomial tag +
    eightLeTagStrictPayloadPolynomial tag +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem eightLeTagCertificate_structuralPayloadBound_le_public
    (tag : Nat) (htag : 8 <= tag) :
    hybridFormulaStructuralPayloadBound
        (eightLeTagCertificate tag htag) <=
      eightLeTagStructuralPayloadEnvelope tag := by
  let args : Fin 2 -> ValuationTerm :=
    ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (‘8’ : ValuationTerm).freeVariables ⊆ {0}
    rw [arithmeticEightTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm tag).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hequality :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
      Language.Eq.eq args hfirst hsecond
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
      Language.ORing.Rel.lt args hfirst hsecond
  by_cases heq : 8 = tag
  · simp only [eightLeTagCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold eightLeTagStructuralPayloadEnvelope
      eightLeTagEqualityPayloadPolynomial
      eightLeTagStrictPayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    omega
  · simp only [eightLeTagCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold eightLeTagStructuralPayloadEnvelope
      eightLeTagEqualityPayloadPolynomial
      eightLeTagStrictPayloadPolynomial
    dsimp only [args] at hequality hstrict ⊢
    omega

def compactNegationFormulaTagEvenPostWitnessPayloadEnvelope
    (tag mapped pair : Nat) : Nat :=
  let pairFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm pair) < 4”
  let equalityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tag) =
      2 * !!(shortBinaryNumeralTerm pair)”
  let successorFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm mapped) =
      !!(shortBinaryNumeralTerm tag) + 1”
  let innerFormula := equalityFormula ⋏ successorFormula
  let innerResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    equalityFormula successorFormula
    (evenTagEqualityStructuralPayloadPolynomial tag pair)
    (mappedSuccessorStructuralPayloadPolynomial tag mapped)
  transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    pairFormula innerFormula
    (pairLtFourStructuralPayloadPolynomial pair) innerResource

theorem
    compactNegationFormulaTagEvenWitnessCertificate_structuralPayloadBound_le_public
    (tag mapped pair : Nat)
    (hpair : pair < 4)
    (htag : tag = 2 * pair)
    (hmapped : mapped = tag + 1) :
    hybridFormulaStructuralPayloadBound
        (compactNegationFormulaTagEvenWitnessCertificate
          tag mapped pair hpair htag hmapped) <=
      hybridExistsWitnessStructuralPayloadEnvelope
        FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
        (compactNegationFormulaTagEvenWitnessBody tag mapped) pair
        (compactNegationFormulaTagEvenPostWitnessPayloadEnvelope
          tag mapped pair) := by
  let pairCertificate := pairLtFourCertificate pair hpair
  let equalityCertificate := evenTagEqualityCertificate tag pair htag
  let successorCertificate := mappedSuccessorCertificate tag mapped hmapped
  let innerCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      equalityCertificate successorCertificate
  let postCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      pairCertificate innerCertificate
  let instantiated := CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactNegationFormulaTagEvenWitnessBody_substitution_alignment
      tag mapped pair).symm postCertificate
  have hpairResource :=
    pairLtFourCertificate_structuralPayloadBound_le_public pair hpair
  have hequalityResource :=
    evenTagEqualityCertificate_structuralPayloadBound_le_public
      tag pair htag
  have hsuccessorResource :=
    mappedSuccessorCertificate_structuralPayloadBound_le_public
      tag mapped hmapped
  have hinner := transparentHybridConjunctionPayloadBound_le
    equalityCertificate successorCertificate _ _ hequalityResource
      hsuccessorResource
  have hpost := transparentHybridConjunctionPayloadBound_le
    pairCertificate innerCertificate _ _ hpairResource hinner
  have hinstantiated : hybridFormulaStructuralPayloadBound instantiated <=
      compactNegationFormulaTagEvenPostWitnessPayloadEnvelope
        tag mapped pair := by
    unfold compactNegationFormulaTagEvenPostWitnessPayloadEnvelope
    simpa only [instantiated, hybridFormulaStructuralPayloadBound,
      pairCertificate, equalityCertificate, successorCertificate,
      innerCertificate, postCertificate] using hpost
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
    (compactNegationFormulaTagEvenWitnessBody tag mapped) pair instantiated
    (compactNegationFormulaTagEvenPostWitnessPayloadEnvelope tag mapped pair)
    hinstantiated
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.existsWitness
        (compactNegationFormulaTagEvenWitnessBody tag mapped) pair
        instantiated) <= _
  exact hexists

def compactNegationFormulaTagOddPostWitnessPayloadEnvelope
    (tag mapped pair : Nat) : Nat :=
  let pairFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm pair) < 4”
  let equalityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tag) =
      2 * !!(shortBinaryNumeralTerm pair) + 1”
  let successorFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tag) =
      !!(shortBinaryNumeralTerm mapped) + 1”
  let innerFormula := equalityFormula ⋏ successorFormula
  let innerResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    equalityFormula successorFormula
    (oddTagEqualityStructuralPayloadPolynomial tag pair)
    (tagMappedSuccessorStructuralPayloadPolynomial tag mapped)
  transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
    pairFormula innerFormula
    (pairLtFourStructuralPayloadPolynomial pair) innerResource

theorem
    compactNegationFormulaTagOddWitnessCertificate_structuralPayloadBound_le_public
    (tag mapped pair : Nat)
    (hpair : pair < 4)
    (htag : tag = 2 * pair + 1)
    (hmapped : tag = mapped + 1) :
    hybridFormulaStructuralPayloadBound
        (compactNegationFormulaTagOddWitnessCertificate
          tag mapped pair hpair htag hmapped) <=
      hybridExistsWitnessStructuralPayloadEnvelope
        FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
        (compactNegationFormulaTagOddWitnessBody tag mapped) pair
        (compactNegationFormulaTagOddPostWitnessPayloadEnvelope
          tag mapped pair) := by
  let pairCertificate := pairLtFourCertificate pair hpair
  let equalityCertificate := oddTagEqualityCertificate tag pair htag
  let successorCertificate := tagMappedSuccessorCertificate tag mapped hmapped
  let innerCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      equalityCertificate successorCertificate
  let postCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      pairCertificate innerCertificate
  let instantiated := CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactNegationFormulaTagOddWitnessBody_substitution_alignment
      tag mapped pair).symm postCertificate
  have hpairResource :=
    pairLtFourCertificate_structuralPayloadBound_le_public pair hpair
  have hequalityResource :=
    oddTagEqualityCertificate_structuralPayloadBound_le_public
      tag pair htag
  have hsuccessorResource :=
    tagMappedSuccessorCertificate_structuralPayloadBound_le_public
      tag mapped hmapped
  have hinner := transparentHybridConjunctionPayloadBound_le
    equalityCertificate successorCertificate _ _ hequalityResource
      hsuccessorResource
  have hpost := transparentHybridConjunctionPayloadBound_le
    pairCertificate innerCertificate _ _ hpairResource hinner
  have hinstantiated : hybridFormulaStructuralPayloadBound instantiated <=
      compactNegationFormulaTagOddPostWitnessPayloadEnvelope
        tag mapped pair := by
    unfold compactNegationFormulaTagOddPostWitnessPayloadEnvelope
    simpa only [instantiated, hybridFormulaStructuralPayloadBound,
      pairCertificate, equalityCertificate, successorCertificate,
      innerCertificate, postCertificate] using hpost
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
    (compactNegationFormulaTagOddWitnessBody tag mapped) pair instantiated
    (compactNegationFormulaTagOddPostWitnessPayloadEnvelope tag mapped pair)
    hinstantiated
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.existsWitness
        (compactNegationFormulaTagOddWitnessBody tag mapped) pair
        instantiated) <= _
  exact hexists

noncomputable def compactNegationFormulaTagBranchPayloadEnvelopeFromData
    (tag mapped : Nat)
    (data : CompactNegationFormulaTagCheckedBranchData tag mapped) : Nat :=
  let valuation :=
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
  let tagLtFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tag) < 8”
  let evenFormula : ValuationFormula :=
    ∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped
  let oddFormula : ValuationFormula :=
    ∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped
  let witnessFormula := evenFormula ⋎ oddFormula
  let smallFormula := tagLtFormula ⋏ witnessFormula
  let eightLeFormula : ValuationFormula :=
    “8 ≤ !!(shortBinaryNumeralTerm tag)”
  let mappedFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm mapped) = !!(shortBinaryNumeralTerm tag)”
  let largeFormula := eightLeFormula ⋏ mappedFormula
  match data with
  | .even _ pair _ _ _ =>
      let evenResource := hybridExistsWitnessStructuralPayloadEnvelope
        valuation (compactNegationFormulaTagEvenWitnessBody tag mapped) pair
        (compactNegationFormulaTagEvenPostWitnessPayloadEnvelope
          tag mapped pair)
      let witnessResource := transparentHybridDisjunctionLeftPayloadEnvelope
        valuation evenFormula oddFormula evenResource
      let smallResource := transparentHybridConjunctionPayloadEnvelope
        valuation tagLtFormula witnessFormula
        (tagLtEightStructuralPayloadPolynomial tag) witnessResource
      transparentHybridDisjunctionLeftPayloadEnvelope valuation
        smallFormula largeFormula smallResource
  | .odd _ pair _ _ _ =>
      let oddResource := hybridExistsWitnessStructuralPayloadEnvelope
        valuation (compactNegationFormulaTagOddWitnessBody tag mapped) pair
        (compactNegationFormulaTagOddPostWitnessPayloadEnvelope
          tag mapped pair)
      let witnessResource := transparentHybridDisjunctionRightPayloadEnvelope
        valuation evenFormula oddFormula oddResource
      let smallResource := transparentHybridConjunctionPayloadEnvelope
        valuation tagLtFormula witnessFormula
        (tagLtEightStructuralPayloadPolynomial tag) witnessResource
      transparentHybridDisjunctionLeftPayloadEnvelope valuation
        smallFormula largeFormula smallResource
  | .large _ _ =>
      let largeResource := transparentHybridConjunctionPayloadEnvelope
        valuation eightLeFormula mappedFormula
        (eightLeTagStructuralPayloadEnvelope tag)
        (mappedTagEqualityStructuralPayloadPolynomial tag mapped)
      transparentHybridDisjunctionRightPayloadEnvelope valuation
        smallFormula largeFormula largeResource

def compactNegationFormulaTagEvenBranchPayloadEnvelope
    (tag mapped pair : Nat) : Nat :=
  let valuation :=
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
  let tagLtFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tag) < 8”
  let evenFormula : ValuationFormula :=
    ∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped
  let oddFormula : ValuationFormula :=
    ∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped
  let witnessFormula := evenFormula ⋎ oddFormula
  let smallFormula := tagLtFormula ⋏ witnessFormula
  let eightLeFormula : ValuationFormula :=
    “8 ≤ !!(shortBinaryNumeralTerm tag)”
  let mappedFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm mapped) = !!(shortBinaryNumeralTerm tag)”
  let largeFormula := eightLeFormula ⋏ mappedFormula
  let evenResource := hybridExistsWitnessStructuralPayloadEnvelope
    valuation (compactNegationFormulaTagEvenWitnessBody tag mapped) pair
    (compactNegationFormulaTagEvenPostWitnessPayloadEnvelope tag mapped pair)
  let witnessResource := transparentHybridDisjunctionLeftPayloadEnvelope
    valuation evenFormula oddFormula evenResource
  let smallResource := transparentHybridConjunctionPayloadEnvelope
    valuation tagLtFormula witnessFormula
    (tagLtEightStructuralPayloadPolynomial tag) witnessResource
  transparentHybridDisjunctionLeftPayloadEnvelope valuation
    smallFormula largeFormula smallResource

def compactNegationFormulaTagOddBranchPayloadEnvelope
    (tag mapped pair : Nat) : Nat :=
  let valuation :=
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
  let tagLtFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tag) < 8”
  let evenFormula : ValuationFormula :=
    ∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped
  let oddFormula : ValuationFormula :=
    ∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped
  let witnessFormula := evenFormula ⋎ oddFormula
  let smallFormula := tagLtFormula ⋏ witnessFormula
  let eightLeFormula : ValuationFormula :=
    “8 ≤ !!(shortBinaryNumeralTerm tag)”
  let mappedFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm mapped) = !!(shortBinaryNumeralTerm tag)”
  let largeFormula := eightLeFormula ⋏ mappedFormula
  let oddResource := hybridExistsWitnessStructuralPayloadEnvelope
    valuation (compactNegationFormulaTagOddWitnessBody tag mapped) pair
    (compactNegationFormulaTagOddPostWitnessPayloadEnvelope tag mapped pair)
  let witnessResource := transparentHybridDisjunctionRightPayloadEnvelope
    valuation evenFormula oddFormula oddResource
  let smallResource := transparentHybridConjunctionPayloadEnvelope
    valuation tagLtFormula witnessFormula
    (tagLtEightStructuralPayloadPolynomial tag) witnessResource
  transparentHybridDisjunctionLeftPayloadEnvelope valuation
    smallFormula largeFormula smallResource

def compactNegationFormulaTagLargeBranchPayloadEnvelope
    (tag mapped : Nat) : Nat :=
  let valuation :=
    FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation
  let tagLtFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm tag) < 8”
  let evenFormula : ValuationFormula :=
    ∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped
  let oddFormula : ValuationFormula :=
    ∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped
  let witnessFormula := evenFormula ⋎ oddFormula
  let smallFormula := tagLtFormula ⋏ witnessFormula
  let eightLeFormula : ValuationFormula :=
    “8 ≤ !!(shortBinaryNumeralTerm tag)”
  let mappedFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm mapped) = !!(shortBinaryNumeralTerm tag)”
  let largeFormula := eightLeFormula ⋏ mappedFormula
  let largeResource := transparentHybridConjunctionPayloadEnvelope
    valuation eightLeFormula mappedFormula
    (eightLeTagStructuralPayloadEnvelope tag)
    (mappedTagEqualityStructuralPayloadPolynomial tag mapped)
  transparentHybridDisjunctionRightPayloadEnvelope valuation
    smallFormula largeFormula largeResource

def compactNegationFormulaTagPublicFinitePayloadEnvelope
    (tag mapped : Nat) : Nat :=
  (Finset.range 4).sum
      (compactNegationFormulaTagEvenBranchPayloadEnvelope tag mapped) +
    (Finset.range 4).sum
      (compactNegationFormulaTagOddBranchPayloadEnvelope tag mapped) +
    compactNegationFormulaTagLargeBranchPayloadEnvelope tag mapped

theorem
    compactNegationFormulaTagBranchPayloadEnvelopeFromData_le_publicFinite
    (tag mapped : Nat)
    (data : CompactNegationFormulaTagCheckedBranchData tag mapped) :
    compactNegationFormulaTagBranchPayloadEnvelopeFromData tag mapped data <=
      compactNegationFormulaTagPublicFinitePayloadEnvelope tag mapped := by
  cases data with
  | even hsmall pair hpair htag hmapped =>
      unfold compactNegationFormulaTagBranchPayloadEnvelopeFromData
      change compactNegationFormulaTagEvenBranchPayloadEnvelope tag mapped
          pair <= _
      have heven :
          compactNegationFormulaTagEvenBranchPayloadEnvelope tag mapped pair <=
            (Finset.range 4).sum
              (compactNegationFormulaTagEvenBranchPayloadEnvelope tag
                mapped) := by
        exact Finset.single_le_sum
          (fun candidate _ => Nat.zero_le
            (compactNegationFormulaTagEvenBranchPayloadEnvelope tag mapped
              candidate))
          (Finset.mem_range.mpr hpair)
      unfold compactNegationFormulaTagPublicFinitePayloadEnvelope
      omega
  | odd hsmall pair hpair htag hmapped =>
      unfold compactNegationFormulaTagBranchPayloadEnvelopeFromData
      change compactNegationFormulaTagOddBranchPayloadEnvelope tag mapped
          pair <= _
      have hodd :
          compactNegationFormulaTagOddBranchPayloadEnvelope tag mapped pair <=
            (Finset.range 4).sum
              (compactNegationFormulaTagOddBranchPayloadEnvelope tag
                mapped) := by
        exact Finset.single_le_sum
          (fun candidate _ => Nat.zero_le
            (compactNegationFormulaTagOddBranchPayloadEnvelope tag mapped
              candidate))
          (Finset.mem_range.mpr hpair)
      unfold compactNegationFormulaTagPublicFinitePayloadEnvelope
      omega
  | large hlarge hmapped =>
      unfold compactNegationFormulaTagBranchPayloadEnvelopeFromData
      change compactNegationFormulaTagLargeBranchPayloadEnvelope tag mapped <= _
      unfold compactNegationFormulaTagPublicFinitePayloadEnvelope
      omega

theorem
    compactNegationFormulaTagExplicitHybridCertificateFromData_structuralPayloadBound_le_public
    (tag mapped : Nat)
    (data : CompactNegationFormulaTagCheckedBranchData tag mapped) :
    hybridFormulaStructuralPayloadBound
        (compactNegationFormulaTagExplicitHybridCertificateFromData
          tag mapped data) <=
      compactNegationFormulaTagBranchPayloadEnvelopeFromData
        tag mapped data := by
  cases data with
  | even hsmall pair hpair htag hmapped =>
      let tagCertificate := tagLtEightCertificate tag hsmall
      let evenCertificate := compactNegationFormulaTagEvenWitnessCertificate
        tag mapped pair hpair htag hmapped
      let witnessCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := ∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped)
          evenCertificate
      let smallCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          tagCertificate witnessCertificate
      have htagResource :=
        tagLtEightCertificate_structuralPayloadBound_le_public tag hsmall
      have hevenResource :=
        compactNegationFormulaTagEvenWitnessCertificate_structuralPayloadBound_le_public
          tag mapped pair hpair htag hmapped
      have hwitness := transparentHybridDisjunctionLeftPayloadBound_le
        (right := ∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped)
        evenCertificate _ hevenResource
      have hsmall := transparentHybridConjunctionPayloadBound_le
        tagCertificate witnessCertificate _ _ htagResource hwitness
      have houter := transparentHybridDisjunctionLeftPayloadBound_le
        (right :=
          (“8 ≤ !!(shortBinaryNumeralTerm tag)” : ValuationFormula) ⋏
            “!!(shortBinaryNumeralTerm mapped) =
              !!(shortBinaryNumeralTerm tag)”) smallCertificate _ hsmall
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right :=
              (“8 ≤ !!(shortBinaryNumeralTerm tag)” : ValuationFormula) ⋏
                “!!(shortBinaryNumeralTerm mapped) =
                  !!(shortBinaryNumeralTerm tag)”) smallCertificate) <= _
      simpa only [
        compactNegationFormulaTagBranchPayloadEnvelopeFromData,
        tagCertificate, evenCertificate, witnessCertificate,
        smallCertificate] using houter
  | odd hsmall pair hpair htag hmapped =>
      let tagCertificate := tagLtEightCertificate tag hsmall
      let oddCertificate := compactNegationFormulaTagOddWitnessCertificate
        tag mapped pair hpair htag hmapped
      let witnessCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped)
          oddCertificate
      let smallCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          tagCertificate witnessCertificate
      have htagResource :=
        tagLtEightCertificate_structuralPayloadBound_le_public tag hsmall
      have hoddResource :=
        compactNegationFormulaTagOddWitnessCertificate_structuralPayloadBound_le_public
          tag mapped pair hpair htag hmapped
      have hwitness := transparentHybridDisjunctionRightPayloadBound_le
        (left := ∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped)
        oddCertificate _ hoddResource
      have hsmall := transparentHybridConjunctionPayloadBound_le
        tagCertificate witnessCertificate _ _ htagResource hwitness
      have houter := transparentHybridDisjunctionLeftPayloadBound_le
        (right :=
          (“8 ≤ !!(shortBinaryNumeralTerm tag)” : ValuationFormula) ⋏
            “!!(shortBinaryNumeralTerm mapped) =
              !!(shortBinaryNumeralTerm tag)”) smallCertificate _ hsmall
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right :=
              (“8 ≤ !!(shortBinaryNumeralTerm tag)” : ValuationFormula) ⋏
                “!!(shortBinaryNumeralTerm mapped) =
                  !!(shortBinaryNumeralTerm tag)”) smallCertificate) <= _
      simpa only [
        compactNegationFormulaTagBranchPayloadEnvelopeFromData,
        tagCertificate, oddCertificate, witnessCertificate,
        smallCertificate] using houter
  | large hlarge hmapped =>
      let lowerCertificate := eightLeTagCertificate tag hlarge
      let equalityCertificate :=
        mappedTagEqualityCertificate tag mapped hmapped
      let largeCertificate :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          lowerCertificate equalityCertificate
      have hlowerResource :=
        eightLeTagCertificate_structuralPayloadBound_le_public tag hlarge
      have hequalityResource :=
        mappedTagEqualityCertificate_structuralPayloadBound_le_public
          tag mapped hmapped
      have hlarge := transparentHybridConjunctionPayloadBound_le
        lowerCertificate equalityCertificate _ _ hlowerResource
          hequalityResource
      have houter := transparentHybridDisjunctionRightPayloadBound_le
        (left :=
          (“!!(shortBinaryNumeralTerm tag) < 8” : ValuationFormula) ⋏
            ((∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped) ⋎
              (∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped)))
        largeCertificate _ hlarge
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left :=
              (“!!(shortBinaryNumeralTerm tag) < 8” : ValuationFormula) ⋏
                ((∃⁰ compactNegationFormulaTagEvenWitnessBody tag mapped) ⋎
                  (∃⁰ compactNegationFormulaTagOddWitnessBody tag mapped)))
            largeCertificate) <= _
      simpa only [
        compactNegationFormulaTagBranchPayloadEnvelopeFromData,
        lowerCertificate, equalityCertificate, largeCertificate] using houter

noncomputable def compactNegationFormulaTagGraphPayloadEnvelope
    (tag mapped : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) : Nat :=
  compactNegationFormulaTagBranchPayloadEnvelopeFromData tag mapped
    (compactNegationFormulaTagCheckedBranchDataOfGraph tag mapped hgraph)

theorem compactNegationFormulaTagGraphPayloadEnvelope_le_publicFinite
    (tag mapped : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) :
    compactNegationFormulaTagGraphPayloadEnvelope tag mapped hgraph <=
      compactNegationFormulaTagPublicFinitePayloadEnvelope tag mapped := by
  unfold compactNegationFormulaTagGraphPayloadEnvelope
  exact
    compactNegationFormulaTagBranchPayloadEnvelopeFromData_le_publicFinite
      tag mapped
      (compactNegationFormulaTagCheckedBranchDataOfGraph tag mapped hgraph)

theorem
    compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tag mapped : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) :
    hybridFormulaStructuralPayloadBound
        (compactNegationFormulaTagExplicitHybridCertificateOfGraph
          tag mapped hgraph) <=
      compactNegationFormulaTagGraphPayloadEnvelope tag mapped hgraph := by
  let data := compactNegationFormulaTagCheckedBranchDataOfGraph
    tag mapped hgraph
  have hbound :=
    compactNegationFormulaTagExplicitHybridCertificateFromData_structuralPayloadBound_le_public
      tag mapped data
  simpa only [compactNegationFormulaTagExplicitHybridCertificateOfGraph,
    compactNegationFormulaTagGraphPayloadEnvelope,
    hybridFormulaStructuralPayloadBound, data] using hbound

theorem
    compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tag mapped : Nat)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) :
    hybridFormulaStructuralPayloadBound
        (compactNegationFormulaTagExplicitHybridCertificateOfGraph
          tag mapped hgraph) <=
      compactNegationFormulaTagPublicFinitePayloadEnvelope tag mapped := by
  exact
    (compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tag mapped hgraph).trans
    (compactNegationFormulaTagGraphPayloadEnvelope_le_publicFinite
      tag mapped hgraph)

#print axioms pairLtFourCertificate_structuralPayloadBound_le_public
#print axioms tagLtEightCertificate_structuralPayloadBound_le_public
#print axioms evenTagEqualityCertificate_structuralPayloadBound_le_public
#print axioms oddTagEqualityCertificate_structuralPayloadBound_le_public
#print axioms mappedSuccessorCertificate_structuralPayloadBound_le_public
#print axioms tagMappedSuccessorCertificate_structuralPayloadBound_le_public
#print axioms mappedTagEqualityCertificate_structuralPayloadBound_le_public
#print axioms eightLeTagCertificate_structuralPayloadBound_le_public
#print axioms
  compactNegationFormulaTagEvenWitnessCertificate_structuralPayloadBound_le_public
#print axioms
  compactNegationFormulaTagOddWitnessCertificate_structuralPayloadBound_le_public
#print axioms
  compactNegationFormulaTagExplicitHybridCertificateFromData_structuralPayloadBound_le_public
#print axioms
  compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
#print axioms
  compactNegationFormulaTagExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectNegationFormulaTagPublicBounds
