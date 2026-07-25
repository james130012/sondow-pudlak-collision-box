import integration.FoundationCompactNumericListedDirectNegationFormulaTagFormulaFixedBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds

/-!
# Fixed atomic resources for the negation tag graph

All tag leaves use one closed-term code coordinate.  The bounded branch witness
`pair < 4` receives a constant numeral budget, while tag and mapped values use
the caller's common bit bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNegationFormulaTagAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds

private abbrev tagZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation

def negationFormulaTagAtomicTermCodePolynomial (bitBound : Nat) : Nat :=
  let base :=
    binaryNumeralTermCodeEnvelope bitBound +
      binaryNumeralTermCodeEnvelope 2 +
      (binaryTermCode (‘1’ : ValuationTerm)).length +
      (binaryTermCode (‘2’ : ValuationTerm)).length +
      (binaryTermCode (‘4’ : ValuationTerm)).length +
      (binaryTermCode (‘8’ : ValuationTerm)).length + 1
  4 * base +
    4 * (binaryFunctionTermCodeOverhead Language.Add.add +
      binaryFunctionTermCodeOverhead Language.Mul.mul + 1) + 1

def negationFormulaTagAtomicFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (negationFormulaTagAtomicTermCodePolynomial bitBound)

def negationFormulaTagLeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  appendSourcePrefixLeFixedPayloadPolynomial
    (negationFormulaTagAtomicTermCodePolynomial bitBound)

theorem arithmeticMulTerm_eq_paMulTerm
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm) = paMulTerm left right := by
  rfl

theorem arithmeticAddTerm_eq_paAddTerm
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) = paAddTerm left right := by
  rfl

private theorem binaryFunctionTerm_freeVariables_tagFixed
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

theorem paAddTerm_freeVariables_tagFixed
    (left right : ValuationTerm) :
    (paAddTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseAddTerm_eq_paAddTerm]
  exact binaryFunctionTerm_freeVariables_tagFixed
    Language.Add.add left right

theorem paMulTerm_freeVariables_tagFixed
    (left right : ValuationTerm) :
    (paMulTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  exact binaryFunctionTerm_freeVariables_tagFixed
    Language.Mul.mul left right

private theorem pairSize_le_two (pair : Nat) (hpair : pair < 4) :
    Nat.size pair <= 2 := by
  have hcases : pair = 0 ∨ pair = 1 ∨ pair = 2 ∨ pair = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> decide

private theorem tagSimpleTermCode_le
    (term : ValuationTerm) (bitBound : Nat)
    (hterm :
      (binaryTermCode term).length <=
        binaryNumeralTermCodeEnvelope bitBound ∨
      (binaryTermCode term).length <=
        binaryNumeralTermCodeEnvelope 2 ∨
      term = (‘1’ : ValuationTerm) ∨ term = (‘2’ : ValuationTerm) ∨
      term = (‘4’ : ValuationTerm) ∨ term = (‘8’ : ValuationTerm)) :
    (binaryTermCode term).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound := by
  rcases hterm with hterm | hterm | rfl | rfl | rfl | rfl <;>
    unfold negationFormulaTagAtomicTermCodePolynomial <;>
    dsimp only <;> omega

theorem tagShortNumeralCode_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound :=
  tagSimpleTermCode_le _ bitBound
    (Or.inl (binaryNumeralTerm_code_length_le_envelope value bitBound hvalue))

theorem pairShortNumeralCode_le
    (pair bitBound : Nat) (hpair : pair < 4) :
    (binaryTermCode (shortBinaryNumeralTerm pair)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound := by
  have hsize : Nat.size pair <= 2 := pairSize_le_two pair hpair
  exact tagSimpleTermCode_le _ bitBound
    (Or.inr (Or.inl
      (binaryNumeralTerm_code_length_le_envelope pair 2 hsize)))

private theorem tagOneCode_le (bitBound : Nat) :
    (binaryTermCode (‘1’ : ValuationTerm)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound :=
  tagSimpleTermCode_le _ bitBound (Or.inr (Or.inr (Or.inl rfl)))

private theorem tagTwoCode_le (bitBound : Nat) :
    (binaryTermCode (‘2’ : ValuationTerm)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound :=
  tagSimpleTermCode_le _ bitBound
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem tagFourCode_le (bitBound : Nat) :
    (binaryTermCode (‘4’ : ValuationTerm)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound :=
  tagSimpleTermCode_le _ bitBound
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

private theorem tagEightCode_le (bitBound : Nat) :
    (binaryTermCode (‘8’ : ValuationTerm)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound :=
  tagSimpleTermCode_le _ bitBound
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem tagMulTwoPairCode_le
    (pair bitBound : Nat) (hpair : pair < 4) :
    (binaryTermCode
      (‘2 * !!(shortBinaryNumeralTerm pair)’ : ValuationTerm)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound := by
  have hpairSize := pairSize_le_two pair hpair
  have hpairCode :=
    binaryNumeralTerm_code_length_le_envelope pair 2 hpairSize
  have hraw := paMulTerm_code_length_le (‘2’ : ValuationTerm)
    (shortBinaryNumeralTerm pair)
  rw [arithmeticMulTerm_eq_paMulTerm]
  unfold negationFormulaTagAtomicTermCodePolynomial
  dsimp only
  omega

theorem tagMulTwoPairAddOneCode_le
    (pair bitBound : Nat) (hpair : pair < 4) :
    (binaryTermCode
      (‘2 * !!(shortBinaryNumeralTerm pair) + 1’ :
        ValuationTerm)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound := by
  have hpairSize := pairSize_le_two pair hpair
  have hpairCode :=
    binaryNumeralTerm_code_length_le_envelope pair 2 hpairSize
  have hproductRaw := paMulTerm_code_length_le (‘2’ : ValuationTerm)
    (shortBinaryNumeralTerm pair)
  have hproduct :
      (binaryTermCode
        (‘2 * !!(shortBinaryNumeralTerm pair)’ : ValuationTerm)).length <=
        (binaryTermCode (‘2’ : ValuationTerm)).length +
          binaryNumeralTermCodeEnvelope 2 +
          binaryFunctionTermCodeOverhead Language.Mul.mul := by
    rw [arithmeticMulTerm_eq_paMulTerm]
    omega
  have hraw := paAddTerm_code_length_le
    (‘2 * !!(shortBinaryNumeralTerm pair)’ : ValuationTerm)
    (‘1’ : ValuationTerm)
  rw [arithmeticAddTerm_eq_paAddTerm]
  unfold negationFormulaTagAtomicTermCodePolynomial
  dsimp only
  omega

theorem tagShortAddOneCode_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode
      (‘!!(shortBinaryNumeralTerm value) + 1’ : ValuationTerm)).length <=
      negationFormulaTagAtomicTermCodePolynomial bitBound := by
  have hvalueCode :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm value) (‘1’ : ValuationTerm)
  rw [arithmeticAddTerm_eq_paAddTerm]
  unfold negationFormulaTagAtomicTermCodePolynomial
  dsimp only
  omega

private theorem tagClosed (term : ValuationTerm)
    (hterm : term.freeVariables = ∅) : term.freeVariables ⊆ {0} := by
  rw [hterm]
  simp

theorem shortNumeralClosed (value : Nat) :
    (shortBinaryNumeralTerm value : ValuationTerm).freeVariables ⊆ {0} :=
  tagClosed _ (shortBinaryNumeralTerm_freeVariables_eq_empty value)

private theorem arithmeticConstantClosed (value : ValuationTerm)
    (hvalue : value = (‘1’ : ValuationTerm) ∨
      value = (‘2’ : ValuationTerm) ∨ value = (‘4’ : ValuationTerm) ∨
      value = (‘8’ : ValuationTerm)) :
    value.freeVariables ⊆ {0} := by
  rcases hvalue with rfl | rfl | rfl | rfl <;>
    simp [LO.FirstOrder.Semiterm.Operator.operator]

theorem tagMulTwoPairClosed (pair : Nat) :
    (‘2 * !!(shortBinaryNumeralTerm pair)’ :
      ValuationTerm).freeVariables ⊆ {0} := by
  rw [arithmeticMulTerm_eq_paMulTerm, paMulTerm_freeVariables_tagFixed,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  have htwo :
      ((‘2’ : ValuationTerm).freeVariables = ∅) := by
    simp [LO.FirstOrder.Semiterm.Operator.operator]
  rw [htwo]
  simp

theorem tagMulTwoPair_freeVariables_eq_empty (pair : Nat) :
    (‘2 * !!(shortBinaryNumeralTerm pair)’ :
      ValuationTerm).freeVariables = ∅ := by
  rw [arithmeticMulTerm_eq_paMulTerm, paMulTerm_freeVariables_tagFixed,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  simp [LO.FirstOrder.Semiterm.Operator.operator]

theorem tagMulTwoPairAddOneClosed (pair : Nat) :
    (‘2 * !!(shortBinaryNumeralTerm pair) + 1’ :
      ValuationTerm).freeVariables ⊆ {0} := by
  rw [arithmeticAddTerm_eq_paAddTerm,
    paAddTerm_freeVariables_tagFixed,
    arithmeticMulTerm_eq_paMulTerm, paMulTerm_freeVariables_tagFixed,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  have htwo :
      ((‘2’ : ValuationTerm).freeVariables = ∅) := by
    simp [LO.FirstOrder.Semiterm.Operator.operator]
  have hone :
      ((‘1’ : ValuationTerm).freeVariables = ∅) := by
    simp [LO.FirstOrder.Semiterm.Operator.operator]
  rw [htwo, hone]
  simp

theorem tagMulTwoPairAddOne_freeVariables_eq_empty (pair : Nat) :
    (‘2 * !!(shortBinaryNumeralTerm pair) + 1’ :
      ValuationTerm).freeVariables = ∅ := by
  rw [arithmeticAddTerm_eq_paAddTerm, paAddTerm_freeVariables_tagFixed,
    arithmeticMulTerm_eq_paMulTerm, paMulTerm_freeVariables_tagFixed,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  simp [LO.FirstOrder.Semiterm.Operator.operator]

theorem tagShortAddOneClosed (value : Nat) :
    (‘!!(shortBinaryNumeralTerm value) + 1’ :
      ValuationTerm).freeVariables ⊆ {0} := by
  rw [arithmeticAddTerm_eq_paAddTerm,
    paAddTerm_freeVariables_tagFixed,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  have hone :
      ((‘1’ : ValuationTerm).freeVariables = ∅) := by
    simp [LO.FirstOrder.Semiterm.Operator.operator]
  rw [hone]
  simp

theorem tagShortAddOne_freeVariables_eq_empty (value : Nat) :
    (‘!!(shortBinaryNumeralTerm value) + 1’ :
      ValuationTerm).freeVariables = ∅ := by
  rw [arithmeticAddTerm_eq_paAddTerm, paAddTerm_freeVariables_tagFixed,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  simp [LO.FirstOrder.Semiterm.Operator.operator]

theorem pairLtFourCertificate_structuralPayloadBound_le_fixed
    (pair bitBound : Nat) (hpair : pair < 4) :
    hybridFormulaStructuralPayloadBound
        (pairLtFourCertificate pair hpair) <=
      negationFormulaTagAtomicFixedPayloadPolynomial bitBound := by
  have hpublic :=
    pairLtFourCertificate_structuralPayloadBound_le_public pair hpair
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed tagZeroValuation
      Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm pair, (‘4’ : ValuationTerm)] 0
      (negationFormulaTagAtomicTermCodePolynomial bitBound)
      (shortNumeralClosed pair)
      (arithmeticConstantClosed (‘4’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inl rfl))))
      (by rfl) (pairShortNumeralCode_le pair bitBound hpair)
      (tagFourCode_le bitBound)
  unfold pairLtFourStructuralPayloadPolynomial at hpublic
  unfold negationFormulaTagAtomicFixedPayloadPolynomial
  exact hpublic.trans hfixed

theorem tagLtEightCertificate_structuralPayloadBound_le_fixed
    (tag bitBound : Nat) (htag : tag < 8)
    (htagSize : Nat.size tag <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (tagLtEightCertificate tag htag) <=
      negationFormulaTagAtomicFixedPayloadPolynomial bitBound := by
  have hpublic :=
    tagLtEightCertificate_structuralPayloadBound_le_public tag htag
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed tagZeroValuation
      Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm tag, (‘8’ : ValuationTerm)] 0
      (negationFormulaTagAtomicTermCodePolynomial bitBound)
      (shortNumeralClosed tag)
      (arithmeticConstantClosed (‘8’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr rfl))))
      (by rfl) (tagShortNumeralCode_le tag bitBound htagSize)
      (tagEightCode_le bitBound)
  unfold tagLtEightStructuralPayloadPolynomial at hpublic
  unfold negationFormulaTagAtomicFixedPayloadPolynomial
  exact hpublic.trans hfixed

theorem evenTagEqualityCertificate_structuralPayloadBound_le_fixed
    (tag pair bitBound : Nat)
    (htag : tag = 2 * pair) (hpair : pair < 4)
    (htagSize : Nat.size tag <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (evenTagEqualityCertificate tag pair htag) <=
      negationFormulaTagAtomicFixedPayloadPolynomial bitBound := by
  have hpublic :=
    evenTagEqualityCertificate_structuralPayloadBound_le_public tag pair htag
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed tagZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm tag,
        (‘2 * !!(shortBinaryNumeralTerm pair)’ : ValuationTerm)] 0
      (negationFormulaTagAtomicTermCodePolynomial bitBound)
      (shortNumeralClosed tag) (tagMulTwoPairClosed pair) (by rfl)
      (tagShortNumeralCode_le tag bitBound htagSize)
      (tagMulTwoPairCode_le pair bitBound hpair)
  unfold evenTagEqualityStructuralPayloadPolynomial at hpublic
  unfold negationFormulaTagAtomicFixedPayloadPolynomial
  exact hpublic.trans hfixed

theorem oddTagEqualityCertificate_structuralPayloadBound_le_fixed
    (tag pair bitBound : Nat)
    (htag : tag = 2 * pair + 1) (hpair : pair < 4)
    (htagSize : Nat.size tag <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (oddTagEqualityCertificate tag pair htag) <=
      negationFormulaTagAtomicFixedPayloadPolynomial bitBound := by
  have hpublic :=
    oddTagEqualityCertificate_structuralPayloadBound_le_public tag pair htag
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed tagZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm tag,
        (‘2 * !!(shortBinaryNumeralTerm pair) + 1’ : ValuationTerm)] 0
      (negationFormulaTagAtomicTermCodePolynomial bitBound)
      (shortNumeralClosed tag) (tagMulTwoPairAddOneClosed pair) (by rfl)
      (tagShortNumeralCode_le tag bitBound htagSize)
      (tagMulTwoPairAddOneCode_le pair bitBound hpair)
  unfold oddTagEqualityStructuralPayloadPolynomial at hpublic
  unfold negationFormulaTagAtomicFixedPayloadPolynomial
  exact hpublic.trans hfixed

theorem mappedSuccessorCertificate_structuralPayloadBound_le_fixed
    (tag mapped bitBound : Nat) (hmapped : mapped = tag + 1)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (mappedSuccessorCertificate tag mapped hmapped) <=
      negationFormulaTagAtomicFixedPayloadPolynomial bitBound := by
  have hpublic :=
    mappedSuccessorCertificate_structuralPayloadBound_le_public
      tag mapped hmapped
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed tagZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm mapped,
        (‘!!(shortBinaryNumeralTerm tag) + 1’ : ValuationTerm)] 0
      (negationFormulaTagAtomicTermCodePolynomial bitBound)
      (shortNumeralClosed mapped) (tagShortAddOneClosed tag) (by rfl)
      (tagShortNumeralCode_le mapped bitBound hmappedSize)
      (tagShortAddOneCode_le tag bitBound htagSize)
  unfold mappedSuccessorStructuralPayloadPolynomial at hpublic
  unfold negationFormulaTagAtomicFixedPayloadPolynomial
  exact hpublic.trans hfixed

theorem tagMappedSuccessorCertificate_structuralPayloadBound_le_fixed
    (tag mapped bitBound : Nat) (htag : tag = mapped + 1)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (tagMappedSuccessorCertificate tag mapped htag) <=
      negationFormulaTagAtomicFixedPayloadPolynomial bitBound := by
  have hpublic :=
    tagMappedSuccessorCertificate_structuralPayloadBound_le_public
      tag mapped htag
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed tagZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm tag,
        (‘!!(shortBinaryNumeralTerm mapped) + 1’ : ValuationTerm)] 0
      (negationFormulaTagAtomicTermCodePolynomial bitBound)
      (shortNumeralClosed tag) (tagShortAddOneClosed mapped) (by rfl)
      (tagShortNumeralCode_le tag bitBound htagSize)
      (tagShortAddOneCode_le mapped bitBound hmappedSize)
  unfold tagMappedSuccessorStructuralPayloadPolynomial at hpublic
  unfold negationFormulaTagAtomicFixedPayloadPolynomial
  exact hpublic.trans hfixed

theorem mappedTagEqualityCertificate_structuralPayloadBound_le_fixed
    (tag mapped bitBound : Nat) (hmapped : mapped = tag)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (mappedTagEqualityCertificate tag mapped hmapped) <=
      negationFormulaTagAtomicFixedPayloadPolynomial bitBound := by
  have hpublic :=
    mappedTagEqualityCertificate_structuralPayloadBound_le_public
      tag mapped hmapped
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed tagZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm mapped, shortBinaryNumeralTerm tag] 0
      (negationFormulaTagAtomicTermCodePolynomial bitBound)
      (shortNumeralClosed mapped) (shortNumeralClosed tag) (by rfl)
      (tagShortNumeralCode_le mapped bitBound hmappedSize)
      (tagShortNumeralCode_le tag bitBound htagSize)
  unfold mappedTagEqualityStructuralPayloadPolynomial at hpublic
  unfold negationFormulaTagAtomicFixedPayloadPolynomial
  exact hpublic.trans hfixed

theorem eightTagEqualityPayloadResource_le_fixed
    (tag bitBound : Nat) (htagSize : Nat.size tag <= bitBound) :
    compilePositiveRelationPayloadResource tagZeroValuation Language.Eq.eq
        ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag] <=
      negationFormulaTagAtomicFixedPayloadPolynomial bitBound := by
  have hpublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      tagZeroValuation Language.Eq.eq
      ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag]
      (arithmeticConstantClosed (‘8’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr rfl))))
      (shortNumeralClosed tag)
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed tagZeroValuation
      Language.Eq.eq
      ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag] 0
      (negationFormulaTagAtomicTermCodePolynomial bitBound)
      (arithmeticConstantClosed (‘8’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr rfl))))
      (shortNumeralClosed tag) (by rfl) (tagEightCode_le bitBound)
      (tagShortNumeralCode_le tag bitBound htagSize)
  exact hpublic.trans hfixed

theorem eightTagStrictPayloadResource_le_fixed
    (tag bitBound : Nat) (htagSize : Nat.size tag <= bitBound) :
    compilePositiveRelationPayloadResource tagZeroValuation
        Language.ORing.Rel.lt
        ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag] <=
      negationFormulaTagAtomicFixedPayloadPolynomial bitBound := by
  have hpublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      tagZeroValuation Language.ORing.Rel.lt
      ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag]
      (arithmeticConstantClosed (‘8’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr rfl))))
      (shortNumeralClosed tag)
  have hfixed :=
    compilePositiveRelationPayloadPolynomial_le_fixed tagZeroValuation
      Language.ORing.Rel.lt
      ![(‘8’ : ValuationTerm), shortBinaryNumeralTerm tag] 0
      (negationFormulaTagAtomicTermCodePolynomial bitBound)
      (arithmeticConstantClosed (‘8’ : ValuationTerm)
        (Or.inr (Or.inr (Or.inr rfl))))
      (shortNumeralClosed tag) (by rfl) (tagEightCode_le bitBound)
      (tagShortNumeralCode_le tag bitBound htagSize)
  exact hpublic.trans hfixed

#print axioms pairLtFourCertificate_structuralPayloadBound_le_fixed
#print axioms tagLtEightCertificate_structuralPayloadBound_le_fixed
#print axioms evenTagEqualityCertificate_structuralPayloadBound_le_fixed
#print axioms oddTagEqualityCertificate_structuralPayloadBound_le_fixed
#print axioms mappedSuccessorCertificate_structuralPayloadBound_le_fixed
#print axioms tagMappedSuccessorCertificate_structuralPayloadBound_le_fixed
#print axioms mappedTagEqualityCertificate_structuralPayloadBound_le_fixed
#print axioms eightTagEqualityPayloadResource_le_fixed
#print axioms eightTagStrictPayloadResource_le_fixed

end FoundationCompactNumericListedDirectNegationFormulaTagAtomicFixedBounds
