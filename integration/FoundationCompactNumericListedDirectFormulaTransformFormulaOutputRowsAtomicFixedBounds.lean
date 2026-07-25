import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsFormulaFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Fixed atomic resources for formula-transform output rows

The count equality is compiled from three closed short numerals and one binary
addition.  Its structural payload therefore has a bound depending only on the
common input bit bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds

private abbrev outputRowsAtomicZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation

def outputRowsAtomicTermCodePolynomial (bitBound : Nat) : Nat :=
  3 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (‘0’ : ValuationTerm)).length +
    (binaryTermCode (‘1’ : ValuationTerm)).length +
    (binaryTermCode (‘2’ : ValuationTerm)).length +
    (binaryTermCode (‘4’ : ValuationTerm)).length +
    (binaryTermCode (‘5’ : ValuationTerm)).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def outputRowsPositiveAtomicFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (outputRowsAtomicTermCodePolynomial bitBound)

def outputRowsNegativeAtomicFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compileNegativeRelationFixedPayloadPolynomial 0
    (outputRowsAtomicTermCodePolynomial bitBound)

def outputRowsAtomicLeafFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * outputRowsAtomicTermCodePolynomial bitBound +
    (binaryNatCode 0).length + (binaryNatCode 2).length + 128

def outputRowsAtomicFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * outputRowsAtomicLeafFormulaCodePolynomial bitBound +
    (binaryNatCode 5).length + 1

def outputRowsNativeLeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  2 * outputRowsPositiveAtomicFixedPayloadPolynomial bitBound +
    3 * generalContextAssemblyEnvelope
      (outputRowsAtomicFormulaCodePolynomial bitBound)

private theorem outputRowsNativeAddTerm_eq_paAddTerm
    (left right : ValuationTerm) :
    nativeAddTerm left right = paAddTerm left right := by
  rfl

private theorem binaryFunctionTerm_freeVariables_outputRowsAtomic
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

private theorem outputRowsNativeAddTerm_freeVariables
    (left right : ValuationTerm) :
    (nativeAddTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [outputRowsNativeAddTerm_eq_paAddTerm]
  exact binaryFunctionTerm_freeVariables_outputRowsAtomic Language.Add.add
    left right

theorem outputRowsShortNumeralCode_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      outputRowsAtomicTermCodePolynomial bitBound := by
  have hraw :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  unfold outputRowsAtomicTermCodePolynomial
  omega

private theorem outputRowsOneCode_le (bitBound : Nat) :
    (binaryTermCode (‘1’ : ValuationTerm)).length <=
      outputRowsAtomicTermCodePolynomial bitBound := by
  unfold outputRowsAtomicTermCodePolynomial
  omega

theorem outputRowsModeLiteralCode_le
    (literal : ValuationTerm) (bitBound : Nat)
    (hliteral :
      literal = (‘0’ : ValuationTerm) ∨
      literal = (‘1’ : ValuationTerm) ∨
      literal = (‘2’ : ValuationTerm) ∨
      literal = (‘4’ : ValuationTerm) ∨
      literal = (‘5’ : ValuationTerm)) :
    (binaryTermCode literal).length <=
      outputRowsAtomicTermCodePolynomial bitBound := by
  rcases hliteral with rfl | rfl | rfl | rfl | rfl <;>
    unfold outputRowsAtomicTermCodePolynomial <;> omega

theorem outputRowsModeLiteral_closed
    (literal : ValuationTerm)
    (hliteral :
      literal = (‘0’ : ValuationTerm) ∨
      literal = (‘1’ : ValuationTerm) ∨
      literal = (‘2’ : ValuationTerm) ∨
      literal = (‘4’ : ValuationTerm) ∨
      literal = (‘5’ : ValuationTerm)) :
    literal.freeVariables = ∅ := by
  rcases hliteral with rfl | rfl | rfl | rfl | rfl <;>
    simp [LO.FirstOrder.Semiterm.Operator.operator,
      LO.FirstOrder.Semiterm.Operator.numeral_one,
      LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem outputRowsAddShortNumeralsCode_le
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    (binaryTermCode
      (nativeAddTerm (shortBinaryNumeralTerm left)
        (shortBinaryNumeralTerm right))).length <=
      outputRowsAtomicTermCodePolynomial bitBound := by
  have hleftCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hrightCode :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hright
  have hraw := paAddTerm_code_length_le
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
  rw [outputRowsNativeAddTerm_eq_paAddTerm]
  unfold outputRowsAtomicTermCodePolynomial
  omega

private theorem outputRowsAddShortNumerals_closed
    (left right : Nat) :
    (nativeAddTerm (shortBinaryNumeralTerm left)
      (shortBinaryNumeralTerm right)).freeVariables = ∅ := by
  rw [outputRowsNativeAddTerm_freeVariables,
    shortBinaryNumeralTerm_freeVariables_eq_empty,
    shortBinaryNumeralTerm_freeVariables_eq_empty]
  simp

theorem outputRowsCountStructuralEnvelope_le_fixed
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount bitBound : Nat)
    (hcurrentCountSize :
      Nat.size current.parserTokensCount <= bitBound)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (hnextCountSize : Nat.size next.parserTokensCount <= bitBound) :
    outputRowsNativeEqStructuralEnvelope
        (shortBinaryNumeralTerm current.parserTokensCount)
        (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
          (shortBinaryNumeralTerm next.parserTokensCount)) <=
      outputRowsPositiveAtomicFixedPayloadPolynomial bitBound := by
  unfold outputRowsNativeEqStructuralEnvelope
    outputRowsPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    outputRowsAtomicZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm current.parserTokensCount)
    (nativeAddTerm (shortBinaryNumeralTerm consumedCount)
      (shortBinaryNumeralTerm next.parserTokensCount))
    0 (outputRowsAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (outputRowsAddShortNumerals_closed _ _)
    (outputRowsShortNumeralCode_le _ bitBound hcurrentCountSize)
    (outputRowsAddShortNumeralsCode_le _ _ bitBound hconsumedSize
      hnextCountSize)

theorem consumedCountEqualityCertificate_structuralPayloadBound_le_fixed
    (current next : CompactFormulaTransformStateRowCoordinates)
    (consumedCount bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hcurrentCountSize :
      Nat.size current.parserTokensCount <= bitBound)
    (hconsumedSize : Nat.size consumedCount <= bitBound)
    (hnextCountSize : Nat.size next.parserTokensCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (consumedCountEqualityCertificate current next consumedCount hcount) <=
      outputRowsPositiveAtomicFixedPayloadPolynomial bitBound :=
  (consumedCountEqualityCertificate_structuralPayloadBound_le_transparent
    current next consumedCount hcount).trans
      (outputRowsCountStructuralEnvelope_le_fixed current next consumedCount
        bitBound hcurrentCountSize hconsumedSize hnextCountSize)

private theorem outputRowsOne_closed :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

theorem outputRowsBinaryRelation_closed
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (LO.FirstOrder.Semiformula.rel relationSymbol
      ![left, right]).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  ext candidate
  simp [hleft, hright]

theorem outputRowsBinaryRelationCode_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) (bitBound : Nat)
    (hleft :
      (binaryTermCode left).length <=
        outputRowsAtomicTermCodePolynomial bitBound)
    (hright :
      (binaryTermCode right).length <=
        outputRowsAtomicTermCodePolynomial bitBound) :
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right])).length <=
      outputRowsAtomicLeafFormulaCodePolynomial bitBound := by
  simp [binaryFormulaCode, Matrix.fun_eq_vec_two]
  have hrelationTag :
      (binaryNatCode (Encodable.encode relationSymbol)).length <= 128 := by
    cases relationSymbol <;> decide
  unfold outputRowsAtomicLeafFormulaCodePolynomial
  omega

private theorem outputRowsAtomicLeafFormulaCodePolynomial_le
    (bitBound : Nat) :
    outputRowsAtomicLeafFormulaCodePolynomial bitBound <=
      outputRowsAtomicFormulaCodePolynomial bitBound := by
  unfold outputRowsAtomicFormulaCodePolynomial
  omega

private theorem outputRowsBinaryDisjunctionCode_le
    (left right : ValuationFormula) (bitBound : Nat)
    (hleft :
      (binaryFormulaCode left).length <=
        outputRowsAtomicLeafFormulaCodePolynomial bitBound)
    (hright :
      (binaryFormulaCode right).length <=
        outputRowsAtomicLeafFormulaCodePolynomial bitBound) :
    (binaryFormulaCode (left ⋎ right)).length <=
      outputRowsAtomicFormulaCodePolynomial bitBound := by
  simp [binaryFormulaCode] at *
  unfold outputRowsAtomicFormulaCodePolynomial
  omega

theorem outputRowsConsumedPositiveStructuralEnvelope_le_fixed
    (consumedCount bitBound : Nat)
    (hconsumedSize : Nat.size consumedCount <= bitBound) :
    outputRowsNativeLeStructuralEnvelope (‘1’ : ValuationTerm)
        (shortBinaryNumeralTerm consumedCount) <=
      outputRowsNativeLeFixedPayloadPolynomial bitBound := by
  let left : ValuationTerm := (‘1’ : ValuationTerm)
  let right : ValuationTerm := shortBinaryNumeralTerm consumedCount
  let args : Fin 2 -> ValuationTerm := ![left, right]
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let syntaxResource := outputRowsAtomicFormulaCodePolynomial bitBound
  let atomResource := outputRowsPositiveAtomicFixedPayloadPolynomial bitBound
  let Gamma := valuationContext targetFormula.freeVariables
    outputRowsAtomicZeroValuation
  have hleftClosed : left.freeVariables = ∅ := outputRowsOne_closed
  have hrightClosed : right.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hleftCode :
      (binaryTermCode left).length <=
        outputRowsAtomicTermCodePolynomial bitBound :=
    outputRowsOneCode_le bitBound
  have hrightCode :
      (binaryTermCode right).length <=
        outputRowsAtomicTermCodePolynomial bitBound :=
    outputRowsShortNumeralCode_le _ bitBound hconsumedSize
  have hequalityClosed : equalityFormula.freeVariables = ∅ := by
    exact outputRowsBinaryRelation_closed Language.Eq.eq left right
      hleftClosed hrightClosed
  have hstrictClosed : strictFormula.freeVariables = ∅ := by
    exact outputRowsBinaryRelation_closed Language.ORing.Rel.lt left right
      hleftClosed hrightClosed
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hequalityClosed,
      hstrictClosed]
    simp
  have hequalityCode :
      (binaryFormulaCode equalityFormula).length <= syntaxResource := by
    exact (outputRowsBinaryRelationCode_le Language.Eq.eq left right bitBound
      hleftCode hrightCode).trans
        (outputRowsAtomicLeafFormulaCodePolynomial_le bitBound)
  have hstrictCode :
      (binaryFormulaCode strictFormula).length <= syntaxResource := by
    exact (outputRowsBinaryRelationCode_le Language.ORing.Rel.lt left right
      bitBound hleftCode hrightCode).trans
        (outputRowsAtomicLeafFormulaCodePolynomial_le bitBound)
  have htargetCode :
      (binaryFormulaCode targetFormula).length <= syntaxResource := by
    exact outputRowsBinaryDisjunctionCode_le equalityFormula strictFormula
      bitBound
      (outputRowsBinaryRelationCode_le Language.Eq.eq left right bitBound
        hleftCode hrightCode)
      (outputRowsBinaryRelationCode_le Language.ORing.Rel.lt left right
        bitBound hleftCode hrightCode)
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold outputRowsAtomicFormulaCodePolynomial
    omega
  have hcontext : formulaCodeSum Gamma <= syntaxResource := by
    dsimp only [Gamma]
    rw [htargetClosed]
    simp [valuationContext, formulaCodeSum]
  have hequalityResource :
      compilePositiveRelationPayloadResource outputRowsAtomicZeroValuation
          Language.Eq.eq args <= atomResource := by
    dsimp only [atomResource, args, left, right]
    unfold outputRowsPositiveAtomicFixedPayloadPolynomial
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed
      outputRowsAtomicZeroValuation Language.Eq.eq
      (‘1’ : ValuationTerm) (shortBinaryNumeralTerm consumedCount)
      0 (outputRowsAtomicTermCodePolynomial bitBound) hleftClosed hrightClosed
      hleftCode hrightCode
  have hstrictResource :
      compilePositiveRelationPayloadResource outputRowsAtomicZeroValuation
          Language.ORing.Rel.lt args <= atomResource := by
    dsimp only [atomResource, args, left, right]
    unfold outputRowsPositiveAtomicFixedPayloadPolynomial
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed
      outputRowsAtomicZeroValuation Language.ORing.Rel.lt
      (‘1’ : ValuationTerm) (shortBinaryNumeralTerm consumedCount)
      0 (outputRowsAtomicTermCodePolynomial bitBound) hleftClosed hrightClosed
      hleftCode hrightCode
  have hequalityInsert : formulaCodeSum (insert equalityFormula Gamma) <=
      generalContextCoordinate syntaxResource := by
    have hraw := formulaCodeSum_insert_le Gamma equalityFormula
    unfold generalContextCoordinate
    omega
  have hstrictInsert : formulaCodeSum (insert strictFormula Gamma) <=
      generalContextCoordinate syntaxResource := by
    have hraw := formulaCodeSum_insert_le Gamma strictFormula
    unfold generalContextCoordinate
    omega
  have hweakEquality := weakeningFullAssemblyCost_le_general
    (insert equalityFormula Gamma) syntaxResource hequalityInsert
  have hweakStrict := weakeningFullAssemblyCost_le_general
    (insert strictFormula Gamma) syntaxResource hstrictInsert
  have hdisjunction := disjunctionFullAssemblyCost_le_general Gamma
    equalityFormula strictFormula syntaxResource hpositive hcontext
    hequalityCode hstrictCode htargetCode
  have hsum :
      compilePositiveRelationPayloadResource outputRowsAtomicZeroValuation
          Language.Eq.eq args +
        compilePositiveRelationPayloadResource outputRowsAtomicZeroValuation
          Language.ORing.Rel.lt args +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert equalityFormula Gamma) +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert strictFormula Gamma) +
        FoundationCompactCertifiedContextProof.CertifiedPAContextProof.disjunctionFullAssemblyCost
          Gamma equalityFormula strictFormula <=
        2 * atomResource +
          3 * generalContextAssemblyEnvelope syntaxResource := by
    omega
  simpa [outputRowsNativeLeStructuralEnvelope,
    outputRowsNativeLeFixedPayloadPolynomial, outputRowsAtomicZeroValuation,
    FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation,
    left, right, args, equalityFormula, strictFormula, targetFormula, Gamma,
    syntaxResource, atomResource] using hsum

theorem consumedCountPositiveCertificate_structuralPayloadBound_le_fixed
    (consumedCount bitBound : Nat)
    (hpositive : 1 <= consumedCount)
    (hconsumedSize : Nat.size consumedCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (consumedCountPositiveCertificate consumedCount hpositive) <=
      outputRowsNativeLeFixedPayloadPolynomial bitBound :=
  (consumedCountPositiveCertificate_structuralPayloadBound_le_transparent
    consumedCount hpositive).trans
      (outputRowsConsumedPositiveStructuralEnvelope_le_fixed consumedCount
        bitBound hconsumedSize)

theorem outputRowsNativeEqStructuralEnvelope_le_fixed
    (mode : Nat) (literal : ValuationTerm) (bitBound : Nat)
    (hmodeSize : Nat.size mode <= bitBound)
    (hliteralClosed : literal.freeVariables = ∅)
    (hliteralCode :
      (binaryTermCode literal).length <=
        outputRowsAtomicTermCodePolynomial bitBound) :
    outputRowsNativeEqStructuralEnvelope (shortBinaryNumeralTerm mode)
        literal <=
      outputRowsPositiveAtomicFixedPayloadPolynomial bitBound := by
  unfold outputRowsNativeEqStructuralEnvelope
    outputRowsPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    outputRowsAtomicZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm mode) literal 0
    (outputRowsAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _) hliteralClosed
    (outputRowsShortNumeralCode_le mode bitBound hmodeSize) hliteralCode

theorem modeNativeEqualityCertificate_structuralPayloadBound_le_fixed
    (mode : Nat) (literal : ValuationTerm) (expected bitBound : Nat)
    (hliteralValue :
      termValue outputRowsAtomicZeroValuation literal = expected)
    (heq : mode = expected)
    (hmodeSize : Nat.size mode <= bitBound)
    (hliteralClosed : literal.freeVariables = ∅)
    (hliteralCode :
      (binaryTermCode literal).length <=
        outputRowsAtomicTermCodePolynomial bitBound) :
    hybridFormulaStructuralPayloadBound
        (modeNativeEqualityCertificate mode literal expected
          hliteralValue heq) <=
      outputRowsPositiveAtomicFixedPayloadPolynomial bitBound := by
  have htransparent :=
    modeNativeEqualityCertificate_structuralPayloadBound_le_transparent
      mode literal expected hliteralValue heq
  exact htransparent.trans
    (outputRowsNativeEqStructuralEnvelope_le_fixed mode literal bitBound
      hmodeSize hliteralClosed hliteralCode)

theorem consumedCountZeroCertificate_structuralPayloadBound_le_fixed
    (consumedCount bitBound : Nat) (hzero : consumedCount = 0)
    (hconsumedSize : Nat.size consumedCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (consumedCountZeroCertificate consumedCount hzero) <=
      outputRowsPositiveAtomicFixedPayloadPolynomial bitBound := by
  have htransparent :=
    consumedCountZeroCertificate_structuralPayloadBound_le_transparent
      consumedCount hzero
  exact htransparent.trans
    (outputRowsNativeEqStructuralEnvelope_le_fixed consumedCount
      (‘0’ : ValuationTerm) bitBound hconsumedSize
      (outputRowsModeLiteral_closed _ (Or.inl rfl))
      (outputRowsModeLiteralCode_le _ bitBound (Or.inl rfl)))

theorem outputRowsNativeNeStructuralEnvelope_le_fixed
    (mode : Nat) (literal : ValuationTerm) (bitBound : Nat)
    (hmodeSize : Nat.size mode <= bitBound)
    (hliteralClosed : literal.freeVariables = ∅)
    (hliteralCode :
      (binaryTermCode literal).length <=
        outputRowsAtomicTermCodePolynomial bitBound) :
    outputRowsNativeNeStructuralEnvelope (shortBinaryNumeralTerm mode)
        literal <=
      outputRowsNegativeAtomicFixedPayloadPolynomial bitBound := by
  unfold outputRowsNativeNeStructuralEnvelope
    outputRowsNegativeAtomicFixedPayloadPolynomial
  exact compileNegativeRelationPayloadResource_le_fixed_of_closed
    outputRowsAtomicZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm mode) literal 0
    (outputRowsAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _) hliteralClosed
    (outputRowsShortNumeralCode_le mode bitBound hmodeSize) hliteralCode

theorem modeNativeInequalityCertificate_structuralPayloadBound_le_fixed
    (mode : Nat) (literal : ValuationTerm) (expected bitBound : Nat)
    (hliteralValue :
      termValue outputRowsAtomicZeroValuation literal = expected)
    (hne : mode ≠ expected)
    (hmodeSize : Nat.size mode <= bitBound)
    (hliteralClosed : literal.freeVariables = ∅)
    (hliteralCode :
      (binaryTermCode literal).length <=
        outputRowsAtomicTermCodePolynomial bitBound) :
    hybridFormulaStructuralPayloadBound
        (modeNativeInequalityCertificate mode literal expected
          hliteralValue hne) <=
      outputRowsNegativeAtomicFixedPayloadPolynomial bitBound := by
  have htransparent :=
    modeNativeInequalityCertificate_structuralPayloadBound_le_transparent
      mode literal expected hliteralValue hne
  exact htransparent.trans
    (outputRowsNativeNeStructuralEnvelope_le_fixed mode literal bitBound
      hmodeSize hliteralClosed hliteralCode)

#print axioms outputRowsCountStructuralEnvelope_le_fixed
#print axioms
  consumedCountEqualityCertificate_structuralPayloadBound_le_fixed
#print axioms outputRowsConsumedPositiveStructuralEnvelope_le_fixed
#print axioms
  consumedCountPositiveCertificate_structuralPayloadBound_le_fixed
#print axioms outputRowsNativeEqStructuralEnvelope_le_fixed
#print axioms
  modeNativeEqualityCertificate_structuralPayloadBound_le_fixed
#print axioms
  consumedCountZeroCertificate_structuralPayloadBound_le_fixed
#print axioms outputRowsNativeNeStructuralEnvelope_le_fixed
#print axioms
  modeNativeInequalityCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds
