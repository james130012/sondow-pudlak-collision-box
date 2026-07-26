import integration.FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural bound for natural-list witness rows

This module removes the three witness-row certificate shapes from the public
resource.  The resulting finite envelope depends only on the eight numerical
coordinates of the original predicate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectNatListWitnessRowsPublicBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPABinaryLengthValuationContextCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds

private abbrev rowZeroValuation : Nat -> Nat :=
  compactAdditiveNatListWitnessRowsZeroValuation

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

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem arithmeticMulTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Mul.mul
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Mul.mul left right

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left * !!right’ =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def witnessRowsValuationLeStructuralPayloadPolynomial
    (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables rowZeroValuation
  compilePositiveRelationPayloadPolynomial
      rowZeroValuation Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial
      rowZeroValuation Language.ORing.Rel.lt args +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert equalityFormula Gamma) +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert strictFormula Gamma) +
    FoundationCompactCertifiedContextProof.CertifiedPAContextProof.disjunctionFullAssemblyCost
      Gamma equalityFormula strictFormula

theorem
    compactAdditiveNatListWitnessRowsLeCertificate_structuralPayloadBound_le_public
    (leftTerm rightTerm : ValuationTerm)
    (hleft : leftTerm.freeVariables = ∅)
    (hright : rightTerm.freeVariables = ∅)
    (hle : termValue rowZeroValuation leftTerm <=
      termValue rowZeroValuation rightTerm) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListWitnessRowsLeCertificate
          leftTerm rightTerm hle) <=
      witnessRowsValuationLeStructuralPayloadPolynomial
        leftTerm rightTerm := by
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
      rowZeroValuation Language.Eq.eq args hfirst hsecond
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      rowZeroValuation Language.ORing.Rel.lt args hfirst hsecond
  by_cases heq : termValue rowZeroValuation leftTerm =
      termValue rowZeroValuation rightTerm
  · simp only [compactAdditiveNatListWitnessRowsLeCertificate]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold witnessRowsValuationLeStructuralPayloadPolynomial
    dsimp only [args, rowZeroValuation,
      compactAdditiveNatListWitnessRowsZeroValuation] at hequality hstrict ⊢
    omega
  · simp only [compactAdditiveNatListWitnessRowsLeCertificate]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold witnessRowsValuationLeStructuralPayloadPolynomial
    dsimp only [args, rowZeroValuation,
      compactAdditiveNatListWitnessRowsZeroValuation] at hequality hstrict ⊢
    omega

def compactAdditiveNatListWitnessRowsPublicFinitePayloadEnvelope
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat) : Nat :=
  let layoutFormula :=
    compactAdditiveStructuredListLayoutClosedFormula tokenTable width
      tokenCount start count finish boundaryTable
  let unitFormula :=
    compactAdditiveUnitBoundaryRowsClosedFormula tokenCount count boundaryTable
  let lengthFormula :=
    binaryLengthAtValuationFormula
      (shortBinaryNumeralTerm boundarySize)
      (shortBinaryNumeralTerm boundaryTable)
  let sizeBoundTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm count) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  let boundFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm boundarySize) ≤ !!sizeBoundTerm”
  let layoutResource :=
    compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
      tokenTable width tokenCount start count finish boundaryTable
  let unitResource :=
    compactAdditiveUnitBoundaryRowsPublicFiniteStructuralPayloadEnvelope
      tokenCount count boundaryTable
  let lengthResource :=
    compileBinaryLengthAtValuationPayloadResource rowZeroValuation
      (shortBinaryNumeralTerm boundarySize)
      (shortBinaryNumeralTerm boundaryTable)
  let boundResource :=
    witnessRowsValuationLeStructuralPayloadPolynomial
      (shortBinaryNumeralTerm boundarySize) sizeBoundTerm
  let lengthBoundResource :=
    transparentHybridConjunctionPayloadEnvelope rowZeroValuation
      lengthFormula boundFormula lengthResource boundResource
  let unitTailResource :=
    transparentHybridConjunctionPayloadEnvelope
      FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation
      unitFormula
      (lengthFormula ⋏ boundFormula) unitResource lengthBoundResource
  transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation
    layoutFormula
    (unitFormula ⋏ (lengthFormula ⋏ boundFormula))
    layoutResource unitTailResource

theorem
    compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat)
    (hrows : CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      start count finish boundaryTable boundarySize) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start count finish boundaryTable
          boundarySize hrows) <=
      compactAdditiveNatListWitnessRowsPublicFinitePayloadEnvelope tokenTable
        width tokenCount start count finish boundaryTable boundarySize := by
  rcases hrows with ⟨hlayout, hunit, hsizeEq, hsizeBound⟩
  let layoutCertificate :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount start count finish boundaryTable hlayout
  let unitCertificate :=
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount count boundaryTable hunit
  let lengthCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.binaryLength
      rowZeroValuation (shortBinaryNumeralTerm boundarySize)
      (shortBinaryNumeralTerm boundaryTable) (by
        simpa [termValue_shortBinaryNumeralTerm] using hsizeEq)
  let sizeBoundTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm count) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  let boundCertificate :=
    compactAdditiveNatListWitnessRowsLeCertificate
      (shortBinaryNumeralTerm boundarySize) sizeBoundTerm (by
        simpa [sizeBoundTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticMul,
          termValue_arithmeticOne] using hsizeBound)
  let layoutFormula :=
    compactAdditiveStructuredListLayoutClosedFormula tokenTable width
      tokenCount start count finish boundaryTable
  let unitFormula :=
    compactAdditiveUnitBoundaryRowsClosedFormula tokenCount count boundaryTable
  let lengthFormula :=
    binaryLengthAtValuationFormula
      (shortBinaryNumeralTerm boundarySize)
      (shortBinaryNumeralTerm boundaryTable)
  let boundFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm boundarySize) ≤ !!sizeBoundTerm”
  let layoutResource :=
    compactAdditiveStructuredListLayoutPublicFiniteStructuralPayloadEnvelope
      tokenTable width tokenCount start count finish boundaryTable
  let unitResource :=
    compactAdditiveUnitBoundaryRowsPublicFiniteStructuralPayloadEnvelope
      tokenCount count boundaryTable
  let lengthResource :=
    compileBinaryLengthAtValuationPayloadResource rowZeroValuation
      (shortBinaryNumeralTerm boundarySize)
      (shortBinaryNumeralTerm boundaryTable)
  let boundResource :=
    witnessRowsValuationLeStructuralPayloadPolynomial
      (shortBinaryNumeralTerm boundarySize) sizeBoundTerm
  have hlayoutResource :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount start count finish boundaryTable hlayout
  have hunitResource :=
    (compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount count boundaryTable hunit).trans
      (compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope_le_publicFinite
        tokenCount count boundaryTable hunit)
  have hlengthResource :
      hybridFormulaStructuralPayloadBound lengthCertificate <=
        lengthResource := by
    simp [lengthCertificate, lengthResource,
      hybridFormulaStructuralPayloadBound]
  have hsizeBoundTermClosed : sizeBoundTerm.freeVariables = ∅ := by
    rw [show sizeBoundTerm =
      ‘(!!(shortBinaryNumeralTerm count) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)’ by rfl]
    rw [arithmeticMulTerm_freeVariables,
      arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hboundResource :=
    compactAdditiveNatListWitnessRowsLeCertificate_structuralPayloadBound_le_public
      (shortBinaryNumeralTerm boundarySize) sizeBoundTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty boundarySize)
      hsizeBoundTermClosed (by
        simpa [sizeBoundTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticMul,
          termValue_arithmeticOne] using hsizeBound)
  let lengthBoundCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      lengthCertificate boundCertificate
  have hlengthBound :=
    transparentHybridConjunctionPayloadBound_le
      lengthCertificate boundCertificate lengthResource boundResource
      hlengthResource hboundResource
  let unitTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      unitCertificate lengthBoundCertificate
  let lengthBoundResource :=
    transparentHybridConjunctionPayloadEnvelope rowZeroValuation
      lengthFormula boundFormula lengthResource boundResource
  have hunitTail :=
    transparentHybridConjunctionPayloadBound_le
      unitCertificate lengthBoundCertificate unitResource lengthBoundResource
      hunitResource (by exact hlengthBound)
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      layoutCertificate unitTailCertificate
  let unitTailResource :=
    transparentHybridConjunctionPayloadEnvelope
      FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation
      unitFormula
      (lengthFormula ⋏ boundFormula) unitResource lengthBoundResource
  have hdirect :=
    transparentHybridConjunctionPayloadBound_le
      layoutCertificate unitTailCertificate layoutResource unitTailResource
      hlayoutResource (by exact hunitTail)
  unfold
    compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  change hybridFormulaStructuralPayloadBound direct <= _
  simpa only [
    compactAdditiveNatListWitnessRowsPublicFinitePayloadEnvelope,
    layoutFormula, unitFormula, lengthFormula, boundFormula, sizeBoundTerm,
    layoutResource, unitResource, lengthResource, boundResource,
    lengthBoundResource, unitTailResource] using hdirect

#print axioms
  compactAdditiveNatListWitnessRowsLeCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectNatListWitnessRowsPublicBounds
