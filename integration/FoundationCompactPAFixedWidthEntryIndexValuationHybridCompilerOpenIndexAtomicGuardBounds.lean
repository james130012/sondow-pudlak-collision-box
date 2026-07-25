import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPABinaryLengthValuationContextCompilerFixedPolynomialBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-!
# Fixed bounds for the open-index top atomic guards

This layer closes the witness guard and size guard after the fixed-width entry
core.  The extra scalar records only the four canonical input-term code
lengths.  Resource equalities are explicit so the kernel can check the large
transparent definitions without unfolding them while elaborating theorem
statements.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPABinaryLengthValuationContextCompilerPublicBounds
open FoundationCompactPABinaryLengthValuationContextCompilerFixedPolynomialBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-- Public scalar for the top guards.  It augments the already closed
open-index scalar only with canonical input syntax sizes. -/
def fixedWidthOpenIndexAtomicCoordinateScale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) : Nat :=
  fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm widthTerm
      indexTerm valueTerm +
    (binaryTermCode tableTerm).length +
    (binaryTermCode widthTerm).length +
    (binaryTermCode indexTerm).length +
    (binaryTermCode valueTerm).length

theorem fixedWidthOpenIndexPublicCoordinateScale_le_atomicCoordinateScale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm) :
    fixedWidthOpenIndexPublicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm <=
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm := by
  unfold fixedWidthOpenIndexAtomicCoordinateScale
  omega

private theorem paAddTerm_freeVariables_openIndexAtomic
    (left right : ValuationTerm) :
    (paAddTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
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

private theorem binaryRelationFormula_freeVariables_openIndexAtomic
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) :
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

private theorem binaryFormulaCode_disjunction_length_le_openIndexAtomic
    (left right : ValuationFormula) :
    (binaryFormulaCode (left ⋎ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + (binaryNatCode 5).length := by
  simp [binaryFormulaCode]
  omega

def fixedWidthOpenIndexTopAtomicTermCodePolynomial (scale : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope scale + scale +
    (binaryTermCode paOneTerm).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 1

def fixedWidthWitnessGuardArgs
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    Fin 2 -> ValuationTerm :=
  ![shortBinaryNumeralTerm (Nat.size (termValue valuation valueTerm)),
    (‘!!valueTerm + 1’ : ValuationTerm)]

private theorem fixedWidthWitnessGuardSize_le_scale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale) :
    Nat.size (termValue valuation valueTerm) <= scale := by
  have hraw : Nat.size (termValue valuation valueTerm) <=
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm := by
    unfold fixedWidthOpenIndexAtomicCoordinateScale
      fixedWidthOpenIndexPublicCoordinateScale
    omega
  exact hraw.trans hscale

private theorem fixedWidthWitnessGuardSizeTermCode_le
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale termBound : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htermBound :
      fixedWidthOpenIndexTopAtomicTermCodePolynomial scale <= termBound) :
    (binaryTermCode (fixedWidthWitnessGuardArgs valuation valueTerm 0)).length <=
      termBound := by
  let size := Nat.size (termValue valuation valueTerm)
  have hsize := fixedWidthWitnessGuardSize_le_scale valuation tableTerm
    widthTerm indexTerm valueTerm scale hscale
  have hsizeWidth : Nat.size size <= scale :=
    (natSize_le_self_uniform size).trans hsize
  have hsizeCodeRaw := binaryNumeralTerm_code_length_le_envelope size scale
    hsizeWidth
  have htop : binaryNumeralTermCodeEnvelope scale <=
      fixedWidthOpenIndexTopAtomicTermCodePolynomial scale := by
    unfold fixedWidthOpenIndexTopAtomicTermCodePolynomial
    omega
  change (binaryTermCode (shortBinaryNumeralTerm size)).length <= termBound
  exact (hsizeCodeRaw.trans htop).trans htermBound

private theorem fixedWidthWitnessGuardSuccessorTermCode_le
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale termBound : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htermBound :
      fixedWidthOpenIndexTopAtomicTermCodePolynomial scale <= termBound) :
    (binaryTermCode (fixedWidthWitnessGuardArgs valuation valueTerm 1)).length <=
      termBound := by
  have hvalueCode : (binaryTermCode valueTerm).length <= scale := by
    have hraw : (binaryTermCode valueTerm).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
      omega
    exact hraw.trans hscale
  have hsuccessorRaw := paAddTerm_code_length_le valueTerm paOneTerm
  have htop : (binaryTermCode valueTerm).length +
        (binaryTermCode paOneTerm).length +
        binaryFunctionTermCodeOverhead Language.Add.add <=
      fixedWidthOpenIndexTopAtomicTermCodePolynomial scale := by
    unfold fixedWidthOpenIndexTopAtomicTermCodePolynomial
    omega
  change (binaryTermCode (paAddTerm valueTerm paOneTerm)).length <= termBound
  exact (hsuccessorRaw.trans htop).trans htermBound

private theorem fixedWidthWitnessGuardFirstFreeVariables
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    (fixedWidthWitnessGuardArgs valuation valueTerm 0).freeVariables ⊆ {0} := by
  change
    (shortBinaryNumeralTerm
      (Nat.size (termValue valuation valueTerm))).freeVariables ⊆ {0}
  rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
  simp

private theorem fixedWidthWitnessGuardSecondFreeVariables
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm)
    (hvalue : valueTerm.freeVariables = ∅) :
    (fixedWidthWitnessGuardArgs valuation valueTerm 1).freeVariables ⊆ {0} := by
  change (paAddTerm valueTerm paOneTerm).freeVariables ⊆ {0}
  rw [paAddTerm_freeVariables_openIndexAtomic, hvalue]
  have hone : paOneTerm.freeVariables = ∅ := by
    change (shortBinaryNumeralTerm 1).freeVariables = ∅
    exact shortBinaryNumeralTerm_freeVariables_eq_empty 1
  rw [hone]
  simp

private theorem fixedWidthWitnessGuardZero_le_scale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale) :
    valuation 0 <= scale := by
  have hraw : valuation 0 <=
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm := by
    unfold fixedWidthOpenIndexAtomicCoordinateScale
      fixedWidthOpenIndexPublicCoordinateScale
    omega
  exact hraw.trans hscale

theorem fixedWidthWitnessGuardStructuralPayload_eq_compiled
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    fixedWidthWitnessGuardStructuralPayloadPolynomial valuation valueTerm =
      compilePositiveRelationPayloadPolynomial valuation Language.ORing.Rel.lt
        (fixedWidthWitnessGuardArgs valuation valueTerm) := by
  unfold fixedWidthWitnessGuardStructuralPayloadPolynomial
    fixedWidthWitnessGuardArgs
  rfl

private theorem fixedWidthWitnessGuardCompiledResource_le_fixed_of_eq
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (resource target scale termBound : Nat)
    (hresource :
      resource = compilePositiveRelationPayloadPolynomial valuation
        Language.ORing.Rel.lt
          (fixedWidthWitnessGuardArgs valuation valueTerm))
    (htarget :
      target = compilePositiveRelationFixedPayloadPolynomial scale termBound)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htermBound :
      fixedWidthOpenIndexTopAtomicTermCodePolynomial scale <= termBound)
    (hvalue : valueTerm.freeVariables = ∅) :
    Nat.le resource target := by
  have hrelation := compilePositiveRelationPayloadPolynomial_le_fixed
    valuation Language.ORing.Rel.lt
      (fixedWidthWitnessGuardArgs valuation valueTerm) scale termBound
      (fixedWidthWitnessGuardFirstFreeVariables valuation valueTerm)
      (fixedWidthWitnessGuardSecondFreeVariables valuation valueTerm hvalue)
      (fixedWidthWitnessGuardZero_le_scale valuation tableTerm widthTerm
        indexTerm valueTerm scale hscale)
      (fixedWidthWitnessGuardSizeTermCode_le valuation tableTerm widthTerm
        indexTerm valueTerm scale termBound hscale htermBound)
      (fixedWidthWitnessGuardSuccessorTermCode_le valuation tableTerm widthTerm
        indexTerm valueTerm scale termBound hscale htermBound)
  rw [hresource, htarget]
  exact hrelation

/-- A resource-explicit witness-guard endpoint.  `hresource` and `htarget` are
transparent definition equations, not mathematical hypotheses. -/
theorem fixedWidthWitnessGuardResource_le_fixed_of_eq
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (resource target scale termBound : Nat)
    (hresource :
      resource =
        fixedWidthWitnessGuardStructuralPayloadPolynomial valuation valueTerm)
    (htarget :
      target = compilePositiveRelationFixedPayloadPolynomial scale termBound)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htermBound :
      fixedWidthOpenIndexTopAtomicTermCodePolynomial scale <= termBound)
    (hvalue : valueTerm.freeVariables = ∅) :
    Nat.le resource target := by
  apply fixedWidthWitnessGuardCompiledResource_le_fixed_of_eq valuation
    tableTerm widthTerm indexTerm valueTerm resource target scale termBound
  · exact hresource.trans
      (fixedWidthWitnessGuardStructuralPayload_eq_compiled valuation valueTerm)
  · exact htarget
  · exact hscale
  · exact htermBound
  · exact hvalue

theorem fixedWidthLengthStructuralPayload_eq_compiled
    (valuation : Nat -> Nat) (valueTerm : ValuationTerm) :
    fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm =
      compileBinaryLengthAtValuationPayloadPolynomial valuation
        (shortBinaryNumeralTerm
          (Nat.size (termValue valuation valueTerm))) valueTerm := by
  unfold fixedWidthLengthStructuralPayloadPolynomial
  rfl

/-- Fixed bound for the binary-length graph in a complete fixed-width entry. -/
theorem fixedWidthLengthResource_le_fixed_of_eq
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (resource target scale termBound : Nat)
    (hresource :
      resource = fixedWidthLengthStructuralPayloadPolynomial valuation
        valueTerm)
    (htarget :
      target = compileBinaryLengthAtValuationFixedPayloadPolynomial scale
        termBound)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htermBound :
      fixedWidthOpenIndexTopAtomicTermCodePolynomial scale <= termBound)
    (hvalue : valueTerm.freeVariables = ∅) :
    Nat.le resource target := by
  let size := Nat.size (termValue valuation valueTerm)
  let sizeTerm : ValuationTerm := shortBinaryNumeralTerm size
  have hsize := fixedWidthWitnessGuardSize_le_scale valuation tableTerm
    widthTerm indexTerm valueTerm scale hscale
  have hsizeClosed : sizeTerm.freeVariables = ∅ := by
    dsimp only [sizeTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty size
  have hsizeValueWidth : Nat.size (termValue valuation sizeTerm) <= scale := by
    rw [show termValue valuation sizeTerm = size by
      dsimp only [sizeTerm]
      exact termValue_shortBinaryNumeralTerm valuation size]
    exact (natSize_le_self_uniform size).trans hsize
  have hvalueWidth : Nat.size (termValue valuation valueTerm) <= scale := hsize
  have hsizeCode := fixedWidthWitnessGuardSizeTermCode_le valuation tableTerm
    widthTerm indexTerm valueTerm scale termBound hscale htermBound
  have hvalueCodeRaw : (binaryTermCode valueTerm).length <= scale := by
    have hcoordinate : (binaryTermCode valueTerm).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
      omega
    exact hcoordinate.trans hscale
  have hvalueCode : (binaryTermCode valueTerm).length <= termBound := by
    have htop : scale <= fixedWidthOpenIndexTopAtomicTermCodePolynomial scale := by
      unfold fixedWidthOpenIndexTopAtomicTermCodePolynomial
      omega
    exact (hvalueCodeRaw.trans htop).trans htermBound
  apply
    compileBinaryLengthAtValuationPayloadPolynomial_le_fixed_of_eq valuation
      sizeTerm valueTerm resource target scale termBound
  · exact hresource.trans
      (fixedWidthLengthStructuralPayload_eq_compiled valuation valueTerm)
  · exact htarget
  · exact hsizeClosed
  · exact hvalue
  · exact hsizeValueWidth
  · exact hvalueWidth
  · exact hsizeCode
  · exact hvalueCode

/-- Fixed endpoint for the shifted width equality used by the bounded
universal compiler.  `houterVariables` identifies the transparent outer
formula variable set; it adds no mathematical assumption. -/
theorem fixedWidthShiftedBoundResource_le_fixed_of_eq
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (outerVariables : Finset Nat) (resource target scale : Nat)
    (hresource : resource =
      compileShiftedBoundEqualityPayloadPublicPolynomial valuation
        outerVariables widthTerm)
    (htarget : target =
      compileShiftedBoundEqualityFixedPayloadPolynomial scale)
    (houterVariables : outerVariables =
      (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm)
        (fixedWidthBitBody tableTerm widthTerm indexTerm
          valueTerm)).freeVariables)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    Nat.le resource target := by
  have houter : outerVariables ⊆ {0} := by
    rw [houterVariables]
    exact
      fixedWidthUniversalOuterFormula_freeVariables_subset_singleton_of_openIndex
        tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hzero : valuation 0 <= scale := by
    have hraw : valuation 0 <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
        fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hscale
  have hwidthValue : termValue valuation widthTerm <= scale := by
    have hraw : termValue valuation widthTerm <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
        fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hscale
  have hwidthCode : (binaryTermCode widthTerm).length <= scale := by
    have hraw : (binaryTermCode widthTerm).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
      omega
    exact hraw.trans hscale
  exact
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
      valuation outerVariables widthTerm resource target scale hresource htarget
      hwidth houter hzero hwidthValue hwidthCode

def fixedWidthSizeGuardArgs
    (valuation : Nat -> Nat) (widthTerm valueTerm : ValuationTerm) :
    Fin 2 -> ValuationTerm :=
  ![shortBinaryNumeralTerm (Nat.size (termValue valuation valueTerm)),
    widthTerm]

def fixedWidthOpenIndexTopAtomicFormulaCodePolynomial
    (scale termBound : Nat) : Nat :=
  arbitraryContextRelationFormulaEnvelope
    (valuationAtomicContextCodePolynomial scale termBound) termBound

def fixedWidthOpenIndexSizeGuardFixedPayloadPolynomial
    (scale termBound : Nat) : Nat :=
  let formulaBound :=
    fixedWidthOpenIndexTopAtomicFormulaCodePolynomial scale termBound
  2 * compilePositiveRelationFixedPayloadPolynomial scale termBound +
    3 * smallContextAssemblyEnvelope formulaBound + 1

private theorem fixedWidthSizeGuardWidthTermCode_le
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale termBound : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htermBound :
      fixedWidthOpenIndexTopAtomicTermCodePolynomial scale <= termBound) :
    (binaryTermCode
      (fixedWidthSizeGuardArgs valuation widthTerm valueTerm 1)).length <=
        termBound := by
  have hraw : (binaryTermCode widthTerm).length <= scale := by
    have hcoordinate : (binaryTermCode widthTerm).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
      omega
    exact hcoordinate.trans hscale
  have htop : scale <=
      fixedWidthOpenIndexTopAtomicTermCodePolynomial scale := by
    unfold fixedWidthOpenIndexTopAtomicTermCodePolynomial
    omega
  change (binaryTermCode widthTerm).length <= termBound
  exact (hraw.trans htop).trans htermBound

private theorem fixedWidthSizeGuardFirstFreeVariables
    (valuation : Nat -> Nat) (widthTerm valueTerm : ValuationTerm) :
    (fixedWidthSizeGuardArgs valuation widthTerm valueTerm 0).freeVariables ⊆
      {0} := by
  change
    (shortBinaryNumeralTerm
      (Nat.size (termValue valuation valueTerm))).freeVariables ⊆ {0}
  rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
  simp

private theorem fixedWidthSizeGuardSecondFreeVariables
    (valuation : Nat -> Nat) (widthTerm valueTerm : ValuationTerm)
    (hwidth : widthTerm.freeVariables = ∅) :
    (fixedWidthSizeGuardArgs valuation widthTerm valueTerm 1).freeVariables ⊆
      {0} := by
  change widthTerm.freeVariables ⊆ {0}
  rw [hwidth]
  simp

/-- Fixed bound for the complete size guard.  The two equalities expose only
transparent resource definitions, so callers discharge them with `rfl`. -/
theorem fixedWidthSizeGuardResource_le_fixed_of_eq
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (resource target scale termBound : Nat)
    (hresource :
      resource = fixedWidthSizeGuardStructuralPayloadPolynomial valuation
        widthTerm valueTerm)
    (htarget :
      target = fixedWidthOpenIndexSizeGuardFixedPayloadPolynomial scale
        termBound)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htermBound :
      fixedWidthOpenIndexTopAtomicTermCodePolynomial scale <= termBound)
    (hwidth : widthTerm.freeVariables = ∅) :
    Nat.le resource target := by
  let args := fixedWidthSizeGuardArgs valuation widthTerm valueTerm
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables valuation
  let formulaBound :=
    fixedWidthOpenIndexTopAtomicFormulaCodePolynomial scale termBound
  have hfirstVars : (args 0).freeVariables ⊆ {0} := by
    exact fixedWidthSizeGuardFirstFreeVariables valuation widthTerm valueTerm
  have hsecondVars : (args 1).freeVariables ⊆ {0} := by
    exact fixedWidthSizeGuardSecondFreeVariables valuation widthTerm valueTerm
      hwidth
  have hfirstCode : (binaryTermCode (args 0)).length <= termBound := by
    exact fixedWidthWitnessGuardSizeTermCode_le valuation tableTerm widthTerm
      indexTerm valueTerm scale termBound hscale htermBound
  have hsecondCode : (binaryTermCode (args 1)).length <= termBound := by
    exact fixedWidthSizeGuardWidthTermCode_le valuation tableTerm widthTerm
      indexTerm valueTerm scale termBound hscale htermBound
  have hzero := fixedWidthWitnessGuardZero_le_scale valuation tableTerm
    widthTerm indexTerm valueTerm scale hscale
  have hequality := compilePositiveRelationPayloadPolynomial_le_fixed
    valuation Language.Eq.eq args scale termBound hfirstVars hsecondVars hzero
      hfirstCode hsecondCode
  have hstrict := compilePositiveRelationPayloadPolynomial_le_fixed
    valuation Language.ORing.Rel.lt args scale termBound hfirstVars hsecondVars
      hzero hfirstCode hsecondCode
  have hequalityCodeRaw := equalityFormula_code_le_orderAtomic (args 0)
    (args 1) termBound hfirstCode hsecondCode
  have hstrictCodeRaw := lessThanFormula_code_le_orderAtomic (args 0)
    (args 1) termBound hfirstCode hsecondCode
  have hatomicPrimitive :=
    (orderAtomic_le_derived termBound).trans
      ((orderDerived_le_local termBound).trans
        (orderLocal_le_primitive termBound))
  have hequalityCode : (binaryFormulaCode equalityFormula).length <=
      formulaBound := by
    exact (hequalityCodeRaw.trans hatomicPrimitive).trans (by
      unfold formulaBound fixedWidthOpenIndexTopAtomicFormulaCodePolynomial
        arbitraryContextRelationFormulaEnvelope
      omega)
  have hstrictCode : (binaryFormulaCode strictFormula).length <=
      formulaBound := by
    exact (hstrictCodeRaw.trans hatomicPrimitive).trans (by
      unfold formulaBound fixedWidthOpenIndexTopAtomicFormulaCodePolynomial
        arbitraryContextRelationFormulaEnvelope
      omega)
  have htagFive : (binaryNatCode 5).length <= 8 := by decide
  have htargetRaw := binaryFormulaCode_disjunction_length_le_openIndexAtomic
    equalityFormula strictFormula
  have htargetCode : (binaryFormulaCode targetFormula).length <=
      formulaBound := by
    have hequalityTight : (binaryFormulaCode equalityFormula).length <=
        orderPrimitiveFormulaCodeEnvelope termBound := by
      dsimp only [equalityFormula]
      exact hequalityCodeRaw.trans hatomicPrimitive
    have hstrictTight : (binaryFormulaCode strictFormula).length <=
        orderPrimitiveFormulaCodeEnvelope termBound := by
      dsimp only [strictFormula]
      exact hstrictCodeRaw.trans hatomicPrimitive
    have htargetTight : (binaryFormulaCode targetFormula).length <=
        2 * orderPrimitiveFormulaCodeEnvelope termBound + 8 := by
      dsimp only [targetFormula] at htargetRaw ⊢
      omega
    unfold formulaBound fixedWidthOpenIndexTopAtomicFormulaCodePolynomial
      arbitraryContextRelationFormulaEnvelope
    omega
  have hsizeClosed : (args 0).freeVariables = ∅ := by
    change
      (shortBinaryNumeralTerm
        (Nat.size (termValue valuation valueTerm))).freeVariables = ∅
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hequalityClosed : equalityFormula.freeVariables = ∅ := by
    dsimp only [equalityFormula, args, fixedWidthSizeGuardArgs]
    rw [binaryRelationFormula_freeVariables_openIndexAtomic,
      shortBinaryNumeralTerm_freeVariables_eq_empty, hwidth]
    simp
  have hstrictClosed : strictFormula.freeVariables = ∅ := by
    dsimp only [strictFormula, args, fixedWidthSizeGuardArgs]
    rw [binaryRelationFormula_freeVariables_openIndexAtomic,
      shortBinaryNumeralTerm_freeVariables_eq_empty, hwidth]
    simp
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    dsimp only [targetFormula]
    simp [hequalityClosed, hstrictClosed]
  have hGammaEmpty : Gamma = ∅ := by
    dsimp only [Gamma]
    rw [htargetClosed]
    simp [valuationContext]
  have hcontext : FormulaCodeBound Gamma formulaBound := by
    rw [hGammaEmpty]
    intro formula hformula
    simp at hformula
  have hcontextCard : Gamma.card <= 4 := by
    rw [hGammaEmpty]
    simp
  have hequalityInsert := hcontext.insert hequalityCode
  have hstrictInsert := hcontext.insert hstrictCode
  have hequalityInsertCard : (insert equalityFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le equalityFormula Gamma
    omega
  have hstrictInsertCard : (insert strictFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le strictFormula Gamma
    omega
  have hweakEquality := weakeningFullAssemblyCost_le_small
    (insert equalityFormula Gamma) formulaBound hequalityInsertCard
      hequalityInsert
  have hweakStrict := weakeningFullAssemblyCost_le_small
    (insert strictFormula Gamma) formulaBound hstrictInsertCard hstrictInsert
  have hdisjunction := disjunctionFullAssemblyCost_le_small Gamma
    equalityFormula strictFormula formulaBound hcontextCard hcontext
      hequalityCode hstrictCode htargetCode
  rw [hresource, htarget]
  change
    compilePositiveRelationPayloadPolynomial valuation Language.Eq.eq args +
        compilePositiveRelationPayloadPolynomial valuation
          Language.ORing.Rel.lt args +
        weakeningFullAssemblyCost (insert equalityFormula Gamma) +
        weakeningFullAssemblyCost (insert strictFormula Gamma) +
        disjunctionFullAssemblyCost Gamma equalityFormula strictFormula <=
      2 * compilePositiveRelationFixedPayloadPolynomial scale termBound +
        3 * smallContextAssemblyEnvelope formulaBound + 1
  omega

#print axioms fixedWidthOpenIndexPublicCoordinateScale_le_atomicCoordinateScale
#print axioms fixedWidthWitnessGuardResource_le_fixed_of_eq
#print axioms fixedWidthLengthResource_le_fixed_of_eq
#print axioms fixedWidthShiftedBoundResource_le_fixed_of_eq
#print axioms fixedWidthSizeGuardResource_le_fixed_of_eq

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
