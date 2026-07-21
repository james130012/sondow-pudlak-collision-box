import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resources for arithmetic function-code validity

The four accepted `(arity, code)` pairs and the four rejected pairs are
charged by proof-free atomic and connective envelopes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactArithmeticSymbolCode
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate

private abbrev funcCodeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate.zeroValuation

private theorem funcCodeFixedNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (funcCodeFixedNumeralTerm value).freeVariables = ∅ := by
  simp [funcCodeFixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

def funcCodeFixedEqPayloadPolynomial (value expected : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial funcCodeZeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm value, funcCodeFixedNumeralTerm expected]

theorem funcCodeFixedEqCertificate_structuralPayloadBound_le_public
    (value expected : Nat) (heq : value = expected) :
    hybridFormulaStructuralPayloadBound
        (funcCodeFixedEqCertificate value expected heq) ≤
      funcCodeFixedEqPayloadPolynomial value expected := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (funcCodeFixedNumeralTerm expected).freeVariables ⊆ {0} := by
    rw [funcCodeFixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    funcCodeZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, funcCodeFixedNumeralTerm expected]
    hleft hright
  change compilePositiveRelationPayloadResource funcCodeZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, funcCodeFixedNumeralTerm expected] ≤ _
  exact hpublic

def funcCodeFixedNePayloadPolynomial (value expected : Nat) : Nat :=
  compileNegativeRelationPayloadPolynomial funcCodeZeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm value, funcCodeFixedNumeralTerm expected]

theorem funcCodeFixedNeCertificate_structuralPayloadBound_le_public
    (value expected : Nat) (hne : value ≠ expected) :
    hybridFormulaStructuralPayloadBound
        (funcCodeFixedNeCertificate value expected hne) ≤
      funcCodeFixedNePayloadPolynomial value expected := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (funcCodeFixedNumeralTerm expected).freeVariables ⊆ {0} := by
    rw [funcCodeFixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compileNegativeRelationPayloadResource_le_publicPolynomial
    funcCodeZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, funcCodeFixedNumeralTerm expected]
    hleft hright
  change compileNegativeRelationPayloadResource funcCodeZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, funcCodeFixedNumeralTerm expected] ≤ _
  exact hpublic

def funcCodeValidPairPayloadEnvelope
    (left leftExpected right rightExpected : Nat) : Nat :=
  transparentHybridConjunctionPayloadEnvelope funcCodeZeroValuation
    (funcCodeFixedEqFormula left leftExpected)
    (funcCodeFixedEqFormula right rightExpected)
    (funcCodeFixedEqPayloadPolynomial left leftExpected)
    (funcCodeFixedEqPayloadPolynomial right rightExpected)

theorem funcCodeValidPairCertificate_structuralPayloadBound_le_public
    (left leftExpected right rightExpected : Nat)
    (hleft : left = leftExpected) (hright : right = rightExpected) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (funcCodeFixedEqCertificate left leftExpected hleft)
          (funcCodeFixedEqCertificate right rightExpected hright)) ≤
      funcCodeValidPairPayloadEnvelope left leftExpected right
        rightExpected := by
  exact transparentHybridConjunctionPayloadBound_le
    (funcCodeFixedEqCertificate left leftExpected hleft)
    (funcCodeFixedEqCertificate right rightExpected hright) _ _
    (funcCodeFixedEqCertificate_structuralPayloadBound_le_public
      left leftExpected hleft)
    (funcCodeFixedEqCertificate_structuralPayloadBound_le_public
      right rightExpected hright)

def funcCodeValidCase00PayloadEnvelope (arity code : Nat) : Nat :=
  let branch00 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 0
  let branch01 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 1
  let branch20 := funcCodeFixedEqFormula arity 2 ⋏
    funcCodeFixedEqFormula code 0
  let branch21 := funcCodeFixedEqFormula arity 2 ⋏
    funcCodeFixedEqFormula code 1
  transparentHybridDisjunctionLeftPayloadEnvelope funcCodeZeroValuation
    branch00 (branch01 ⋎ branch20 ⋎ branch21)
    (funcCodeValidPairPayloadEnvelope arity 0 code 0)

def funcCodeValidCase01PayloadEnvelope (arity code : Nat) : Nat :=
  let branch00 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 0
  let branch01 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 1
  let branch20 := funcCodeFixedEqFormula arity 2 ⋏
    funcCodeFixedEqFormula code 0
  let branch21 := funcCodeFixedEqFormula arity 2 ⋏
    funcCodeFixedEqFormula code 1
  let inner := transparentHybridDisjunctionLeftPayloadEnvelope
    funcCodeZeroValuation branch01 (branch20 ⋎ branch21)
    (funcCodeValidPairPayloadEnvelope arity 0 code 1)
  transparentHybridDisjunctionRightPayloadEnvelope funcCodeZeroValuation
    branch00 (branch01 ⋎ branch20 ⋎ branch21) inner

def funcCodeValidCase20PayloadEnvelope (arity code : Nat) : Nat :=
  let branch00 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 0
  let branch01 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 1
  let branch20 := funcCodeFixedEqFormula arity 2 ⋏
    funcCodeFixedEqFormula code 0
  let branch21 := funcCodeFixedEqFormula arity 2 ⋏
    funcCodeFixedEqFormula code 1
  let inner20 := transparentHybridDisjunctionLeftPayloadEnvelope
    funcCodeZeroValuation branch20 branch21
    (funcCodeValidPairPayloadEnvelope arity 2 code 0)
  let inner01 := transparentHybridDisjunctionRightPayloadEnvelope
    funcCodeZeroValuation branch01 (branch20 ⋎ branch21) inner20
  transparentHybridDisjunctionRightPayloadEnvelope funcCodeZeroValuation
    branch00 (branch01 ⋎ branch20 ⋎ branch21) inner01

def funcCodeValidCase21PayloadEnvelope (arity code : Nat) : Nat :=
  let branch00 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 0
  let branch01 := funcCodeFixedEqFormula arity 0 ⋏
    funcCodeFixedEqFormula code 1
  let branch20 := funcCodeFixedEqFormula arity 2 ⋏
    funcCodeFixedEqFormula code 0
  let branch21 := funcCodeFixedEqFormula arity 2 ⋏
    funcCodeFixedEqFormula code 1
  let inner21 := transparentHybridDisjunctionRightPayloadEnvelope
    funcCodeZeroValuation branch20 branch21
    (funcCodeValidPairPayloadEnvelope arity 2 code 1)
  let inner01 := transparentHybridDisjunctionRightPayloadEnvelope
    funcCodeZeroValuation branch01 (branch20 ⋎ branch21) inner21
  transparentHybridDisjunctionRightPayloadEnvelope funcCodeZeroValuation
    branch00 (branch01 ⋎ branch20 ⋎ branch21) inner01

theorem funcCodeValidCase00Certificate_structuralPayloadBound_le_public
    (arity code : Nat) (hpair : arity = 0 ∧ code = 0) :
    hybridFormulaStructuralPayloadBound
        (funcCodeValidCase00Certificate arity code hpair) ≤
      funcCodeValidCase00PayloadEnvelope arity code := by
  let pair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeFixedEqCertificate arity 0 hpair.1)
    (funcCodeFixedEqCertificate code 0 hpair.2)
  have hpairResource :=
    funcCodeValidPairCertificate_structuralPayloadBound_le_public
      arity 0 code 0 hpair.1 hpair.2
  have houter := transparentHybridDisjunctionLeftPayloadBound_le
    (right :=
      (funcCodeFixedEqFormula arity 0 ⋏ funcCodeFixedEqFormula code 1) ⋎
      (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 0) ⋎
      (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 1))
    pair _ hpairResource
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right :=
          (funcCodeFixedEqFormula arity 0 ⋏ funcCodeFixedEqFormula code 1) ⋎
          (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 0) ⋎
          (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 1))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (funcCodeFixedEqCertificate arity 0 hpair.1)
          (funcCodeFixedEqCertificate code 0 hpair.2))) ≤ _
  unfold funcCodeValidCase00PayloadEnvelope
  simpa only [pair] using houter

theorem funcCodeValidCase01Certificate_structuralPayloadBound_le_public
    (arity code : Nat) (hpair : arity = 0 ∧ code = 1) :
    hybridFormulaStructuralPayloadBound
        (funcCodeValidCase01Certificate arity code hpair) ≤
      funcCodeValidCase01PayloadEnvelope arity code := by
  let pair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeFixedEqCertificate arity 0 hpair.1)
    (funcCodeFixedEqCertificate code 1 hpair.2)
  have hpairResource :=
    funcCodeValidPairCertificate_structuralPayloadBound_le_public
      arity 0 code 1 hpair.1 hpair.2
  let inner := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right :=
      (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 0) ⋎
      (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 1)) pair
  have hinner := transparentHybridDisjunctionLeftPayloadBound_le
    (right :=
      (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 0) ⋎
      (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 1))
    pair _ hpairResource
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := funcCodeFixedEqFormula arity 0 ⋏
      funcCodeFixedEqFormula code 0)
    inner _ hinner
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := funcCodeFixedEqFormula arity 0 ⋏
          funcCodeFixedEqFormula code 0)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 0) ⋎
            (funcCodeFixedEqFormula arity 2 ⋏ funcCodeFixedEqFormula code 1))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (funcCodeFixedEqCertificate arity 0 hpair.1)
            (funcCodeFixedEqCertificate code 1 hpair.2)))) ≤ _
  unfold funcCodeValidCase01PayloadEnvelope
  simpa only [pair, inner] using houter

theorem funcCodeValidCase20Certificate_structuralPayloadBound_le_public
    (arity code : Nat) (hpair : arity = 2 ∧ code = 0) :
    hybridFormulaStructuralPayloadBound
        (funcCodeValidCase20Certificate arity code hpair) ≤
      funcCodeValidCase20PayloadEnvelope arity code := by
  let pair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeFixedEqCertificate arity 2 hpair.1)
    (funcCodeFixedEqCertificate code 0 hpair.2)
  have hpairResource :=
    funcCodeValidPairCertificate_structuralPayloadBound_le_public
      arity 2 code 0 hpair.1 hpair.2
  let inner20 := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := funcCodeFixedEqFormula arity 2 ⋏
      funcCodeFixedEqFormula code 1) pair
  have hinner20 := transparentHybridDisjunctionLeftPayloadBound_le
    (right := funcCodeFixedEqFormula arity 2 ⋏
      funcCodeFixedEqFormula code 1)
    pair _ hpairResource
  let inner01 := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := funcCodeFixedEqFormula arity 0 ⋏
      funcCodeFixedEqFormula code 1) inner20
  have hinner01 := transparentHybridDisjunctionRightPayloadBound_le
    (left := funcCodeFixedEqFormula arity 0 ⋏
      funcCodeFixedEqFormula code 1) inner20 _ hinner20
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := funcCodeFixedEqFormula arity 0 ⋏
      funcCodeFixedEqFormula code 0) inner01 _ hinner01
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := funcCodeFixedEqFormula arity 0 ⋏
          funcCodeFixedEqFormula code 0)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := funcCodeFixedEqFormula arity 0 ⋏
            funcCodeFixedEqFormula code 1)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := funcCodeFixedEqFormula arity 2 ⋏
              funcCodeFixedEqFormula code 1)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (funcCodeFixedEqCertificate arity 2 hpair.1)
              (funcCodeFixedEqCertificate code 0 hpair.2))))) ≤ _
  unfold funcCodeValidCase20PayloadEnvelope
  simpa only [pair, inner20, inner01] using houter

theorem funcCodeValidCase21Certificate_structuralPayloadBound_le_public
    (arity code : Nat) (hpair : arity = 2 ∧ code = 1) :
    hybridFormulaStructuralPayloadBound
        (funcCodeValidCase21Certificate arity code hpair) ≤
      funcCodeValidCase21PayloadEnvelope arity code := by
  let pair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (funcCodeFixedEqCertificate arity 2 hpair.1)
    (funcCodeFixedEqCertificate code 1 hpair.2)
  have hpairResource :=
    funcCodeValidPairCertificate_structuralPayloadBound_le_public
      arity 2 code 1 hpair.1 hpair.2
  let inner21 := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := funcCodeFixedEqFormula arity 2 ⋏
      funcCodeFixedEqFormula code 0) pair
  have hinner21 := transparentHybridDisjunctionRightPayloadBound_le
    (left := funcCodeFixedEqFormula arity 2 ⋏
      funcCodeFixedEqFormula code 0) pair _ hpairResource
  let inner01 := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := funcCodeFixedEqFormula arity 0 ⋏
      funcCodeFixedEqFormula code 1) inner21
  have hinner01 := transparentHybridDisjunctionRightPayloadBound_le
    (left := funcCodeFixedEqFormula arity 0 ⋏
      funcCodeFixedEqFormula code 1) inner21 _ hinner21
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := funcCodeFixedEqFormula arity 0 ⋏
      funcCodeFixedEqFormula code 0) inner01 _ hinner01
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := funcCodeFixedEqFormula arity 0 ⋏
          funcCodeFixedEqFormula code 0)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := funcCodeFixedEqFormula arity 0 ⋏
            funcCodeFixedEqFormula code 1)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := funcCodeFixedEqFormula arity 2 ⋏
              funcCodeFixedEqFormula code 0)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (funcCodeFixedEqCertificate arity 2 hpair.1)
              (funcCodeFixedEqCertificate code 1 hpair.2))))) ≤ _
  unfold funcCodeValidCase21PayloadEnvelope
  simpa only [pair, inner21, inner01] using houter

def compactAdditiveArithmeticFuncCodeValidPayloadEnvelope
    (arity code : Nat) : Nat :=
  if _h00 : arity = 0 ∧ code = 0 then
    funcCodeValidCase00PayloadEnvelope arity code
  else if _h01 : arity = 0 ∧ code = 1 then
    funcCodeValidCase01PayloadEnvelope arity code
  else if _h20 : arity = 2 ∧ code = 0 then
    funcCodeValidCase20PayloadEnvelope arity code
  else
    funcCodeValidCase21PayloadEnvelope arity code

theorem
    compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificate_structuralPayloadBound_le_public
    (arity code : Nat) (hvalid : ArithmeticFuncCodeValid arity code) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificate
          arity code hvalid) ≤
      compactAdditiveArithmeticFuncCodeValidPayloadEnvelope arity code := by
  by_cases h00 : arity = 0 ∧ code = 0
  · simpa [compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificate,
      compactAdditiveArithmeticFuncCodeValidPayloadEnvelope, h00] using
      funcCodeValidCase00Certificate_structuralPayloadBound_le_public
        arity code h00
  · by_cases h01 : arity = 0 ∧ code = 1
    · simpa [compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificate,
        compactAdditiveArithmeticFuncCodeValidPayloadEnvelope, h00, h01] using
        funcCodeValidCase01Certificate_structuralPayloadBound_le_public
          arity code h01
    · by_cases h20 : arity = 2 ∧ code = 0
      · simpa [compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificate,
          compactAdditiveArithmeticFuncCodeValidPayloadEnvelope, h00, h01,
          h20] using
          funcCodeValidCase20Certificate_structuralPayloadBound_le_public
            arity code h20
      · have h21 : arity = 2 ∧ code = 1 := by
          unfold ArithmeticFuncCodeValid at hvalid
          rcases hvalid with hvalid | hvalid | hvalid | hvalid
          · exact False.elim (h00 hvalid)
          · exact False.elim (h01 hvalid)
          · exact False.elim (h20 hvalid)
          · exact hvalid
        simpa [compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificate,
          compactAdditiveArithmeticFuncCodeValidPayloadEnvelope, h00, h01,
          h20, h21] using
          funcCodeValidCase21Certificate_structuralPayloadBound_le_public
            arity code h21

theorem
    compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (arity code : Nat) (hvalid : ArithmeticFuncCodeValid arity code) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph
          arity code hvalid) ≤
      compactAdditiveArithmeticFuncCodeValidPayloadEnvelope arity code := by
  simpa only [
    compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph,
    hybridFormulaStructuralPayloadBound] using
    compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificate_structuralPayloadBound_le_public
      arity code hvalid

def funcCodeInvalidPairPayloadEnvelope
    (left leftExpected right rightExpected : Nat) : Nat :=
  if _hleft : left = leftExpected then
    transparentHybridDisjunctionRightPayloadEnvelope funcCodeZeroValuation
      (funcCodeFixedNeFormula left leftExpected)
      (funcCodeFixedNeFormula right rightExpected)
      (funcCodeFixedNePayloadPolynomial right rightExpected)
  else
    transparentHybridDisjunctionLeftPayloadEnvelope funcCodeZeroValuation
      (funcCodeFixedNeFormula left leftExpected)
      (funcCodeFixedNeFormula right rightExpected)
      (funcCodeFixedNePayloadPolynomial left leftExpected)

theorem funcCodeInvalidPairCertificate_structuralPayloadBound_le_public
    (left leftExpected right rightExpected : Nat)
    (hinvalid : ¬(left = leftExpected ∧ right = rightExpected)) :
    hybridFormulaStructuralPayloadBound
        (funcCodeInvalidPairCertificate left leftExpected right rightExpected
          hinvalid) ≤
      funcCodeInvalidPairPayloadEnvelope left leftExpected right
        rightExpected := by
  by_cases hleft : left = leftExpected
  · have hright : right ≠ rightExpected := by
      intro hright
      exact hinvalid ⟨hleft, hright⟩
    have hresource :=
      funcCodeFixedNeCertificate_structuralPayloadBound_le_public
        right rightExpected hright
    have houter := transparentHybridDisjunctionRightPayloadBound_le
      (left := funcCodeFixedNeFormula left leftExpected)
      (funcCodeFixedNeCertificate right rightExpected hright) _ hresource
    simp only [funcCodeInvalidPairCertificate]
    rw [dif_pos hleft]
    unfold funcCodeInvalidPairPayloadEnvelope
    rw [dif_pos hleft]
    simpa only using houter
  · have hresource :=
      funcCodeFixedNeCertificate_structuralPayloadBound_le_public
        left leftExpected hleft
    have houter := transparentHybridDisjunctionLeftPayloadBound_le
      (right := funcCodeFixedNeFormula right rightExpected)
      (funcCodeFixedNeCertificate left leftExpected hleft) _ hresource
    simp only [funcCodeInvalidPairCertificate]
    rw [dif_neg hleft]
    unfold funcCodeInvalidPairPayloadEnvelope
    rw [dif_neg hleft]
    simpa only using houter

def compactAdditiveArithmeticFuncCodeInvalidPayloadEnvelope
    (arity code : Nat) : Nat :=
  let pair00 := funcCodeFixedNeFormula arity 0 ⋎
    funcCodeFixedNeFormula code 0
  let pair01 := funcCodeFixedNeFormula arity 0 ⋎
    funcCodeFixedNeFormula code 1
  let pair20 := funcCodeFixedNeFormula arity 2 ⋎
    funcCodeFixedNeFormula code 0
  let pair21 := funcCodeFixedNeFormula arity 2 ⋎
    funcCodeFixedNeFormula code 1
  let resource21 := funcCodeInvalidPairPayloadEnvelope arity 2 code 1
  let resource20Tail := transparentHybridConjunctionPayloadEnvelope
    funcCodeZeroValuation pair20 pair21
    (funcCodeInvalidPairPayloadEnvelope arity 2 code 0) resource21
  let resource01Tail := transparentHybridConjunctionPayloadEnvelope
    funcCodeZeroValuation pair01 (pair20 ⋏ pair21)
    (funcCodeInvalidPairPayloadEnvelope arity 0 code 1) resource20Tail
  transparentHybridConjunctionPayloadEnvelope funcCodeZeroValuation
    pair00 (pair01 ⋏ (pair20 ⋏ pair21))
    (funcCodeInvalidPairPayloadEnvelope arity 0 code 0) resource01Tail

theorem
    compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificate_structuralPayloadBound_le_public
    (arity code : Nat) (hinvalid : ¬ArithmeticFuncCodeValid arity code) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificate
          arity code hinvalid) ≤
      compactAdditiveArithmeticFuncCodeInvalidPayloadEnvelope arity code := by
  have h00 : ¬(arity = 0 ∧ code = 0) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  have h01 : ¬(arity = 0 ∧ code = 1) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  have h20 : ¬(arity = 2 ∧ code = 0) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  have h21 : ¬(arity = 2 ∧ code = 1) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticFuncCodeValid, hpair])
  let certificate00 :=
    funcCodeInvalidPairCertificate arity 0 code 0 h00
  let certificate01 :=
    funcCodeInvalidPairCertificate arity 0 code 1 h01
  let certificate20 :=
    funcCodeInvalidPairCertificate arity 2 code 0 h20
  let certificate21 :=
    funcCodeInvalidPairCertificate arity 2 code 1 h21
  have hresource00 :=
    funcCodeInvalidPairCertificate_structuralPayloadBound_le_public
      arity 0 code 0 h00
  have hresource01 :=
    funcCodeInvalidPairCertificate_structuralPayloadBound_le_public
      arity 0 code 1 h01
  have hresource20 :=
    funcCodeInvalidPairCertificate_structuralPayloadBound_le_public
      arity 2 code 0 h20
  have hresource21 :=
    funcCodeInvalidPairCertificate_structuralPayloadBound_le_public
      arity 2 code 1 h21
  let certificate20Tail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      certificate20 certificate21
  have hresource20Tail := transparentHybridConjunctionPayloadBound_le
    certificate20 certificate21 _ _ hresource20 hresource21
  let certificate01Tail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      certificate01 certificate20Tail
  have hresource01Tail := transparentHybridConjunctionPayloadBound_le
    certificate01 certificate20Tail _ _ hresource01 hresource20Tail
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    certificate00 certificate01Tail
  have hdirect := transparentHybridConjunctionPayloadBound_le
    certificate00 certificate01Tail _ _ hresource00 hresource01Tail
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        certificate00 certificate01Tail) ≤ _
  unfold compactAdditiveArithmeticFuncCodeInvalidPayloadEnvelope
  simpa only [certificate00, certificate01, certificate20, certificate21,
    certificate20Tail, certificate01Tail, direct] using hdirect

theorem
    compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (arity code : Nat) (hinvalid : ¬ArithmeticFuncCodeValid arity code) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph
          arity code hinvalid) ≤
      compactAdditiveArithmeticFuncCodeInvalidPayloadEnvelope arity code := by
  simpa only [
    compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph,
    hybridFormulaStructuralPayloadBound] using
    compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificate_structuralPayloadBound_le_public
      arity code hinvalid

#print axioms
  compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
#print axioms
  compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidPublicBounds
