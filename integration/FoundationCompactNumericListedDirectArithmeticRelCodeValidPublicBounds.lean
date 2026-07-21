import integration.FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resources for arithmetic relation-code validity

Both accepted relation-code pairs and both rejected-pair witnesses are
charged by explicit atomic and connective envelopes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticRelCodeValidPublicBounds

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
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate

private abbrev relCodeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate.zeroValuation

private theorem relCodeFixedNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (relCodeFixedNumeralTerm value).freeVariables = ∅ := by
  simp [relCodeFixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

def relCodeFixedEqPayloadPolynomial (value expected : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial relCodeZeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm value, relCodeFixedNumeralTerm expected]

theorem relCodeFixedEqCertificate_structuralPayloadBound_le_public
    (value expected : Nat) (heq : value = expected) :
    hybridFormulaStructuralPayloadBound
        (relCodeFixedEqCertificate value expected heq) <=
      relCodeFixedEqPayloadPolynomial value expected := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (relCodeFixedNumeralTerm expected).freeVariables ⊆ {0} := by
    rw [relCodeFixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    relCodeZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, relCodeFixedNumeralTerm expected]
    hleft hright
  change compilePositiveRelationPayloadResource relCodeZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, relCodeFixedNumeralTerm expected] <= _
  exact hpublic

def relCodeFixedNePayloadPolynomial (value expected : Nat) : Nat :=
  compileNegativeRelationPayloadPolynomial relCodeZeroValuation
    Language.Eq.eq
    ![shortBinaryNumeralTerm value, relCodeFixedNumeralTerm expected]

theorem relCodeFixedNeCertificate_structuralPayloadBound_le_public
    (value expected : Nat) (hne : value ≠ expected) :
    hybridFormulaStructuralPayloadBound
        (relCodeFixedNeCertificate value expected hne) <=
      relCodeFixedNePayloadPolynomial value expected := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (relCodeFixedNumeralTerm expected).freeVariables ⊆ {0} := by
    rw [relCodeFixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compileNegativeRelationPayloadResource_le_publicPolynomial
    relCodeZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, relCodeFixedNumeralTerm expected]
    hleft hright
  change compileNegativeRelationPayloadResource relCodeZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, relCodeFixedNumeralTerm expected] <= _
  exact hpublic

def relCodeValidPairPayloadEnvelope
    (left leftExpected right rightExpected : Nat) : Nat :=
  transparentHybridConjunctionPayloadEnvelope relCodeZeroValuation
    (relCodeFixedEqFormula left leftExpected)
    (relCodeFixedEqFormula right rightExpected)
    (relCodeFixedEqPayloadPolynomial left leftExpected)
    (relCodeFixedEqPayloadPolynomial right rightExpected)

theorem relCodeValidPairCertificate_structuralPayloadBound_le_public
    (left leftExpected right rightExpected : Nat)
    (hleft : left = leftExpected) (hright : right = rightExpected) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (relCodeFixedEqCertificate left leftExpected hleft)
          (relCodeFixedEqCertificate right rightExpected hright)) <=
      relCodeValidPairPayloadEnvelope left leftExpected right
        rightExpected := by
  exact transparentHybridConjunctionPayloadBound_le
    (relCodeFixedEqCertificate left leftExpected hleft)
    (relCodeFixedEqCertificate right rightExpected hright) _ _
    (relCodeFixedEqCertificate_structuralPayloadBound_le_public
      left leftExpected hleft)
    (relCodeFixedEqCertificate_structuralPayloadBound_le_public
      right rightExpected hright)

def relCodeValidCase20PayloadEnvelope (arity code : Nat) : Nat :=
  let branch20 := relCodeFixedEqFormula arity 2 ⋏
    relCodeFixedEqFormula code 0
  let branch21 := relCodeFixedEqFormula arity 2 ⋏
    relCodeFixedEqFormula code 1
  transparentHybridDisjunctionLeftPayloadEnvelope relCodeZeroValuation
    branch20 branch21 (relCodeValidPairPayloadEnvelope arity 2 code 0)

def relCodeValidCase21PayloadEnvelope (arity code : Nat) : Nat :=
  let branch20 := relCodeFixedEqFormula arity 2 ⋏
    relCodeFixedEqFormula code 0
  let branch21 := relCodeFixedEqFormula arity 2 ⋏
    relCodeFixedEqFormula code 1
  transparentHybridDisjunctionRightPayloadEnvelope relCodeZeroValuation
    branch20 branch21 (relCodeValidPairPayloadEnvelope arity 2 code 1)

theorem relCodeValidCase20Certificate_structuralPayloadBound_le_public
    (arity code : Nat) (hpair : arity = 2 ∧ code = 0) :
    hybridFormulaStructuralPayloadBound
        (relCodeValidCase20Certificate arity code hpair) <=
      relCodeValidCase20PayloadEnvelope arity code := by
  let pair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (relCodeFixedEqCertificate arity 2 hpair.1)
    (relCodeFixedEqCertificate code 0 hpair.2)
  have hpairResource :=
    relCodeValidPairCertificate_structuralPayloadBound_le_public
      arity 2 code 0 hpair.1 hpair.2
  have houter := transparentHybridDisjunctionLeftPayloadBound_le
    (right := relCodeFixedEqFormula arity 2 ⋏
      relCodeFixedEqFormula code 1) pair _ hpairResource
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := relCodeFixedEqFormula arity 2 ⋏
          relCodeFixedEqFormula code 1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (relCodeFixedEqCertificate arity 2 hpair.1)
          (relCodeFixedEqCertificate code 0 hpair.2))) <= _
  unfold relCodeValidCase20PayloadEnvelope
  simpa only [pair] using houter

theorem relCodeValidCase21Certificate_structuralPayloadBound_le_public
    (arity code : Nat) (hpair : arity = 2 ∧ code = 1) :
    hybridFormulaStructuralPayloadBound
        (relCodeValidCase21Certificate arity code hpair) <=
      relCodeValidCase21PayloadEnvelope arity code := by
  let pair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (relCodeFixedEqCertificate arity 2 hpair.1)
    (relCodeFixedEqCertificate code 1 hpair.2)
  have hpairResource :=
    relCodeValidPairCertificate_structuralPayloadBound_le_public
      arity 2 code 1 hpair.1 hpair.2
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := relCodeFixedEqFormula arity 2 ⋏
      relCodeFixedEqFormula code 0) pair _ hpairResource
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := relCodeFixedEqFormula arity 2 ⋏
          relCodeFixedEqFormula code 0)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (relCodeFixedEqCertificate arity 2 hpair.1)
          (relCodeFixedEqCertificate code 1 hpair.2))) <= _
  unfold relCodeValidCase21PayloadEnvelope
  simpa only [pair] using houter

def compactAdditiveArithmeticRelCodeValidPayloadEnvelope
    (arity code : Nat) : Nat :=
  if _h20 : arity = 2 ∧ code = 0 then
    relCodeValidCase20PayloadEnvelope arity code
  else
    relCodeValidCase21PayloadEnvelope arity code

theorem
    compactAdditiveArithmeticRelCodeValidExplicitHybridCertificate_structuralPayloadBound_le_public
    (arity code : Nat) (hvalid : ArithmeticRelCodeValid arity code) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticRelCodeValidExplicitHybridCertificate
          arity code hvalid) <=
      compactAdditiveArithmeticRelCodeValidPayloadEnvelope arity code := by
  by_cases h20 : arity = 2 ∧ code = 0
  · simpa [compactAdditiveArithmeticRelCodeValidExplicitHybridCertificate,
      compactAdditiveArithmeticRelCodeValidPayloadEnvelope, h20] using
      relCodeValidCase20Certificate_structuralPayloadBound_le_public
        arity code h20
  · have h21 : arity = 2 ∧ code = 1 := by
      unfold ArithmeticRelCodeValid at hvalid
      rcases hvalid with hvalid | hvalid
      · exact False.elim (h20 hvalid)
      · exact hvalid
    simpa [compactAdditiveArithmeticRelCodeValidExplicitHybridCertificate,
      compactAdditiveArithmeticRelCodeValidPayloadEnvelope, h20, h21] using
      relCodeValidCase21Certificate_structuralPayloadBound_le_public
        arity code h21

theorem
    compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (arity code : Nat) (hvalid : ArithmeticRelCodeValid arity code) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph
          arity code hvalid) <=
      compactAdditiveArithmeticRelCodeValidPayloadEnvelope arity code := by
  simpa only [
    compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph,
    hybridFormulaStructuralPayloadBound] using
    compactAdditiveArithmeticRelCodeValidExplicitHybridCertificate_structuralPayloadBound_le_public
      arity code hvalid

def relCodeInvalidPairPayloadEnvelope
    (left leftExpected right rightExpected : Nat) : Nat :=
  if _hleft : left = leftExpected then
    transparentHybridDisjunctionRightPayloadEnvelope relCodeZeroValuation
      (relCodeFixedNeFormula left leftExpected)
      (relCodeFixedNeFormula right rightExpected)
      (relCodeFixedNePayloadPolynomial right rightExpected)
  else
    transparentHybridDisjunctionLeftPayloadEnvelope relCodeZeroValuation
      (relCodeFixedNeFormula left leftExpected)
      (relCodeFixedNeFormula right rightExpected)
      (relCodeFixedNePayloadPolynomial left leftExpected)

theorem relCodeInvalidPairCertificate_structuralPayloadBound_le_public
    (left leftExpected right rightExpected : Nat)
    (hinvalid : ¬(left = leftExpected ∧ right = rightExpected)) :
    hybridFormulaStructuralPayloadBound
        (relCodeInvalidPairCertificate left leftExpected right rightExpected
          hinvalid) <=
      relCodeInvalidPairPayloadEnvelope left leftExpected right
        rightExpected := by
  by_cases hleft : left = leftExpected
  · have hright : right ≠ rightExpected := by
      intro hright
      exact hinvalid ⟨hleft, hright⟩
    have hresource :=
      relCodeFixedNeCertificate_structuralPayloadBound_le_public
        right rightExpected hright
    have houter := transparentHybridDisjunctionRightPayloadBound_le
      (left := relCodeFixedNeFormula left leftExpected)
      (relCodeFixedNeCertificate right rightExpected hright) _ hresource
    simp only [relCodeInvalidPairCertificate]
    rw [dif_pos hleft]
    unfold relCodeInvalidPairPayloadEnvelope
    rw [dif_pos hleft]
    simpa only using houter
  · have hresource :=
      relCodeFixedNeCertificate_structuralPayloadBound_le_public
        left leftExpected hleft
    have houter := transparentHybridDisjunctionLeftPayloadBound_le
      (right := relCodeFixedNeFormula right rightExpected)
      (relCodeFixedNeCertificate left leftExpected hleft) _ hresource
    simp only [relCodeInvalidPairCertificate]
    rw [dif_neg hleft]
    unfold relCodeInvalidPairPayloadEnvelope
    rw [dif_neg hleft]
    simpa only using houter

def compactAdditiveArithmeticRelCodeInvalidPayloadEnvelope
    (arity code : Nat) : Nat :=
  let pair20 := relCodeFixedNeFormula arity 2 ⋎
    relCodeFixedNeFormula code 0
  let pair21 := relCodeFixedNeFormula arity 2 ⋎
    relCodeFixedNeFormula code 1
  transparentHybridConjunctionPayloadEnvelope relCodeZeroValuation
    pair20 pair21
    (relCodeInvalidPairPayloadEnvelope arity 2 code 0)
    (relCodeInvalidPairPayloadEnvelope arity 2 code 1)

theorem
    compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificate_structuralPayloadBound_le_public
    (arity code : Nat) (hinvalid : ¬ArithmeticRelCodeValid arity code) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificate
          arity code hinvalid) <=
      compactAdditiveArithmeticRelCodeInvalidPayloadEnvelope arity code := by
  have h20 : ¬(arity = 2 ∧ code = 0) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticRelCodeValid, hpair])
  have h21 : ¬(arity = 2 ∧ code = 1) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticRelCodeValid, hpair])
  let certificate20 :=
    relCodeInvalidPairCertificate arity 2 code 0 h20
  let certificate21 :=
    relCodeInvalidPairCertificate arity 2 code 1 h21
  have hresource20 :=
    relCodeInvalidPairCertificate_structuralPayloadBound_le_public
      arity 2 code 0 h20
  have hresource21 :=
    relCodeInvalidPairCertificate_structuralPayloadBound_le_public
      arity 2 code 1 h21
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    certificate20 certificate21
  have hdirect := transparentHybridConjunctionPayloadBound_le certificate20
    certificate21 _ _ hresource20 hresource21
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        certificate20 certificate21) <= _
  unfold compactAdditiveArithmeticRelCodeInvalidPayloadEnvelope
  simpa only [certificate20, certificate21, direct] using hdirect

theorem
    compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (arity code : Nat) (hinvalid : ¬ArithmeticRelCodeValid arity code) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
          arity code hinvalid) <=
      compactAdditiveArithmeticRelCodeInvalidPayloadEnvelope arity code := by
  simpa only [
    compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph,
    hybridFormulaStructuralPayloadBound] using
    compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificate_structuralPayloadBound_le_public
      arity code hinvalid

#print axioms
  compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
#print axioms
  compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectArithmeticRelCodeValidPublicBounds
