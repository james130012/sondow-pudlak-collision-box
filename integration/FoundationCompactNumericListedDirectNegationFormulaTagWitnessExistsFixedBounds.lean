import integration.FoundationCompactNumericListedDirectNegationFormulaTagEvenWitnessPostFixedBounds
import integration.FoundationCompactNumericListedDirectNegationFormulaTagOddWitnessPostFixedBounds
import integration.FoundationCompactNumericListedDirectNegationFormulaTagWitnessOpenSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds

/-!
# Fixed existential resources for both negation-tag parity witnesses

The branch-supplied pair is installed into the open body.  The resulting
closed three-leaf certificate and all existential assembly costs are bounded
only by the common numeral bit bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNegationFormulaTagWitnessExistsFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagAtomicFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagWitnessPostFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagEvenWitnessPostFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagOddWitnessPostFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagWitnessOpenSyntaxFixedBounds

private abbrev tagZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation

def negationFormulaTagWitnessExistsFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  hybridExistsWitnessGeneralPayloadEnvelope
    (negationFormulaTagWitnessExistentialSyntaxPolynomial bitBound)
    (negationFormulaTagWitnessPostFixedPayloadPolynomial bitBound)

private theorem witnessPairCode_le_existsSyntax
    (pair bitBound : Nat) (hpair : pair < 4) :
    (binaryTermCode (shortBinaryNumeralTerm pair)).length <=
      negationFormulaTagWitnessExistentialSyntaxPolynomial bitBound := by
  have hpairCode := pairShortNumeralCode_le pair bitBound hpair
  unfold negationFormulaTagWitnessExistentialSyntaxPolynomial
  omega

theorem evenWitnessCertificate_structuralPayloadBound_le_fixed
    (tag mapped pair bitBound : Nat)
    (hpair : pair < 4)
    (htag : tag = 2 * pair)
    (hmapped : mapped = tag + 1)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactNegationFormulaTagEvenWitnessCertificate
          tag mapped pair hpair htag hmapped) <=
      negationFormulaTagWitnessExistsFixedPayloadPolynomial bitBound := by
  let body := compactNegationFormulaTagEvenWitnessBody tag mapped
  let pairCertificate := pairLtFourCertificate pair hpair
  let equalityCertificate := evenTagEqualityCertificate tag pair htag
  let successorCertificate :=
    mappedSuccessorCertificate tag mapped hmapped
  let innerCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      equalityCertificate successorCertificate
  let postCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      pairCertificate innerCertificate
  let instantiated := CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactNegationFormulaTagEvenWitnessBody_substitution_alignment
      tag mapped pair).symm postCertificate
  let postResource :=
    negationFormulaTagWitnessPostFixedPayloadPolynomial bitBound
  let syntaxResource :=
    negationFormulaTagWitnessExistentialSyntaxPolynomial bitBound
  have hpost :
      hybridFormulaStructuralPayloadBound postCertificate <= postResource := by
    dsimp only [postCertificate, postResource, pairCertificate,
      equalityCertificate, successorCertificate, innerCertificate]
    exact evenPostCertificate_structuralPayloadBound_le_fixed
      tag mapped pair bitBound hpair htag hmapped htagSize hmappedSize
  have hinstantiated :
      hybridFormulaStructuralPayloadBound instantiated <= postResource := by
    simpa only [instantiated, hybridFormulaStructuralPayloadBound] using hpost
  have hexistsRaw := hybridExistsWitnessStructuralPayloadBound_le_envelope
    body pair instantiated postResource hinstantiated
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold negationFormulaTagWitnessExistentialSyntaxPolynomial
    omega
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (∃⁰ body : ValuationFormula).freeVariables
            tagZeroValuation) <= syntaxResource := by
    have hclosed :=
      evenWitnessExistential_freeVariables_eq_empty tag mapped
    dsimp only [body] at hclosed ⊢
    rw [hclosed]
    simp [valuationContext,
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
  have hbody :
      (binaryFormulaCode body).length <= syntaxResource := by
    have hraw := evenWitnessBody_code_le_fixed tag mapped bitBound htagSize
      hmappedSize
    dsimp only [body, syntaxResource]
    unfold negationFormulaTagWitnessExistentialSyntaxPolynomial
    omega
  have hwitness :
      (binaryTermCode (shortBinaryNumeralTerm pair)).length <=
        syntaxResource := by
    dsimp only [syntaxResource]
    exact witnessPairCode_le_existsSyntax pair bitBound hpair
  have hinstantiatedCode :
      (binaryFormulaCode
        (body/[shortBinaryNumeralTerm pair])).length <= syntaxResource := by
    have hpostCode :=
      evenPostFormula_code_le tag mapped pair bitBound hpair htagSize
        hmappedSize
    rw [compactNegationFormulaTagEvenWitnessBody_substitution_alignment]
    dsimp only [syntaxResource]
    unfold negationFormulaTagWitnessExistentialSyntaxPolynomial
    omega
  have hexistentialCode :
      (binaryFormulaCode (∃⁰ body : ValuationFormula)).length <=
        syntaxResource := by
    have hraw := evenWitnessExistentialFormula_code_le_fixed tag mapped
      bitBound htagSize hmappedSize
    simpa only [body, syntaxResource] using hraw
  have hgeneral := hybridExistsWitnessStructuralPayloadEnvelope_le_general
    tagZeroValuation body pair postResource syntaxResource hpositive hcontext
    hbody hwitness hinstantiatedCode hexistentialCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.existsWitness
        body pair instantiated) <= _
  exact hexistsRaw.trans (by
    simpa only [negationFormulaTagWitnessExistsFixedPayloadPolynomial,
      postResource, syntaxResource] using hgeneral)

theorem oddWitnessCertificate_structuralPayloadBound_le_fixed
    (tag mapped pair bitBound : Nat)
    (hpair : pair < 4)
    (htag : tag = 2 * pair + 1)
    (hmapped : tag = mapped + 1)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactNegationFormulaTagOddWitnessCertificate
          tag mapped pair hpair htag hmapped) <=
      negationFormulaTagWitnessExistsFixedPayloadPolynomial bitBound := by
  let body := compactNegationFormulaTagOddWitnessBody tag mapped
  let pairCertificate := pairLtFourCertificate pair hpair
  let equalityCertificate := oddTagEqualityCertificate tag pair htag
  let successorCertificate :=
    tagMappedSuccessorCertificate tag mapped hmapped
  let innerCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      equalityCertificate successorCertificate
  let postCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      pairCertificate innerCertificate
  let instantiated := CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactNegationFormulaTagOddWitnessBody_substitution_alignment
      tag mapped pair).symm postCertificate
  let postResource :=
    negationFormulaTagWitnessPostFixedPayloadPolynomial bitBound
  let syntaxResource :=
    negationFormulaTagWitnessExistentialSyntaxPolynomial bitBound
  have hpost :
      hybridFormulaStructuralPayloadBound postCertificate <= postResource := by
    dsimp only [postCertificate, postResource, pairCertificate,
      equalityCertificate, successorCertificate, innerCertificate]
    exact oddPostCertificate_structuralPayloadBound_le_fixed
      tag mapped pair bitBound hpair htag hmapped htagSize hmappedSize
  have hinstantiated :
      hybridFormulaStructuralPayloadBound instantiated <= postResource := by
    simpa only [instantiated, hybridFormulaStructuralPayloadBound] using hpost
  have hexistsRaw := hybridExistsWitnessStructuralPayloadBound_le_envelope
    body pair instantiated postResource hinstantiated
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold negationFormulaTagWitnessExistentialSyntaxPolynomial
    omega
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext (∃⁰ body : ValuationFormula).freeVariables
            tagZeroValuation) <= syntaxResource := by
    have hclosed :=
      oddWitnessExistential_freeVariables_eq_empty tag mapped
    dsimp only [body] at hclosed ⊢
    rw [hclosed]
    simp [valuationContext,
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
  have hbody :
      (binaryFormulaCode body).length <= syntaxResource := by
    have hraw := oddWitnessBody_code_le_fixed tag mapped bitBound htagSize
      hmappedSize
    dsimp only [body, syntaxResource]
    unfold negationFormulaTagWitnessExistentialSyntaxPolynomial
    omega
  have hwitness :
      (binaryTermCode (shortBinaryNumeralTerm pair)).length <=
        syntaxResource := by
    dsimp only [syntaxResource]
    exact witnessPairCode_le_existsSyntax pair bitBound hpair
  have hinstantiatedCode :
      (binaryFormulaCode
        (body/[shortBinaryNumeralTerm pair])).length <= syntaxResource := by
    have hpostCode :=
      oddPostFormula_code_le tag mapped pair bitBound hpair htagSize
        hmappedSize
    rw [compactNegationFormulaTagOddWitnessBody_substitution_alignment]
    dsimp only [syntaxResource]
    unfold negationFormulaTagWitnessExistentialSyntaxPolynomial
    omega
  have hexistentialCode :
      (binaryFormulaCode (∃⁰ body : ValuationFormula)).length <=
        syntaxResource := by
    have hraw := oddWitnessExistentialFormula_code_le_fixed tag mapped
      bitBound htagSize hmappedSize
    simpa only [body, syntaxResource] using hraw
  have hgeneral := hybridExistsWitnessStructuralPayloadEnvelope_le_general
    tagZeroValuation body pair postResource syntaxResource hpositive hcontext
    hbody hwitness hinstantiatedCode hexistentialCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.existsWitness
        body pair instantiated) <= _
  exact hexistsRaw.trans (by
    simpa only [negationFormulaTagWitnessExistsFixedPayloadPolynomial,
      postResource, syntaxResource] using hgeneral)

#print axioms evenWitnessCertificate_structuralPayloadBound_le_fixed
#print axioms oddWitnessCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectNegationFormulaTagWitnessExistsFixedBounds
