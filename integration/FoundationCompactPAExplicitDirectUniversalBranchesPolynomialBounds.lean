import integration.FoundationCompactPAExplicitDirectUniversalBranches
import integration.FoundationCompactPABoundedUniversalPolynomialBounds

/-!
# Polynomial assembly bounds for explicit direct universal branches

The branch certificates in this module are already direct contextual PA
proofs.  Their payload lengths are therefore treated as an explicit leaf
resource; no hybrid certificate payload bound is involved.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedCertifiedVerifier
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitDirectUniversalBranches

def explicitDirectUniversalSyntaxResource
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  bound + (binaryFormulaCode body).length

def explicitDirectUniversalFormulaEnvelope
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (explicitDirectUniversalSyntaxResource bound body) +
    2 * (binaryFormulaCode body).length

def explicitDirectUniversalLocalPayloadEnvelope
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  smallContextAssemblyEnvelope
    (explicitDirectUniversalFormulaEnvelope bound body)

def explicitDirectUniversalBranchesPayloadPolynomial
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (leafBound : Nat) : Nat :=
  (bound + 1) *
    (leafBound +
      3 * explicitDirectUniversalLocalPayloadEnvelope bound body)

private theorem target_code_le_formulaEnvelope
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode (Rewriting.free body)).length <=
      explicitDirectUniversalFormulaEnvelope bound body := by
  have hfree := binaryFormulaCode_free_length_le body
  unfold explicitDirectUniversalFormulaEnvelope
  omega

private theorem finiteContext_formulaCodeBound
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    FormulaCodeBound
      (contextualFiniteBoundContext
        (∅ : Finset LO.FirstOrder.ArithmeticProposition) bound)
      (explicitDirectUniversalFormulaEnvelope bound body) := by
  let resource := explicitDirectUniversalSyntaxResource bound body
  have hbound : bound ≤ resource := by
    dsimp only [resource]
    unfold explicitDirectUniversalSyntaxResource
    omega
  have hbase :=
    finiteBoundContext_formulaCodeBound_boundedUniversal
      bound resource hbound
  have henvelope :
      boundedUniversalClosedFormulaEnvelope resource ≤
        explicitDirectUniversalFormulaEnvelope bound body := by
    dsimp only [resource]
    unfold explicitDirectUniversalFormulaEnvelope
    omega
  intro formula hformula
  have hmember : formula ∈
      FoundationCompactPABoundedUniversalCompiler.finiteBoundContext bound := by
    simpa [contextualFiniteBoundContext,
      FoundationCompactPABoundedUniversalCompiler.finiteBoundContext] using
        hformula
  exact (hbase formula hmember).trans henvelope

private theorem baseAssemblyCost_le
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost
          (Rewriting.free body) +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert (Rewriting.free body)
            (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
              (contextualFiniteBoundContext
                (∅ : Finset LO.FirstOrder.ArithmeticProposition) bound))) ≤
      2 * explicitDirectUniversalLocalPayloadEnvelope bound body := by
  let formulaEnvelope := explicitDirectUniversalFormulaEnvelope bound body
  have htarget :
      (binaryFormulaCode (Rewriting.free body)).length ≤ formulaEnvelope := by
    exact target_code_le_formulaEnvelope bound body
  have hfalseBase :=
    negatedFalse_code_le_boundedUniversal
      (explicitDirectUniversalSyntaxResource bound body)
  have hfalse :
      (binaryFormulaCode
        (∼(⊥ : LO.FirstOrder.ArithmeticProposition))).length <=
          formulaEnvelope := by
    exact hfalseBase.trans (by
      dsimp only [formulaEnvelope]
      unfold explicitDirectUniversalFormulaEnvelope
      omega)
  have hcontext := finiteContext_formulaCodeBound bound body
  have hweakContext : FormulaCodeBound
      (insert (Rewriting.free body)
        (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
          (contextualFiniteBoundContext
            (∅ : Finset LO.FirstOrder.ArithmeticProposition) bound)))
      formulaEnvelope :=
    (hcontext.insert hfalse).insert htarget
  have hcard :
      (insert (Rewriting.free body)
        (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
          (contextualFiniteBoundContext
            (∅ : Finset LO.FirstOrder.ArithmeticProposition) bound))).card <= 8 := by
    have hbase :
        (contextualFiniteBoundContext
          (∅ : Finset LO.FirstOrder.ArithmeticProposition) bound).card <= 1 := by
      simp [contextualFiniteBoundContext]
    have hfirst := Finset.card_insert_le
      (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
      (contextualFiniteBoundContext
        (∅ : Finset LO.FirstOrder.ArithmeticProposition) bound)
    have hsecond := Finset.card_insert_le (Rewriting.free body)
      (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
        (contextualFiniteBoundContext
          (∅ : Finset LO.FirstOrder.ArithmeticProposition) bound))
    omega
  have hexFalso := exFalsoAssumptionFullPayloadCost_le_small
    (Rewriting.free body) formulaEnvelope htarget hfalse
  have hweakening := weakeningFullAssemblyCost_le_small
    (insert (Rewriting.free body)
      (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
        (contextualFiniteBoundContext
          (∅ : Finset LO.FirstOrder.ArithmeticProposition) bound)))
    formulaEnvelope hcard hweakContext
  unfold explicitDirectUniversalLocalPayloadEnvelope
  dsimp only [formulaEnvelope] at hexFalso hweakening ⊢
  omega

private theorem stepAssemblyCost_le
    (totalBound index : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hindex : index + 1 <= totalBound) :
    let Gamma :=
      (valuationContext
        (∅ : Finset Nat) (fun _ => 0)).image Rewriting.shift
    let target := Rewriting.free body
    let caseFormula := finiteCaseEqualityFormula
      (iteratedSuccessorTerm 0 index) (&0)
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
        (insert target (insert (∼caseFormula) Gamma)) +
      FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
        (insert target
          (insert (∼caseFormula)
            (contextualFiniteBoundContext Gamma totalBound))) +
      CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        (contextualFiniteBoundContext Gamma totalBound) target
        (finiteEqualityCases (&0) index) caseFormula <=
      3 * explicitDirectUniversalLocalPayloadEnvelope totalBound body := by
  let resource := explicitDirectUniversalSyntaxResource totalBound body
  let formulaEnvelope :=
    explicitDirectUniversalFormulaEnvelope totalBound body
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition := ∅
  let target := Rewriting.free body
  let caseFormula := finiteCaseEqualityFormula
    (iteratedSuccessorTerm 0 index) (&0)
  have hresource : totalBound <= resource := by
    dsimp only [resource]
    unfold explicitDirectUniversalSyntaxResource
    omega
  have henvelope :
      boundedUniversalClosedFormulaEnvelope resource <= formulaEnvelope := by
    dsimp only [resource, formulaEnvelope]
    unfold explicitDirectUniversalFormulaEnvelope
    omega
  have htarget :
      (binaryFormulaCode target).length <= formulaEnvelope := by
    dsimp only [target, formulaEnvelope]
    exact target_code_le_formulaEnvelope totalBound body
  have hcaseBase :=
    negatedFiniteCaseEqualityFormula_code_le_boundedUniversal
      index resource (by omega)
  have hcase :
      (binaryFormulaCode (∼caseFormula)).length <= formulaEnvelope := by
    dsimp only [caseFormula]
    exact hcaseBase.trans henvelope
  have hfiniteContext : FormulaCodeBound
      (contextualFiniteBoundContext Gamma totalBound)
      formulaEnvelope := by
    dsimp only [Gamma, formulaEnvelope]
    exact finiteContext_formulaCodeBound totalBound body
  have hempty : FormulaCodeBound Gamma formulaEnvelope := by
    simp [Gamma, FormulaCodeBound]
  have hweakOneBound : FormulaCodeBound
      (insert target (insert (∼caseFormula) Gamma)) formulaEnvelope :=
    (hempty.insert hcase).insert htarget
  have hweakTwoBound : FormulaCodeBound
      (insert target
        (insert (∼caseFormula)
          (contextualFiniteBoundContext Gamma totalBound)))
      formulaEnvelope :=
    (hfiniteContext.insert hcase).insert htarget
  have hcontextCard :
      (contextualFiniteBoundContext Gamma totalBound).card <= 4 := by
    simp [Gamma, contextualFiniteBoundContext]
  have hweakOneCard :
      (insert target (insert (∼caseFormula) Gamma)).card <= 8 := by
    have hfirst := Finset.card_insert_le (∼caseFormula) Gamma
    have hsecond := Finset.card_insert_le target
      (insert (∼caseFormula) Gamma)
    simp only [Gamma, Finset.card_empty] at hfirst hsecond ⊢
    omega
  have hweakTwoCard :
      (insert target
        (insert (∼caseFormula)
          (contextualFiniteBoundContext Gamma totalBound))).card <= 8 := by
    have hbase := hcontextCard
    have hfirst := Finset.card_insert_le (∼caseFormula)
      (contextualFiniteBoundContext Gamma totalBound)
    have hsecond := Finset.card_insert_le target
      (insert (∼caseFormula)
        (contextualFiniteBoundContext Gamma totalBound))
    omega
  have hnegatedLeftBase :=
    negatedFiniteEqualityCases_code_le_boundedUniversal
      index resource (by omega)
  have hnegatedLeft :
      (binaryFormulaCode
        (∼finiteEqualityCases (&0) index)).length <= formulaEnvelope :=
    hnegatedLeftBase.trans henvelope
  have hnegatedDisjunctionBase :=
    negatedFiniteEqualityCases_code_le_boundedUniversal
      (index + 1) resource (by omega)
  have hnegatedDisjunction :
      (binaryFormulaCode
        (∼(finiteEqualityCases (&0) index ⋎ caseFormula))).length <=
          formulaEnvelope := by
    have hraw := hnegatedDisjunctionBase.trans henvelope
    simpa only [caseFormula, finiteEqualityCases_succ] using hraw
  have hweakOne := weakeningFullAssemblyCost_le_small
    (insert target (insert (∼caseFormula) Gamma))
    formulaEnvelope hweakOneCard hweakOneBound
  have hweakTwo := weakeningFullAssemblyCost_le_small
    (insert target
      (insert (∼caseFormula)
        (contextualFiniteBoundContext Gamma totalBound)))
    formulaEnvelope hweakTwoCard hweakTwoBound
  have heliminate :=
    eliminateDisjunctionAssumptionFullAssemblyCost_le_small
      (contextualFiniteBoundContext Gamma totalBound) target
      (finiteEqualityCases (&0) index) caseFormula formulaEnvelope
      hcontextCard hfiniteContext htarget hnegatedLeft hcase
      hnegatedDisjunction
  unfold explicitDirectUniversalLocalPayloadEnvelope
  simp only [valuationContext, Finset.image_empty]
  dsimp only [Gamma, target, caseFormula, formulaEnvelope]
    at hweakOne hweakTwo heliminate ⊢
  omega

theorem directBranchesStructuralPayloadEnvelope_le_uniformPolynomial
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (totalBound leafBound : Nat)
    (branchResource : Nat -> Nat) :
    (caseCount : Nat) ->
    caseCount <= totalBound ->
    (∀ index, branchResource index <= leafBound) ->
    explicitDirectUniversalBranchesStructuralEnvelope
        valuation totalBound body ∅ branchResource caseCount <=
      (caseCount + 1) *
        (leafBound +
          3 * explicitDirectUniversalLocalPayloadEnvelope totalBound body)
  | 0, _, _ => by
      have hbase := baseAssemblyCost_le totalBound body
      simp only [explicitDirectUniversalBranchesStructuralEnvelope,
        valuationContext, Finset.image_empty]
      omega
  | index + 1, hcaseCount, hresource => by
      have hinitial :=
        directBranchesStructuralPayloadEnvelope_le_uniformPolynomial
          (valuation := valuation) (body := body)
          totalBound leafBound branchResource index (by omega) hresource
      have hstep := stepAssemblyCost_le totalBound index body hcaseCount
      have hleaf := hresource index
      let localEnvelope :=
        explicitDirectUniversalLocalPayloadEnvelope totalBound body
      have hpoly :
          (index + 1 + 1) * (leafBound + 3 * localEnvelope) =
            (index + 1) * (leafBound + 3 * localEnvelope) +
              (leafBound + 3 * localEnvelope) := by
        ring
      simp only [explicitDirectUniversalBranchesStructuralEnvelope]
      rw [hpoly]
      simp only [valuationContext, Finset.image_empty] at hstep ⊢
      dsimp only [localEnvelope] at hinitial hstep hleaf ⊢
      omega

theorem directBranchesStructuralPayloadEnvelope_le_polynomial
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {bound : Nat}
    (leafBound : Nat)
    (branchResource : Nat -> Nat)
    (hresource : ∀ index, branchResource index <= leafBound) :
    explicitDirectUniversalBranchesStructuralEnvelope
        valuation bound body ∅ branchResource bound <=
      explicitDirectUniversalBranchesPayloadPolynomial
        bound body leafBound := by
  simpa only [explicitDirectUniversalBranchesPayloadPolynomial] using
    directBranchesStructuralPayloadEnvelope_le_uniformPolynomial
      bound leafBound branchResource bound le_rfl hresource

#print axioms directBranchesStructuralPayloadEnvelope_le_uniformPolynomial
#print axioms directBranchesStructuralPayloadEnvelope_le_polynomial

end FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
