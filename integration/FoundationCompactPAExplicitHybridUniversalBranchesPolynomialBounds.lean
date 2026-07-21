import integration.FoundationCompactPAExplicitHybridUniversalBranches
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
import integration.FoundationCompactPABoundedUniversalPolynomialBounds

/-!
# Polynomial assembly bounds for explicit hybrid universal branches

This file separates the repeated finite-case assembly cost from the resources
of the concrete branch certificates.  The formula envelope depends only on the
numeric branch bound and the actual code length of the universal body.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedCertifiedVerifier
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds

def explicitHybridUniversalSyntaxResource
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  bound + (binaryFormulaCode body).length

def explicitHybridUniversalFormulaEnvelope
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  boundedUniversalClosedFormulaEnvelope
      (explicitHybridUniversalSyntaxResource bound body) +
    2 * (binaryFormulaCode body).length

def explicitHybridUniversalLocalPayloadEnvelope
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  smallContextAssemblyEnvelope
    (explicitHybridUniversalFormulaEnvelope bound body)

def explicitHybridUniversalBranchesPayloadPolynomial
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (leafBound : Nat) : Nat :=
  (bound + 1) *
    (leafBound +
      3 * explicitHybridUniversalLocalPayloadEnvelope bound body)

def HybridBranchesLeafPayloadBound
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (leafBound : Nat) :
    {bound : Nat} ->
      CheckedHybridValuationUniversalBranches valuation body bound -> Prop
  | 0, .nil _ _ => True
  | _ + 1, .snoc initial last =>
      HybridBranchesLeafPayloadBound leafBound initial ∧
        hybridFormulaStructuralPayloadBound last <= leafBound

theorem buildExplicitHybridUniversalBranches_leafPayloadBound
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (leafBound bound : Nat)
    (branch : ∀ index, index < bound ->
      CheckedHybridValuationBoundedFormulaCertificate
        (extendValuation index valuation) (Rewriting.free body))
    (hleaf : ∀ index hindex,
      hybridFormulaStructuralPayloadBound (branch index hindex) <=
        leafBound) :
    HybridBranchesLeafPayloadBound leafBound
      (buildExplicitHybridUniversalBranches bound branch) := by
  induction bound with
  | zero =>
      simp [buildExplicitHybridUniversalBranches,
        HybridBranchesLeafPayloadBound]
  | succ previous inductionHypothesis =>
      simp only [buildExplicitHybridUniversalBranches,
        HybridBranchesLeafPayloadBound]
      constructor
      · exact inductionHypothesis
          (fun index hindex =>
            branch index
              (Nat.lt_trans hindex (Nat.lt_succ_self previous)))
          (fun index hindex => hleaf index
            (Nat.lt_trans hindex (Nat.lt_succ_self previous)))
      · exact hleaf previous (Nat.lt_succ_self previous)

private theorem target_code_le_formulaEnvelope
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    (binaryFormulaCode (Rewriting.free body)).length <=
      explicitHybridUniversalFormulaEnvelope bound body := by
  have hfree := binaryFormulaCode_free_length_le body
  unfold explicitHybridUniversalFormulaEnvelope
  omega

private theorem finiteContext_formulaCodeBound
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    FormulaCodeBound
      (contextualFiniteBoundContext
        (∅ : Finset LO.FirstOrder.ArithmeticProposition) bound)
      (explicitHybridUniversalFormulaEnvelope bound body) := by
  let resource := explicitHybridUniversalSyntaxResource bound body
  have hbound : bound <= resource := by
    dsimp only [resource]
    unfold explicitHybridUniversalSyntaxResource
    omega
  have hbase :=
    finiteBoundContext_formulaCodeBound_boundedUniversal
      bound resource hbound
  have henvelope :
      boundedUniversalClosedFormulaEnvelope resource <=
        explicitHybridUniversalFormulaEnvelope bound body := by
    dsimp only [resource]
    unfold explicitHybridUniversalFormulaEnvelope
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
                (∅ : Finset LO.FirstOrder.ArithmeticProposition) bound))) <=
      2 * explicitHybridUniversalLocalPayloadEnvelope bound body := by
  let formulaEnvelope := explicitHybridUniversalFormulaEnvelope bound body
  have htarget :
      (binaryFormulaCode (Rewriting.free body)).length <= formulaEnvelope := by
    exact target_code_le_formulaEnvelope bound body
  have hfalseBase :=
    negatedFalse_code_le_boundedUniversal
      (explicitHybridUniversalSyntaxResource bound body)
  have hfalse :
      (binaryFormulaCode
        (∼(⊥ : LO.FirstOrder.ArithmeticProposition))).length <=
          formulaEnvelope := by
    exact hfalseBase.trans (by
      dsimp only [formulaEnvelope]
      unfold explicitHybridUniversalFormulaEnvelope
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
  unfold explicitHybridUniversalLocalPayloadEnvelope
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
      3 * explicitHybridUniversalLocalPayloadEnvelope totalBound body := by
  let resource := explicitHybridUniversalSyntaxResource totalBound body
  let formulaEnvelope :=
    explicitHybridUniversalFormulaEnvelope totalBound body
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition := ∅
  let target := Rewriting.free body
  let caseFormula := finiteCaseEqualityFormula
    (iteratedSuccessorTerm 0 index) (&0)
  have hresource : totalBound <= resource := by
    dsimp only [resource]
    unfold explicitHybridUniversalSyntaxResource
    omega
  have henvelope :
      boundedUniversalClosedFormulaEnvelope resource <= formulaEnvelope := by
    dsimp only [resource, formulaEnvelope]
    unfold explicitHybridUniversalFormulaEnvelope
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
  unfold explicitHybridUniversalLocalPayloadEnvelope
  simp only [valuationContext, Finset.image_empty]
  dsimp only [Gamma, target, caseFormula, formulaEnvelope] at hweakOne hweakTwo heliminate ⊢
  omega

theorem hybridBranchesStructuralPayloadEnvelope_le_uniformPolynomial
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (totalBound leafBound : Nat) :
    {caseCount : Nat} ->
    (branches :
      CheckedHybridValuationUniversalBranches valuation body caseCount) ->
    caseCount <= totalBound ->
    HybridBranchesLeafPayloadBound leafBound branches ->
    hybridBranchesStructuralPayloadEnvelope
          totalBound (∅ : Finset Nat) branches <=
        (caseCount + 1) *
          (leafBound +
            3 * explicitHybridUniversalLocalPayloadEnvelope totalBound body)
  | 0, .nil _ _, _, _ => by
      have hbase := baseAssemblyCost_le totalBound body
      simp only [hybridBranchesStructuralPayloadEnvelope,
        valuationContext, Finset.image_empty]
      omega
  | index + 1, .snoc initial last, hcaseCount, hleaves => by
      have hparts : HybridBranchesLeafPayloadBound leafBound initial ∧
          hybridFormulaStructuralPayloadBound last <= leafBound := by
        simpa only [HybridBranchesLeafPayloadBound] using hleaves
      have hinitial :=
        hybridBranchesStructuralPayloadEnvelope_le_uniformPolynomial
          totalBound leafBound initial (by omega) hparts.1
      have hstep := stepAssemblyCost_le totalBound index body hcaseCount
      let localEnvelope :=
        explicitHybridUniversalLocalPayloadEnvelope totalBound body
      have hpoly :
          (index + 1 + 1) * (leafBound + 3 * localEnvelope) =
            (index + 1) * (leafBound + 3 * localEnvelope) +
              (leafBound + 3 * localEnvelope) := by
        ring
      simp only [hybridBranchesStructuralPayloadEnvelope]
      rw [hpoly]
      simp only [valuationContext, Finset.image_empty] at hstep ⊢
      dsimp only [localEnvelope] at hinitial hstep ⊢
      omega

theorem hybridBranchesStructuralPayloadEnvelope_le_polynomial
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {bound : Nat}
    (leafBound : Nat)
    (branches :
      CheckedHybridValuationUniversalBranches valuation body bound)
    (hleaves : HybridBranchesLeafPayloadBound leafBound branches) :
    hybridBranchesStructuralPayloadEnvelope
        bound (∅ : Finset Nat) branches <=
      explicitHybridUniversalBranchesPayloadPolynomial
        bound body leafBound := by
  simpa only [explicitHybridUniversalBranchesPayloadPolynomial] using
    hybridBranchesStructuralPayloadEnvelope_le_uniformPolynomial
      bound leafBound branches le_rfl hleaves

#print axioms
  buildExplicitHybridUniversalBranches_leafPayloadBound
#print axioms
  hybridBranchesStructuralPayloadEnvelope_le_uniformPolynomial
#print axioms hybridBranchesStructuralPayloadEnvelope_le_polynomial

end FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
