import integration.FoundationCompactPAContextualBoundedUniversalCompiler
import integration.FoundationCompactPAValuationContextRewriting

/-!
# Explicit direct branches for finite bounded universals

Every leaf is already a real certified context proof.  This module only moves
the valuation context into the corresponding finite-case context and records
the complete structural cost of the resulting branch spine.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactPAExplicitDirectUniversalBranches

open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches

noncomputable def buildExplicitDirectUniversalBranches
    {valuation : Nat -> Nat}
    {body : ArithmeticSemiformula Nat 1}
    (outerVariables : Finset Nat)
    (hbodyVariables : body.freeVariables ⊆ outerVariables) :
    (bound : Nat) ->
    (branch : ∀ index < bound,
      CertifiedPAContextProof
        (valuationContext (Rewriting.free body).freeVariables
          (extendValuation index valuation))
        (Rewriting.free body)) ->
    CertifiedContextFiniteUniversalBranches
      ((valuationContext outerVariables valuation).image Rewriting.shift)
      (Rewriting.free body) bound
  | 0, _ => .nil
  | bound + 1, branch =>
      let initial := buildExplicitDirectUniversalBranches
        outerVariables hbodyVariables bound
        (fun index hindex => branch index (by omega))
      let raw := branch bound (by omega)
      let last := CertifiedPAContextProof.weakenContext raw
        (freedFormulaValuationContext_subset_branch
          bound valuation body outerVariables hbodyVariables)
      .snoc initial last

def explicitDirectUniversalBranchesStructuralEnvelope
    (valuation : Nat -> Nat)
    (totalBound : Nat)
    (body : ArithmeticSemiformula Nat 1)
    (outerVariables : Finset Nat)
    (branchResource : Nat -> Nat) : Nat -> Nat
  | 0 =>
      CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost
          (Rewriting.free body) +
        weakeningFullAssemblyCost
          (insert (Rewriting.free body)
            (insert (∼(⊥ : ValuationFormula))
              (contextualFiniteBoundContext
                ((valuationContext outerVariables valuation).image
                  Rewriting.shift)
                totalBound)))
  | bound + 1 =>
      let Gamma :=
        (valuationContext outerVariables valuation).image Rewriting.shift
      let target := Rewriting.free body
      let caseFormula := finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 bound) (&0)
      explicitDirectUniversalBranchesStructuralEnvelope
          valuation totalBound body outerVariables branchResource bound +
        (branchResource bound +
          weakeningFullAssemblyCost
            (insert target (insert (∼caseFormula) Gamma))) +
        weakeningFullAssemblyCost
          (insert target
            (insert (∼caseFormula)
              (contextualFiniteBoundContext Gamma totalBound))) +
        CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
          (contextualFiniteBoundContext Gamma totalBound) target
          (finiteEqualityCases (&0) bound) caseFormula

theorem buildExplicitDirectUniversalBranches_structuralPayloadBound_le
    {valuation : Nat -> Nat}
    {body : ArithmeticSemiformula Nat 1}
    (outerVariables : Finset Nat)
    (hbodyVariables : body.freeVariables ⊆ outerVariables)
    (totalBound : Nat)
    (branchResource : Nat -> Nat) :
    (bound : Nat) ->
    (branch : ∀ index < bound,
      CertifiedPAContextProof
        (valuationContext (Rewriting.free body).freeVariables
          (extendValuation index valuation))
        (Rewriting.free body)) ->
    (hbranch : ∀ index (hindex : index < bound),
      (branch index hindex).payloadLength ≤ branchResource index) ->
    (buildExplicitDirectUniversalBranches outerVariables hbodyVariables
      bound branch).structuralPayloadBound totalBound ≤
      explicitDirectUniversalBranchesStructuralEnvelope
        valuation totalBound body outerVariables branchResource bound
  | 0, branch, hbranch => by
      simp only [buildExplicitDirectUniversalBranches,
        CertifiedContextFiniteUniversalBranches.structuralPayloadBound,
        explicitDirectUniversalBranchesStructuralEnvelope]
      exact Nat.le_refl _
  | bound + 1, branch, hbranch => by
      let initialBranch := fun index (hindex : index < bound) =>
        branch index (by omega)
      let initial := buildExplicitDirectUniversalBranches
        outerVariables hbodyVariables bound initialBranch
      let raw := branch bound (by omega)
      let hsubset := freedFormulaValuationContext_subset_branch
        bound valuation body outerVariables hbodyVariables
      let last := CertifiedPAContextProof.weakenContext raw hsubset
      have hinitial :=
        buildExplicitDirectUniversalBranches_structuralPayloadBound_le
          outerVariables hbodyVariables totalBound branchResource
          bound initialBranch (fun index hindex => hbranch index (by omega))
      have hraw : raw.payloadLength ≤ branchResource bound := by
        exact hbranch bound (by omega)
      have hweak := CertifiedPAContextProof.weakenContext_payloadLength_le
        raw hsubset
      have hlast : last.payloadLength ≤
          branchResource bound +
            weakeningFullAssemblyCost
              (insert (Rewriting.free body)
                (insert
                  (∼finiteCaseEqualityFormula
                    (iteratedSuccessorTerm 0 bound) (&0))
                  ((valuationContext outerVariables valuation).image
                    Rewriting.shift))) :=
        hweak.trans (Nat.add_le_add_right hraw _)
      simp only [buildExplicitDirectUniversalBranches,
        CertifiedContextFiniteUniversalBranches.structuralPayloadBound,
        explicitDirectUniversalBranchesStructuralEnvelope]
      change initial.structuralPayloadBound totalBound +
          (last.payloadLength + _) + _ ≤ _
      dsimp only [initial, last, initialBranch] at hinitial hlast ⊢
      omega

#print axioms buildExplicitDirectUniversalBranches
#print axioms explicitDirectUniversalBranchesStructuralEnvelope
#print axioms buildExplicitDirectUniversalBranches_structuralPayloadBound_le

end FoundationCompactPAExplicitDirectUniversalBranches
