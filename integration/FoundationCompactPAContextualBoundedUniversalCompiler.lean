import integration.FoundationCompactCertifiedContextUniversalIntroduction
import integration.FoundationCompactCertifiedContextDischarge
import integration.FoundationCompactPABoundedUniversalCompilerBounds

/-!
# Contextual finite bounded-universal compiler

This is the nested-quantifier counterpart of the closed finite-exhaustion
compiler.  Every branch is a real certified PA proof under:

* the shifted outer valuation context; and
* the equality identifying the fresh eigenvariable with that branch numeral.

The compiler combines all branches, handles the impossible lower-bound case,
cuts the genuine finite-exhaustion theorem, discharges the finite bound, and
universally introduces the eigenvariable while retaining the outer context.
No proof-existence field or proof-length premise is used.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAContextualBoundedUniversalCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalCompiler.CheckedFiniteBoundedUniversalCertificate
open FoundationCompactPABoundedUniversalCompilerBounds
open FoundationCompactCertifiedContextDischarge
open FoundationCompactCertifiedContextUniversalIntroduction

def contextualFiniteBoundContext
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat) : Finset LO.FirstOrder.ArithmeticProposition :=
  insert (∼finiteBoundFormula bound) Gamma

/-- Certified case proofs for values `0, ..., bound - 1`.  The target may
contain the fresh eigenvariable `&0` and any shifted outer variables. -/
inductive CertifiedContextFiniteUniversalBranches
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (target : LO.FirstOrder.ArithmeticProposition) : Nat → Type
  | nil : CertifiedContextFiniteUniversalBranches Gamma target 0
  | snoc {bound : Nat}
      (initial : CertifiedContextFiniteUniversalBranches Gamma target bound)
      (last : CertifiedPAContextProof
        (insert
          (∼finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 bound) (&0)) Gamma)
        target) :
      CertifiedContextFiniteUniversalBranches Gamma target (bound + 1)

namespace CertifiedContextFiniteUniversalBranches

def structuralPayloadBound
    (totalBound : Nat)
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target : LO.FirstOrder.ArithmeticProposition} :
    {caseCount : Nat} →
      CertifiedContextFiniteUniversalBranches Gamma target caseCount → Nat
  | 0, .nil =>
      CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost target +
        weakeningFullAssemblyCost
          (insert target
            (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
              (contextualFiniteBoundContext Gamma totalBound)))
  | bound + 1, .snoc initial last =>
      structuralPayloadBound totalBound initial +
        (last.payloadLength +
          weakeningFullAssemblyCost
            (insert target
              (insert
                (∼finiteCaseEqualityFormula
                  (iteratedSuccessorTerm 0 bound) (&0))
                (contextualFiniteBoundContext Gamma totalBound)))) +
        CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
          (contextualFiniteBoundContext Gamma totalBound) target
          (finiteEqualityCases (&0) bound)
          (finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 bound) (&0))

noncomputable def compileCasesUnderBoundAssumption
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target : LO.FirstOrder.ArithmeticProposition}
    (totalBound : Nat) :
    {caseCount : Nat} →
      CertifiedContextFiniteUniversalBranches Gamma target caseCount →
      CertifiedPAContextProof
        (insert (∼finiteEqualityCases (&0) caseCount)
          (contextualFiniteBoundContext Gamma totalBound)) target
  | 0, .nil => by
      let base := CertifiedPAContextProof.exFalsoAssumption target
      exact CertifiedPAContextProof.weakenContext base (by
        intro formula hformula
        simp only [Finset.mem_singleton] at hformula
        subst formula
        simp [contextualFiniteBoundContext])
  | bound + 1, .snoc initial last => by
      let leftBranch :=
        compileCasesUnderBoundAssumption totalBound initial
      let rightBranch : CertifiedPAContextProof
          (insert
            (∼finiteCaseEqualityFormula
              (iteratedSuccessorTerm 0 bound) (&0))
            (contextualFiniteBoundContext Gamma totalBound)) target :=
        CertifiedPAContextProof.weakenContext last (by
          intro formula hformula
          simp only [Finset.mem_insert] at hformula ⊢
          rcases hformula with hformula | hformula
          · exact Or.inl hformula
          · exact Or.inr (by
              simp [contextualFiniteBoundContext, hformula]))
      exact CertifiedPAContextProof.eliminateDisjunctionAssumption
        leftBranch rightBranch

theorem compileCasesUnderBoundAssumption_payloadLength_le_structural
    (totalBound : Nat)
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target : LO.FirstOrder.ArithmeticProposition}
    {caseCount : Nat}
    (branches : CertifiedContextFiniteUniversalBranches
      Gamma target caseCount) :
    (branches.compileCasesUnderBoundAssumption totalBound).payloadLength ≤
      branches.structuralPayloadBound totalBound := by
  induction branches with
  | nil =>
      let base := CertifiedPAContextProof.exFalsoAssumption target
      have hbaseSubset :
          ({∼(⊥ : LO.FirstOrder.ArithmeticProposition)} :
            Finset LO.FirstOrder.ArithmeticProposition) ⊆
          insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
            (contextualFiniteBoundContext Gamma totalBound) := by
        intro formula hformula
        simp only [Finset.mem_singleton] at hformula
        subst formula
        exact Finset.mem_insert_self _ _
      let weakened : CertifiedPAContextProof
          (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
            (contextualFiniteBoundContext Gamma totalBound)) target :=
        CertifiedPAContextProof.weakenContext base hbaseSubset
      have hbase :=
        CertifiedPAContextProof.exFalsoAssumption_payloadLength_eq target
      have hweaken :=
        CertifiedPAContextProof.weakenContext_payloadLength_le
          base hbaseSubset
      have hresult : weakened.payloadLength ≤
          structuralPayloadBound totalBound
            (CertifiedContextFiniteUniversalBranches.nil :
              CertifiedContextFiniteUniversalBranches Gamma target 0) := by
        simp only [structuralPayloadBound]
        exact hweaken.trans (by rw [hbase])
      exact hresult
  | @snoc bound initial last ih =>
      let leftBranch :=
        compileCasesUnderBoundAssumption totalBound initial
      have hrightSubset :
          insert
              (∼finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 bound) (&0)) Gamma ⊆
            insert
              (∼finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 bound) (&0))
              (contextualFiniteBoundContext Gamma totalBound) := by
        intro formula hformula
        simp only [Finset.mem_insert] at hformula ⊢
        rcases hformula with hformula | hformula
        · exact Or.inl hformula
        · exact Or.inr (by
            simp [contextualFiniteBoundContext, hformula])
      let rightBranch : CertifiedPAContextProof
          (insert
            (∼finiteCaseEqualityFormula
              (iteratedSuccessorTerm 0 bound) (&0))
            (contextualFiniteBoundContext Gamma totalBound)) target :=
        CertifiedPAContextProof.weakenContext last hrightSubset
      let combined :=
        CertifiedPAContextProof.eliminateDisjunctionAssumption
          leftBranch rightBranch
      have hright := CertifiedPAContextProof.weakenContext_payloadLength_le
        last hrightSubset
      have hcombined :=
        CertifiedPAContextProof.eliminateDisjunctionAssumption_payloadLength_le
          leftBranch rightBranch
      change combined.payloadLength ≤ _ at hcombined
      change combined.payloadLength ≤
        structuralPayloadBound totalBound
          (CertifiedContextFiniteUniversalBranches.snoc initial last)
      simp only [structuralPayloadBound]
      exact hcombined.trans
        (Nat.add_le_add_right
          (Nat.add_le_add ih hright) _)

noncomputable def compileUnderBoundAssumption
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target : LO.FirstOrder.ArithmeticProposition}
    {bound : Nat}
    (branches : CertifiedContextFiniteUniversalBranches
      Gamma target bound) :
    CertifiedPAContextProof
      (contextualFiniteBoundContext Gamma bound) target := by
  let caseBranch := branches.compileCasesUnderBoundAssumption bound
  let lowerRaw := lowerBoundContradiction bound target
  let lowerBranch : CertifiedPAContextProof
      (insert (∼finiteLowerBoundFormula bound (&0))
        (contextualFiniteBoundContext Gamma bound)) target :=
    CertifiedPAContextProof.weakenContext lowerRaw (by
      intro formula hformula
      simp only [Finset.mem_insert] at hformula ⊢
      rcases hformula with hformula | hformula
      · exact Or.inl hformula
      · exact Or.inr (by
          simp [contextualFiniteBoundContext, finiteBoundContext]
            at hformula ⊢
          exact Or.inl hformula))
  let underExhaustion :=
    CertifiedPAContextProof.eliminateDisjunctionAssumption
      caseBranch lowerBranch
  exact cutClosedAssumption
    (proveFiniteExhaustionAtEigenvariable bound) underExhaustion

def lowerBranchStructuralPayloadBound
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat)
    (target : LO.FirstOrder.ArithmeticProposition) : Nat :=
  lowerBoundContradictionFullPayloadCost bound target +
    weakeningFullAssemblyCost
      (insert target
        (insert (∼finiteLowerBoundFormula bound (&0))
          (contextualFiniteBoundContext Gamma bound)))

def underExhaustionStructuralPayloadBound
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target : LO.FirstOrder.ArithmeticProposition}
    {bound : Nat}
    (branches : CertifiedContextFiniteUniversalBranches
      Gamma target bound) : Nat :=
  branches.structuralPayloadBound bound +
    lowerBranchStructuralPayloadBound Gamma bound target +
    CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
      (contextualFiniteBoundContext Gamma bound) target
      (finiteEqualityCases (&0) bound)
      (finiteLowerBoundFormula bound (&0))

def compileUnderBoundAssumptionStructuralPayloadBound
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target : LO.FirstOrder.ArithmeticProposition}
    {bound : Nat}
    (branches : CertifiedContextFiniteUniversalBranches
      Gamma target bound) : Nat :=
  finiteExhaustionAtEigenvariableStructuralPayloadBound bound +
    underExhaustionStructuralPayloadBound branches +
    cutClosedAssumptionFullAssemblyCost
      (contextualFiniteBoundContext Gamma bound)
      (finiteExhaustionFormula bound (&0)) target

theorem compileUnderBoundAssumption_payloadLength_le_structural
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {target : LO.FirstOrder.ArithmeticProposition}
    {bound : Nat}
    (branches : CertifiedContextFiniteUniversalBranches
      Gamma target bound) :
    branches.compileUnderBoundAssumption.payloadLength ≤
      branches.compileUnderBoundAssumptionStructuralPayloadBound := by
  let caseBranch := branches.compileCasesUnderBoundAssumption bound
  let lowerRaw := lowerBoundContradiction bound target
  have hlowerSubset :
      insert (∼finiteLowerBoundFormula bound (&0))
          (finiteBoundContext bound) ⊆
        insert (∼finiteLowerBoundFormula bound (&0))
          (contextualFiniteBoundContext Gamma bound) := by
    intro formula hformula
    simp only [Finset.mem_insert] at hformula ⊢
    rcases hformula with hformula | hformula
    · exact Or.inl hformula
    · exact Or.inr (by
        simp [contextualFiniteBoundContext, finiteBoundContext]
          at hformula ⊢
        exact Or.inl hformula)
  let lowerBranch : CertifiedPAContextProof
      (insert (∼finiteLowerBoundFormula bound (&0))
        (contextualFiniteBoundContext Gamma bound)) target :=
    CertifiedPAContextProof.weakenContext lowerRaw hlowerSubset
  let underExhaustion :=
    CertifiedPAContextProof.eliminateDisjunctionAssumption
      caseBranch lowerBranch
  let exhaustionProof := proveFiniteExhaustionAtEigenvariable bound
  have hcases :=
    compileCasesUnderBoundAssumption_payloadLength_le_structural
      bound branches
  have hlowerRaw := lowerBoundContradiction_payloadLength_eq bound target
  have hlowerWeakening :=
    CertifiedPAContextProof.weakenContext_payloadLength_le
      lowerRaw hlowerSubset
  have hlower : lowerBranch.payloadLength ≤
      lowerBranchStructuralPayloadBound Gamma bound target := by
    change lowerBranch.payloadLength ≤ _ at hlowerWeakening
    unfold lowerBranchStructuralPayloadBound
    exact hlowerWeakening.trans (by
      rw [hlowerRaw])
  have hunderConstructor :=
    CertifiedPAContextProof.eliminateDisjunctionAssumption_payloadLength_le
      caseBranch lowerBranch
  have hunder : underExhaustion.payloadLength ≤
      underExhaustionStructuralPayloadBound branches := by
    change underExhaustion.payloadLength ≤ _ at hunderConstructor
    unfold underExhaustionStructuralPayloadBound
    exact hunderConstructor.trans
      (Nat.add_le_add_right
        (Nat.add_le_add hcases hlower) _)
  have hexhaustion :=
    proveFiniteExhaustionAtEigenvariable_payloadLength_le_structural bound
  have hexhaustionProof : exhaustionProof.payloadLength ≤
      finiteExhaustionAtEigenvariableStructuralPayloadBound bound := by
    simpa only [exhaustionProof] using hexhaustion
  have hcut := cutClosedAssumption_payloadLength_le
    exhaustionProof underExhaustion
  change branches.compileUnderBoundAssumption.payloadLength ≤ _ at hcut
  unfold compileUnderBoundAssumptionStructuralPayloadBound
  exact hcut.trans
    (Nat.add_le_add_right
      (Nat.add_le_add hexhaustionProof hunder) _)

end CertifiedContextFiniteUniversalBranches

theorem iteratedSuccessorTerm_free
    (value : Nat) :
    Rew.free (iteratedSuccessorTerm 1 value) =
      iteratedSuccessorTerm 0 value := by
  induction value with
  | zero =>
      simp [iteratedSuccessorTerm, finiteCaseZeroTerm, Rew.func]
  | succ value ih =>
      simp [iteratedSuccessorTerm_succ, finiteCaseAddTerm,
        finiteCaseOneTerm, Rew.func, ih]

theorem finiteBoundFormula_free
    (bound : Nat) :
    Rewriting.free
        (finiteCaseLessThanFormula (#0)
          (iteratedSuccessorTerm 1 bound)) =
      finiteBoundFormula bound := by
  unfold finiteBoundFormula finiteCaseLessThanFormula
  simp only [Semiformula.rew_rel]
  rw [Matrix.fun_eq_vec_two (fun index ↦
    Rew.free
      (![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
        iteratedSuccessorTerm 1 bound] index))]
  simp [iteratedSuccessorTerm_free]

theorem finiteBoundedUniversalBody_free_contextual
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    Rewriting.free (finiteBoundedUniversalBody bound body) =
      contextualImplicationFormula
        (finiteBoundFormula bound) (Rewriting.free body) := by
  unfold finiteBoundedUniversalBody contextualImplicationFormula
  rw [LogicalConnective.HomClass.map_imply]
  rw [finiteBoundFormula_free]

/-- Compile a canonical numeral-bounded universal while preserving an
arbitrary outer context.  Nested callers use `Gamma.image Rewriting.shift`
for the branch context and `Rewriting.free body` for the branch target. -/
noncomputable def compileContextualBoundedUniversal
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (branches : CertifiedContextFiniteUniversalBranches
      (Gamma.image Rewriting.shift) (Rewriting.free body) bound) :
    CertifiedPAContextProof Gamma
      (∀⁰ finiteBoundedUniversalBody bound body) := by
  let underBound := branches.compileUnderBoundAssumption
  let implicationProof := contextualDischarge
    (finiteBoundFormula bound) (Rewriting.free body) underBound
  let freeBodyProof : CertifiedPAContextProof
      (Gamma.image Rewriting.shift)
      (Rewriting.free (finiteBoundedUniversalBody bound body)) :=
    CertifiedPAContextProof.cast
      (finiteBoundedUniversalBody_free_contextual bound body).symm
      implicationProof
  exact contextualUniversalIntroduction
    (finiteBoundedUniversalBody bound body) freeBodyProof

def compileContextualBoundedUniversalStructuralPayloadBound
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (branches : CertifiedContextFiniteUniversalBranches
      (Gamma.image Rewriting.shift) (Rewriting.free body) bound) : Nat :=
  branches.compileUnderBoundAssumptionStructuralPayloadBound +
    contextualDischargeFullAssemblyCost
      (Gamma.image Rewriting.shift)
      (finiteBoundFormula bound) (Rewriting.free body) +
    contextualUniversalIntroductionFullAssemblyCost Gamma
      (finiteBoundedUniversalBody bound body)

theorem compileContextualBoundedUniversal_payloadLength_le_structural
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (branches : CertifiedContextFiniteUniversalBranches
      (Gamma.image Rewriting.shift) (Rewriting.free body) bound) :
    (compileContextualBoundedUniversal bound body branches).payloadLength ≤
      compileContextualBoundedUniversalStructuralPayloadBound
        bound body branches := by
  let underBound := branches.compileUnderBoundAssumption
  let implicationProof := contextualDischarge
    (finiteBoundFormula bound) (Rewriting.free body) underBound
  let freeBodyProof : CertifiedPAContextProof
      (Gamma.image Rewriting.shift)
      (Rewriting.free (finiteBoundedUniversalBody bound body)) :=
    CertifiedPAContextProof.cast
      (finiteBoundedUniversalBody_free_contextual bound body).symm
      implicationProof
  have hunder :=
    CertifiedContextFiniteUniversalBranches.compileUnderBoundAssumption_payloadLength_le_structural
      branches
  have hdischarge := contextualDischarge_payloadLength_le
    (finiteBoundFormula bound) (Rewriting.free body) underBound
  have himplication : implicationProof.payloadLength ≤
      branches.compileUnderBoundAssumptionStructuralPayloadBound +
        contextualDischargeFullAssemblyCost
          (Gamma.image Rewriting.shift)
          (finiteBoundFormula bound) (Rewriting.free body) := by
    change implicationProof.payloadLength ≤ _ at hdischarge
    exact hdischarge.trans (Nat.add_le_add_right hunder _)
  have hfreeBody : freeBodyProof.payloadLength =
      implicationProof.payloadLength := by
    dsimp only [freeBodyProof]
    exact CertifiedPAContextProof.cast_payloadLength _ _
  have hall := contextualUniversalIntroduction_payloadLength_le
    (finiteBoundedUniversalBody bound body) freeBodyProof
  change (compileContextualBoundedUniversal
      bound body branches).payloadLength ≤ _
  change (contextualUniversalIntroduction
      (finiteBoundedUniversalBody bound body) freeBodyProof).payloadLength ≤ _
  unfold compileContextualBoundedUniversalStructuralPayloadBound
  exact hall.trans (by
    rw [hfreeBody]
    exact Nat.add_le_add_right himplication _)

theorem compileContextualBoundedUniversal_certificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (branches : CertifiedContextFiniteUniversalBranches
      (Gamma.image Rewriting.shift) (Rewriting.free body) bound) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (compileContextualBoundedUniversal
          bound body branches).derivation)
      (compileContextualBoundedUniversal
        bound body branches).certificate :=
  (compileContextualBoundedUniversal
    bound body branches).certificate_valid

#print axioms iteratedSuccessorTerm_free
#print axioms finiteBoundedUniversalBody_free_contextual
#print axioms CertifiedContextFiniteUniversalBranches.compileCasesUnderBoundAssumption_payloadLength_le_structural
#print axioms CertifiedContextFiniteUniversalBranches.compileUnderBoundAssumption_payloadLength_le_structural
#print axioms compileContextualBoundedUniversal_payloadLength_le_structural
#print axioms compileContextualBoundedUniversal_certificate_valid

end FoundationCompactPAContextualBoundedUniversalCompiler
