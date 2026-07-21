import integration.FoundationCompactPAFiniteExhaustionInduction
import integration.FoundationCompactPAUnaryBoundedFormulaTransport

/-!
# Proof-producing compiler for finite bounded universals

For a fixed bound `B`, a certificate contains one proof-free replacement
certificate for every value `0, ..., B - 1`.  Compilation proves the genuine
PA exhaustion theorem, splits its finite disjunction, transports every checked
branch along `i = x`, discharges `x < B`, and universally introduces `x`.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABoundedUniversalCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAFiniteExhaustionInduction
open FoundationCompactPAUnaryTermEqualityImplication
open FoundationCompactPAUnaryBoundedFormulaTransport
open FoundationCompactCertifiedUniversalIntroduction

def finiteBoundFormula (bound : Nat) :
    LO.FirstOrder.ArithmeticProposition :=
  finiteCaseLessThanFormula (&0)
    (iteratedSuccessorTerm 0 bound)

def finiteBoundContext (bound : Nat) :
    Finset LO.FirstOrder.ArithmeticProposition :=
  {∼finiteBoundFormula bound}

inductive CheckedFiniteUniversalBranches
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat → Type
  | nil : CheckedFiniteUniversalBranches body 0
  | snoc {bound : Nat}
      (initial : CheckedFiniteUniversalBranches body bound)
      (last : CheckedUnaryReplacementCertificate
        (iteratedSuccessorTerm 0 bound) (&0) (body/[&0])) :
      CheckedFiniteUniversalBranches body (bound + 1)

namespace CheckedFiniteUniversalBranches

def equalityContext_eq_finiteCaseContext
    (index : Nat) :
    parameterEqualityContext (iteratedSuccessorTerm 0 index) (&0) =
      ({∼finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 index) (&0)} :
        Finset LO.FirstOrder.ArithmeticProposition) := by
  unfold parameterEqualityContext parameterEqualityFormula
  rw [finiteCaseEqualityFormula_eq_operator]

noncomputable def compileCasesUnderBoundAssumption
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (totalBound : Nat) :
    {caseCount : Nat} →
    CheckedFiniteUniversalBranches body caseCount →
    CertifiedPAContextProof
      (insert (∼finiteEqualityCases (&0) caseCount)
        (finiteBoundContext totalBound))
      (body/[&0])
  | 0, .nil => by
      let base := CertifiedPAContextProof.exFalsoAssumption (body/[&0])
      let weakened : CertifiedPAContextProof
          (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
            (finiteBoundContext totalBound)) (body/[&0]) :=
        CertifiedPAContextProof.weakenContext base (by
          intro formula hformula
          simp only [Finset.mem_singleton] at hformula
          subst formula
          exact Finset.mem_insert_self
            (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
            (finiteBoundContext totalBound))
      exact weakened
  | bound + 1, .snoc initial last => by
      let leftBranch := compileCasesUnderBoundAssumption totalBound initial
      let rightRaw := last.compileUnderAssumption
      let rightSingleton := CertifiedPAContextProof.castContext
        (equalityContext_eq_finiteCaseContext bound) rightRaw
      let rightBranch : CertifiedPAContextProof
          (insert
            (∼finiteCaseEqualityFormula
              (iteratedSuccessorTerm 0 bound) (&0))
            (finiteBoundContext totalBound)) (body/[&0]) :=
        CertifiedPAContextProof.weakenContext rightSingleton (by
          intro formula hformula
          simp only [Finset.mem_singleton] at hformula
          subst formula
          exact Finset.mem_insert_self
            (∼finiteCaseEqualityFormula
              (iteratedSuccessorTerm 0 bound) (&0))
            (finiteBoundContext totalBound))
      let combined := CertifiedPAContextProof.eliminateDisjunctionAssumption
        (Gamma := finiteBoundContext totalBound)
        (target := body/[&0])
        (left := finiteEqualityCases (&0) bound)
        (right := finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 bound) (&0))
        leftBranch rightBranch
      exact combined

end CheckedFiniteUniversalBranches

def lowerBoundContradiction
    (bound : Nat)
    (target : LO.FirstOrder.ArithmeticProposition) :
    CertifiedPAContextProof
      (insert
        (∼finiteLowerBoundFormula bound (&0))
        (finiteBoundContext bound)) target where
  derivation := LO.FirstOrder.Derivation2.closed _
    (finiteBoundFormula bound)
    (by
      simp [finiteBoundFormula, finiteBoundContext,
        finiteLowerBoundFormula])
    (by
      simp [finiteBoundFormula, finiteBoundContext,
        finiteLowerBoundFormula])
  certificate := .leaf
  certificate_valid := by
    simp [CheckedPAProofTree.ofDerivation, certificateValid,
      finiteBoundFormula, finiteBoundContext, finiteLowerBoundFormula]

def cutClosedAssumptionDerivation
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {caseFormula target : LO.FirstOrder.ArithmeticProposition}
    (caseProof : LO.FirstOrder.Derivation2 PA {caseFormula})
    (targetProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼caseFormula) Gamma))) :
    LO.FirstOrder.Derivation2 PA (insert target Gamma) :=
  LO.FirstOrder.Derivation2.cut (φ := caseFormula)
    (LO.FirstOrder.Derivation2.wk caseProof (by
      intro formula hformula
      simp only [Finset.mem_singleton] at hformula
      subst formula
      exact Finset.mem_insert_self caseFormula (insert target Gamma)))
    (LO.FirstOrder.Derivation2.wk targetProof (by
      intro formula hformula
      simp only [Finset.mem_insert] at hformula ⊢
      rcases hformula with hformula | hformula
      · exact Or.inr (Or.inl hformula)
      · rcases hformula with hformula | hformula
        · exact Or.inl hformula
        · exact Or.inr (Or.inr hformula)))

def cutClosedAssumptionCertificate
    (caseCertificate targetCertificate : StructuralValidityCertificate) :
    StructuralValidityCertificate :=
  .binary (.unary caseCertificate) (.unary targetCertificate)

theorem cutClosedAssumptionCertificate_valid
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {caseFormula target : LO.FirstOrder.ArithmeticProposition}
    (caseProof : LO.FirstOrder.Derivation2 PA {caseFormula})
    (targetProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼caseFormula) Gamma)))
    (caseCertificate targetCertificate : StructuralValidityCertificate)
    (hcase : certificateValid
      (CheckedPAProofTree.ofDerivation caseProof) caseCertificate)
    (htarget : certificateValid
      (CheckedPAProofTree.ofDerivation targetProof) targetCertificate) :
    certificateValid
      (CheckedPAProofTree.ofDerivation
        (cutClosedAssumptionDerivation caseProof targetProof))
      (cutClosedAssumptionCertificate caseCertificate targetCertificate) := by
  have hcaseConclusion :=
    CheckedPAProofTree.conclusion_ofDerivation caseProof
  have htargetConclusion :=
    CheckedPAProofTree.conclusion_ofDerivation targetProof
  have hcaseSubset :
      (CheckedPAProofTree.ofDerivation caseProof).conclusion ⊆
        insert caseFormula (insert target Gamma) := by
    rw [hcaseConclusion]
    simp
  have htargetSubset :
      (CheckedPAProofTree.ofDerivation targetProof).conclusion ⊆
        insert (∼caseFormula) (insert target Gamma) := by
    rw [htargetConclusion]
    intro formula hformula
    simp only [Finset.mem_insert] at hformula ⊢
    rcases hformula with hformula | hformula
    · exact Or.inr (Or.inl hformula)
    · rcases hformula with hformula | hformula
      · exact Or.inl hformula
      · exact Or.inr (Or.inr hformula)
  simp [cutClosedAssumptionDerivation,
    cutClosedAssumptionCertificate, CheckedPAProofTree.ofDerivation,
    CheckedPAProofTree.conclusion, certificateValid, hcase, htarget]
  exact ⟨hcaseSubset, htargetSubset⟩

def cutClosedAssumption
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {caseFormula target : LO.FirstOrder.ArithmeticProposition}
    (caseProof : CertifiedPAProof caseFormula)
    (targetProof : CertifiedPAContextProof
      (insert (∼caseFormula) Gamma) target) :
    CertifiedPAContextProof Gamma target where
  derivation := cutClosedAssumptionDerivation
    caseProof.derivation targetProof.derivation
  certificate := cutClosedAssumptionCertificate
    caseProof.certificate targetProof.certificate
  certificate_valid := cutClosedAssumptionCertificate_valid
    caseProof.derivation targetProof.derivation
    caseProof.certificate targetProof.certificate
    caseProof.certificate_valid targetProof.certificate_valid

def proveFiniteExhaustionAtEigenvariable
    (bound : Nat) :
    CertifiedPAProof (finiteExhaustionFormula bound (&0)) :=
  CertifiedPAProof.cast
    (finiteExhaustionBody_substitution bound (&0))
    (CertifiedPAProof.specialize (proveFiniteExhaustion bound) (&0))

structure CheckedFiniteBoundedUniversalCertificate
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) where
  body_freeVariables_eq_empty : body.freeVariables = ∅
  branches : CheckedFiniteUniversalBranches body bound

namespace CheckedFiniteBoundedUniversalCertificate

def compileUnderBoundAssumption
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    CertifiedPAContextProof (finiteBoundContext bound) (body/[&0]) := by
  let casesBranch :=
    certificate.branches.compileCasesUnderBoundAssumption bound
  let lowerBranch := lowerBoundContradiction bound (body/[&0])
  let underExhaustion :=
    CertifiedPAContextProof.eliminateDisjunctionAssumption
      (Gamma := finiteBoundContext bound)
      (target := body/[&0])
      (left := finiteEqualityCases (&0) bound)
      (right := finiteLowerBoundFormula bound (&0))
      casesBranch lowerBranch
  exact cutClosedAssumption
    (proveFiniteExhaustionAtEigenvariable bound) underExhaustion

def compileOpenImplication
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    CertifiedPAProof (finiteBoundFormula bound 🡒 body/[&0]) :=
  CertifiedPAContextProof.discharge
    (finiteBoundFormula bound) (body/[&0])
    certificate.compileUnderBoundAssumption

def finiteBoundedUniversalBody
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  finiteCaseLessThanFormula (#0)
      (iteratedSuccessorTerm 1 bound) 🡒 body

theorem formula_shift_eq_self_of_freeVariables_eq_empty
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hformula : formula.freeVariables = ∅) :
    Rewriting.shift formula = formula := by
  apply Semiformula.rew_eq_self_of
  · intro index
    simp
  · intro index hindex
    have : index ∈ formula.freeVariables := hindex
    rw [hformula] at this
    simp at this

theorem formula_free_eq_substitution_of_freeVariables_eq_empty
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hformula : formula.freeVariables = ∅) :
    Rewriting.free formula = formula/[&0] := by
  calc
    Rewriting.free formula =
        (Rewriting.shift formula)/[&0] :=
      (LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free
        formula).symm
    _ = formula/[&0] := by
      rw [formula_shift_eq_self_of_freeVariables_eq_empty formula hformula]

theorem finiteBoundedUniversalBody_free
    (bound : Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hbody : body.freeVariables = ∅) :
    Rewriting.free (finiteBoundedUniversalBody bound body) =
      (finiteBoundFormula bound 🡒 body/[&0]) := by
  let boundFormula : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
    finiteCaseLessThanFormula (#0) (iteratedSuccessorTerm 1 bound)
  have hsubject :
      ((#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1).freeVariables) = ∅ :=
    rfl
  have hboundTerm :=
    iteratedSuccessorTerm_freeVariables_eq_empty 1 bound
  have hboundFormula : boundFormula.freeVariables = ∅ :=
    finiteCaseLessThanFormula_freeVariables_eq_empty
      (#0) (iteratedSuccessorTerm 1 bound) hsubject hboundTerm
  unfold finiteBoundedUniversalBody
  rw [LogicalConnective.HomClass.map_imply]
  rw [formula_free_eq_substitution_of_freeVariables_eq_empty
      boundFormula hboundFormula]
  rw [formula_free_eq_substitution_of_freeVariables_eq_empty body hbody]
  rw [finiteCaseLessThanFormula_substitution]
  rfl

def compile
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    CertifiedPAProof (∀⁰ finiteBoundedUniversalBody bound body) :=
  universalIntroduction
    (finiteBoundedUniversalBody bound body)
    (CertifiedPAProof.cast
      (finiteBoundedUniversalBody_free bound body
        certificate.body_freeVariables_eq_empty).symm
      certificate.compileOpenImplication)

theorem compile_verifier_eq_true
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    listedCompactCertifiedPAProofVerifier certificate.compile.code
      (compactFormulaCode
        (∀⁰ finiteBoundedUniversalBody bound body)) = true :=
  certificate.compile.verifier_eq_true

#print axioms CheckedFiniteUniversalBranches.compileCasesUnderBoundAssumption
#print axioms cutClosedAssumptionCertificate_valid
#print axioms compile_verifier_eq_true

end CheckedFiniteBoundedUniversalCertificate

end FoundationCompactPABoundedUniversalCompiler
