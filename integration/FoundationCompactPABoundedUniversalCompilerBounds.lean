import integration.FoundationCompactPAFiniteExhaustionBounds

/-!
# Structural payload bounds for the finite bounded-universal compiler

The bounds below charge the actual weakening, case-split, cut, discharge, and
universal-introduction nodes emitted by the compiler.  They accept no proof
length, proof existence, or semantic completeness premise.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABoundedUniversalCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAFiniteExhaustionInduction
open FoundationCompactPAFiniteExhaustionBounds
open FoundationCompactPAUnaryTermEqualityImplication
open FoundationCompactPAUnaryBoundedFormulaTransport
open FoundationCompactPAUnaryBoundedFormulaTransport.CheckedUnaryReplacementCertificate
open FoundationCompactCertifiedUniversalIntroduction
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalCompiler.CheckedFiniteUniversalBranches
open FoundationCompactPABoundedUniversalCompiler.CheckedFiniteBoundedUniversalCertificate

def cutClosedAssumptionDerivationCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (caseFormula target : LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryNatCode 9).length +
      (binarySequentCode (insert target Gamma)).length +
      (binaryFormulaCode caseFormula).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert caseFormula (insert target Gamma))).length +
    (binaryNatCode 7).length +
      (binarySequentCode
        (insert (∼caseFormula) (insert target Gamma))).length

theorem cutClosedAssumptionDerivation_binaryProofLength_eq
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {caseFormula target : LO.FirstOrder.ArithmeticProposition}
    (caseProof : LO.FirstOrder.Derivation2 PA {caseFormula})
    (targetProof : LO.FirstOrder.Derivation2 PA
      (insert target (insert (∼caseFormula) Gamma))) :
    binaryProofLength
        (cutClosedAssumptionDerivation caseProof targetProof) =
      binaryProofLength caseProof + binaryProofLength targetProof +
        cutClosedAssumptionDerivationCost Gamma caseFormula target := by
  simp only [cutClosedAssumptionDerivation, binaryProofLength,
    binaryDerivationCode, List.length_append]
  unfold cutClosedAssumptionDerivationCost
  omega

theorem cutClosedAssumptionCertificate_code_length_le
    (caseCertificate targetCertificate : StructuralValidityCertificate) :
    (binaryStructuralValidityCertificateCode
      (cutClosedAssumptionCertificate
        caseCertificate targetCertificate)).length <=
      (binaryStructuralValidityCertificateCode caseCertificate).length +
      (binaryStructuralValidityCertificateCode targetCertificate).length +
      48 := by
  have htag2 : (binaryNatCode 2).length <= 16 := by decide
  have htag3 : (binaryNatCode 3).length <= 16 := by decide
  simp only [cutClosedAssumptionCertificate,
    binaryStructuralValidityCertificateCode, List.length_append]
  omega

def cutClosedAssumptionFullAssemblyCost
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (caseFormula target : LO.FirstOrder.ArithmeticProposition) : Nat :=
  cutClosedAssumptionDerivationCost Gamma caseFormula target + 48

theorem cutClosedAssumption_payloadLength_le
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {caseFormula target : LO.FirstOrder.ArithmeticProposition}
    (caseProof : CertifiedPAProof caseFormula)
    (targetProof : CertifiedPAContextProof
      (insert (∼caseFormula) Gamma) target) :
    (cutClosedAssumption caseProof targetProof).payloadLength <=
      caseProof.payloadLength + targetProof.payloadLength +
        cutClosedAssumptionFullAssemblyCost
          Gamma caseFormula target := by
  have hproof := cutClosedAssumptionDerivation_binaryProofLength_eq
    caseProof.derivation targetProof.derivation
  have hcertificate := cutClosedAssumptionCertificate_code_length_le
    caseProof.certificate targetProof.certificate
  rw [CertifiedPAProof.payloadLength_eq]
  unfold CertifiedPAContextProof.payloadLength
  change binaryProofLength
      (cutClosedAssumptionDerivation
        caseProof.derivation targetProof.derivation) +
      (binaryStructuralValidityCertificateCode
        (cutClosedAssumptionCertificate
          caseProof.certificate targetProof.certificate)).length <= _
  unfold cutClosedAssumptionFullAssemblyCost
  omega

namespace CheckedFiniteUniversalBranches

def structuralPayloadBound
    (totalBound : Nat)
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1} :
    {caseCount : Nat} →
      CheckedFiniteUniversalBranches body caseCount → Nat
  | 0, .nil =>
      CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost (body/[&0]) +
        weakeningFullAssemblyCost
          (insert (body/[&0])
            (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
              (finiteBoundContext totalBound)))
  | bound + 1, .snoc initial last =>
      structuralPayloadBound totalBound initial +
        (last.structuralPayloadBound +
          weakeningFullAssemblyCost
            (insert (body/[&0])
              (insert
                (∼finiteCaseEqualityFormula
                  (iteratedSuccessorTerm 0 bound) (&0))
                (finiteBoundContext totalBound)))) +
        CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
          (finiteBoundContext totalBound) (body/[&0])
          (finiteEqualityCases (&0) bound)
          (finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 bound) (&0))

theorem compileCasesUnderBoundAssumption_payloadLength_le_structural
    (totalBound : Nat)
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {caseCount : Nat}
    (branches : CheckedFiniteUniversalBranches body caseCount) :
    (branches.compileCasesUnderBoundAssumption totalBound).payloadLength <=
      structuralPayloadBound totalBound branches := by
  induction branches with
  | nil =>
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
      have hbase := CertifiedPAContextProof.exFalsoAssumption_payloadLength_eq
        (body/[&0])
      have hweaken := CertifiedPAContextProof.weakenContext_payloadLength_le
        base (by
          intro formula hformula
          simp only [Finset.mem_singleton] at hformula
          subst formula
          exact Finset.mem_insert_self
            (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
            (finiteBoundContext totalBound))
      have hresult : weakened.payloadLength <=
          structuralPayloadBound totalBound
            (CheckedFiniteUniversalBranches.nil :
              CheckedFiniteUniversalBranches body 0) := by
        simp only [structuralPayloadBound]
        exact hweaken.trans (by
          rw [hbase])
      exact hresult
  | @snoc bound initial last ih =>
      let leftBranch :=
        compileCasesUnderBoundAssumption totalBound initial
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
      have hrightRaw :=
        compileUnderAssumption_payloadLength_le_structuralPayloadBound last
      have hrightSingleton : rightSingleton.payloadLength <=
          last.structuralPayloadBound := by
        rw [CertifiedPAContextProof.castContext_payloadLength]
        exact hrightRaw
      have hrightConstructor :=
        CertifiedPAContextProof.weakenContext_payloadLength_le
          rightSingleton (by
            intro formula hformula
            simp only [Finset.mem_singleton] at hformula
            subst formula
            exact Finset.mem_insert_self
              (∼finiteCaseEqualityFormula
                (iteratedSuccessorTerm 0 bound) (&0))
              (finiteBoundContext totalBound))
      have hright : rightBranch.payloadLength <=
          last.structuralPayloadBound +
            weakeningFullAssemblyCost
              (insert (body/[&0])
                (insert
                  (∼finiteCaseEqualityFormula
                    (iteratedSuccessorTerm 0 bound) (&0))
                  (finiteBoundContext totalBound))) := by
        change rightBranch.payloadLength <= _ at hrightConstructor
        exact hrightConstructor.trans
          (Nat.add_le_add_right hrightSingleton _)
      have hcombined :=
        CertifiedPAContextProof.eliminateDisjunctionAssumption_payloadLength_le
          (Gamma := finiteBoundContext totalBound)
          (target := body/[&0])
          (left := finiteEqualityCases (&0) bound)
          (right := finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 bound) (&0))
          leftBranch rightBranch
      change combined.payloadLength <= _ at hcombined
      change combined.payloadLength <= structuralPayloadBound totalBound
        (CheckedFiniteUniversalBranches.snoc initial last)
      simp only [structuralPayloadBound]
      exact hcombined.trans
        (Nat.add_le_add_right (Nat.add_le_add ih hright) _)

end CheckedFiniteUniversalBranches

def lowerBoundContradictionFullPayloadCost
    (bound : Nat)
    (target : LO.FirstOrder.ArithmeticProposition) : Nat :=
  (binaryNatCode 0).length +
    (binarySequentCode
      (insert target
        (insert (∼finiteLowerBoundFormula bound (&0))
          (finiteBoundContext bound)))).length +
    (binaryFormulaCode (finiteBoundFormula bound)).length +
    (binaryNatCode 0).length

theorem lowerBoundContradiction_payloadLength_eq
    (bound : Nat)
    (target : LO.FirstOrder.ArithmeticProposition) :
    (lowerBoundContradiction bound target).payloadLength =
      lowerBoundContradictionFullPayloadCost bound target := by
  simp [CertifiedPAContextProof.payloadLength,
    lowerBoundContradiction, lowerBoundContradictionFullPayloadCost,
    binaryProofLength, binaryDerivationCode,
    binaryStructuralValidityCertificateCode]
  omega

def finiteExhaustionAtEigenvariableStructuralPayloadBound
    (bound : Nat) : Nat :=
  finiteExhaustionStructuralPayloadBound bound +
    specializationCost (finiteExhaustionBody bound) (&0)

theorem proveFiniteExhaustionAtEigenvariable_payloadLength_le_structural
    (bound : Nat) :
    (proveFiniteExhaustionAtEigenvariable bound).payloadLength <=
      finiteExhaustionAtEigenvariableStructuralPayloadBound bound := by
  have hfinite := proveFiniteExhaustion_payloadLength_le_structural bound
  have hspecialize := CertifiedPAProof.specialize_payloadLength_le_cost
    (proveFiniteExhaustion bound) (&0)
  simp only [proveFiniteExhaustionAtEigenvariable,
    CertifiedPAProof.cast_payloadLength]
  exact hspecialize.trans (Nat.add_le_add_right hfinite _)

namespace CheckedFiniteBoundedUniversalCertificate

def underExhaustionStructuralPayloadBound
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) : Nat :=
  CheckedFiniteUniversalBranches.structuralPayloadBound
      bound certificate.branches +
    lowerBoundContradictionFullPayloadCost bound (body/[&0]) +
    CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
      (finiteBoundContext bound) (body/[&0])
      (finiteEqualityCases (&0) bound)
      (finiteLowerBoundFormula bound (&0))

def compileUnderBoundAssumptionStructuralPayloadBound
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) : Nat :=
  finiteExhaustionAtEigenvariableStructuralPayloadBound bound +
    underExhaustionStructuralPayloadBound certificate +
    cutClosedAssumptionFullAssemblyCost
      (finiteBoundContext bound)
      (finiteExhaustionFormula bound (&0)) (body/[&0])

theorem compileUnderBoundAssumption_payloadLength_le_structural
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    certificate.compileUnderBoundAssumption.payloadLength <=
      compileUnderBoundAssumptionStructuralPayloadBound certificate := by
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
  let exhaustionProof := proveFiniteExhaustionAtEigenvariable bound
  have hcases :=
    CheckedFiniteUniversalBranches.compileCasesUnderBoundAssumption_payloadLength_le_structural
      bound certificate.branches
  have hlower := lowerBoundContradiction_payloadLength_eq
    bound (body/[&0])
  have hunderConstructor :=
    CertifiedPAContextProof.eliminateDisjunctionAssumption_payloadLength_le
      (Gamma := finiteBoundContext bound)
      (target := body/[&0])
      (left := finiteEqualityCases (&0) bound)
      (right := finiteLowerBoundFormula bound (&0))
      casesBranch lowerBranch
  have hunder : underExhaustion.payloadLength <=
      underExhaustionStructuralPayloadBound certificate := by
    change underExhaustion.payloadLength <= _ at hunderConstructor
    unfold underExhaustionStructuralPayloadBound
    exact hunderConstructor.trans
      (Nat.add_le_add_right
        (Nat.add_le_add hcases (le_of_eq hlower)) _)
  have hexhaustion :=
    proveFiniteExhaustionAtEigenvariable_payloadLength_le_structural bound
  have hexhaustionProof : exhaustionProof.payloadLength <=
      finiteExhaustionAtEigenvariableStructuralPayloadBound bound := by
    simpa only [exhaustionProof] using hexhaustion
  have hcut := cutClosedAssumption_payloadLength_le
    exhaustionProof underExhaustion
  change certificate.compileUnderBoundAssumption.payloadLength <= _ at hcut
  unfold compileUnderBoundAssumptionStructuralPayloadBound
  exact hcut.trans
    (Nat.add_le_add_right
      (Nat.add_le_add hexhaustionProof hunder) _)

def compileOpenImplicationStructuralPayloadBound
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) : Nat :=
  compileUnderBoundAssumptionStructuralPayloadBound certificate +
    CertifiedPAContextProof.dischargeFullAssemblyCost
      (finiteBoundFormula bound) (body/[&0])

theorem compileOpenImplication_payloadLength_le_structural
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    certificate.compileOpenImplication.payloadLength <=
      compileOpenImplicationStructuralPayloadBound certificate := by
  have hunder := compileUnderBoundAssumption_payloadLength_le_structural
    certificate
  have hdischarge := CertifiedPAContextProof.discharge_payloadLength_le
    (finiteBoundFormula bound) (body/[&0])
    certificate.compileUnderBoundAssumption
  exact hdischarge.trans (by
    unfold compileOpenImplicationStructuralPayloadBound
    exact Nat.add_le_add_right hunder _)

def compileStructuralPayloadBound
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) : Nat :=
  compileOpenImplicationStructuralPayloadBound certificate +
    universalIntroductionFullAssemblyCost
      (finiteBoundedUniversalBody bound body)

theorem compile_payloadLength_le_structural
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    certificate.compile.payloadLength <=
      compileStructuralPayloadBound certificate := by
  let openProof := certificate.compileOpenImplication
  let bodyProof := CertifiedPAProof.cast
    (finiteBoundedUniversalBody_free bound body
      certificate.body_freeVariables_eq_empty).symm openProof
  have hopen := compileOpenImplication_payloadLength_le_structural certificate
  have hbody : bodyProof.payloadLength <=
      compileOpenImplicationStructuralPayloadBound certificate := by
    rw [CertifiedPAProof.cast_payloadLength]
    simpa only [openProof] using hopen
  have hconstructor := universalIntroduction_payloadLength_le
    (finiteBoundedUniversalBody bound body) bodyProof
  change certificate.compile.payloadLength <= _ at hconstructor
  unfold compileStructuralPayloadBound
  exact hconstructor.trans (Nat.add_le_add_right hbody _)

theorem compile_checked_structural
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    listedCompactCertifiedPAProofVerifier certificate.compile.code
        (compactFormulaCode
          (∀⁰ finiteBoundedUniversalBody bound body)) = true ∧
      certificate.compile.payloadLength <=
        compileStructuralPayloadBound certificate :=
  ⟨certificate.compile_verifier_eq_true,
    compile_payloadLength_le_structural certificate⟩

end CheckedFiniteBoundedUniversalCertificate

#print axioms cutClosedAssumption_payloadLength_le
#print axioms proveFiniteExhaustionAtEigenvariable_payloadLength_le_structural

namespace CheckedFiniteUniversalBranches
#print axioms compileCasesUnderBoundAssumption_payloadLength_le_structural
end CheckedFiniteUniversalBranches

namespace CheckedFiniteBoundedUniversalCertificate
#print axioms compile_checked_structural
end CheckedFiniteBoundedUniversalCertificate

end FoundationCompactPABoundedUniversalCompilerBounds
