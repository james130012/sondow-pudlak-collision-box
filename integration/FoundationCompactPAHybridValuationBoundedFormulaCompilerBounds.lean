import integration.FoundationCompactPAHybridValuationBoundedFormulaCompiler
import integration.FoundationCompactPAValuationAtomicCompilerBounds
import integration.FoundationCompactPAExponentialValuationContextCompilerBounds
import integration.FoundationCompactPABinaryLengthValuationContextCompilerBounds
import integration.FoundationCompactPABitMembershipValuationContextCompilerBounds
import integration.FoundationCompactPAValuationShiftedBoundCompilerBounds
import integration.FoundationCompactPAContextualTermBoundedUniversalCompilerBounds

/-!
# Structural payload bounds for the hybrid valuation compiler

The bounds in this file depend only on the certificate data and explicit
syntax resources.  In particular, the bounded-universal resource replaces
the generated bound proof and generated branch proofs by independent
proof-free envelopes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAAxiomCertificate
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactBinaryNumeralTerm
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextDischarge
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalCompilerBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAExponentialValuationContextCompilerBounds
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPABinaryLengthValuationContextCompilerBounds
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

namespace CheckedHybridValuationBoundedFormulaCertificate

open FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate

/-- The part of `compileUnderBoundAssumptionStructuralPayloadBound` that is
independent of the concrete generated branch proofs. -/
def contextualBranchesUnderBoundPayloadEnvelope
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound : Nat)
    (target : LO.FirstOrder.ArithmeticProposition)
    (caseResource : Nat) : Nat :=
  finiteExhaustionAtEigenvariableStructuralPayloadBound bound +
    (caseResource +
      lowerBranchStructuralPayloadBound Gamma bound target +
      CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
        (contextualFiniteBoundContext Gamma bound) target
        (finiteEqualityCases (&0) bound)
        (finiteLowerBoundFormula bound (&0))) +
    cutClosedAssumptionFullAssemblyCost
      (contextualFiniteBoundContext Gamma bound)
      (finiteExhaustionFormula bound (&0)) target

mutual

  /-- Proof-free structural resource for one hybrid formula certificate. -/
  def hybridFormulaStructuralPayloadBound :
      {valuation : Nat -> Nat} -> {formula : ValuationFormula} ->
      CheckedHybridValuationBoundedFormulaCertificate valuation formula -> Nat
    | _, _, .verum valuation =>
        let Gamma := valuationContext
          (⊤ : ValuationFormula).freeVariables valuation
        (48 + 9 * verumSyntaxBudget) +
          weakeningFullAssemblyCost
            (insert (⊤ : ValuationFormula) Gamma)
    | _, _, .positiveAtomic valuation relationSymbol args _ =>
        compilePositiveRelationPayloadResource valuation relationSymbol args
    | _, _, .negativeAtomic valuation relationSymbol args _ =>
        compileNegativeRelationPayloadResource valuation relationSymbol args
    | _, _, .exponential valuation valueTerm exponentTerm _ =>
        compileExponentialAtValuationPayloadResource
          valuation valueTerm exponentTerm
    | _, _, .binaryLength valuation sizeTerm valueTerm _ =>
        compileBinaryLengthAtValuationPayloadResource
          valuation sizeTerm valueTerm
    | _, _, .binaryBit expected valuation indexTerm valueTerm _ _ =>
        let formula := binaryBitAtValuationFormula
          expected indexTerm valueTerm
        let Gamma := valuationContext formula.freeVariables valuation
        compileBinaryBitLiteralAtValuationPayloadResource
            expected valuation indexTerm valueTerm +
          weakeningFullAssemblyCost (insert formula Gamma)
    | valuation, _, .conjunction (left := left) (right := right)
        leftCertificate rightCertificate =>
        let Gamma := valuationContext (left ⋏ right).freeVariables valuation
        hybridFormulaStructuralPayloadBound leftCertificate +
          weakeningFullAssemblyCost (insert left Gamma) +
          hybridFormulaStructuralPayloadBound rightCertificate +
          weakeningFullAssemblyCost (insert right Gamma) +
          CertifiedPAContextProof.conjunctionFullAssemblyCost Gamma left right
    | valuation, _, .disjunctionLeft (left := left) (right := right)
        leftCertificate =>
        let Gamma := valuationContext (left ⋎ right).freeVariables valuation
        hybridFormulaStructuralPayloadBound leftCertificate +
          weakeningFullAssemblyCost (insert left Gamma) +
          CertifiedPAContextProof.disjunctionFullAssemblyCost Gamma left right
    | valuation, _, .disjunctionRight (left := left) (right := right)
        rightCertificate =>
        let Gamma := valuationContext (left ⋎ right).freeVariables valuation
        hybridFormulaStructuralPayloadBound rightCertificate +
          weakeningFullAssemblyCost (insert right Gamma) +
          CertifiedPAContextProof.disjunctionFullAssemblyCost Gamma left right
    | valuation, _, .existsWitness body witness bodyCertificate =>
        let formula := (∃⁰ body : ValuationFormula)
        let instantiated := body/[shortBinaryNumeralTerm witness]
        let Gamma := valuationContext formula.freeVariables valuation
        hybridFormulaStructuralPayloadBound bodyCertificate +
          weakeningFullAssemblyCost (insert instantiated Gamma) +
          CertifiedPAContextProof.existsIntroFullAssemblyCost Gamma body
            (shortBinaryNumeralTerm witness)
    | valuation, _, .boundedUniversal boundSource body branches =>
        let outerFormula := ∀⁰ termBoundedUniversalBody
          (Rew.bShift boundSource) body
        let outerVariables := outerFormula.freeVariables
        let Gamma := valuationContext outerVariables valuation
        let bound := termValue valuation boundSource
        let branchResource := contextualBranchesUnderBoundPayloadEnvelope
          (Gamma.image Rewriting.shift) bound (Rewriting.free body)
          (hybridBranchesStructuralPayloadEnvelope
            bound outerVariables branches)
        compileContextualTermBoundedUniversalPayloadEnvelope
          Gamma bound (Rew.bShift boundSource) body
          (compileShiftedBoundEqualityPayloadResource
            valuation outerVariables boundSource)
          branchResource
    | _, _, .cast _ sourceCertificate =>
        hybridFormulaStructuralPayloadBound sourceCertificate

  /-- Proof-free envelope for the recursive case split assembled from all
  hybrid branch certificates.  It charges both contextual weakenings used by
  the runtime compiler. -/
  def hybridBranchesStructuralPayloadEnvelope
      (totalBound : Nat)
      (outerVariables : Finset Nat)
      {valuation : Nat -> Nat}
      {body : LO.FirstOrder.ArithmeticSemiformula Nat 1} :
      {bound : Nat} ->
      CheckedHybridValuationUniversalBranches valuation body bound -> Nat
    | 0, .nil _ _ =>
        let Gamma :=
          (valuationContext outerVariables valuation).image Rewriting.shift
        let target := Rewriting.free body
        CertifiedPAContextProof.exFalsoAssumptionFullPayloadCost target +
          weakeningFullAssemblyCost
            (insert target
              (insert (∼(⊥ : LO.FirstOrder.ArithmeticProposition))
                (contextualFiniteBoundContext Gamma totalBound)))
    | bound + 1, .snoc initial last =>
        let Gamma :=
          (valuationContext outerVariables valuation).image Rewriting.shift
        let target := Rewriting.free body
        let caseFormula := finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 bound) (&0)
        hybridBranchesStructuralPayloadEnvelope
            totalBound outerVariables initial +
          (hybridFormulaStructuralPayloadBound last +
            weakeningFullAssemblyCost
              (insert target (insert (∼caseFormula) Gamma)) +
            weakeningFullAssemblyCost
              (insert target
                (insert (∼caseFormula)
                  (contextualFiniteBoundContext Gamma totalBound)))) +
          CertifiedPAContextProof.eliminateDisjunctionAssumptionFullAssemblyCost
            (contextualFiniteBoundContext Gamma totalBound) target
            (finiteEqualityCases (&0) bound) caseFormula

end

def hybridBranchesUnderBoundPayloadEnvelope
    (outerVariables : Finset Nat)
    {valuation : Nat -> Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    {bound : Nat}
    (branches : CheckedHybridValuationUniversalBranches valuation body bound) :
    Nat :=
  let Gamma :=
    (valuationContext outerVariables valuation).image Rewriting.shift
  contextualBranchesUnderBoundPayloadEnvelope Gamma bound
    (Rewriting.free body)
    (hybridBranchesStructuralPayloadEnvelope bound outerVariables branches)

mutual

  noncomputable def compile_payloadLength_le_structuralPayloadBound :
      {valuation : Nat -> Nat} -> {formula : ValuationFormula} ->
      (certificate :
        CheckedHybridValuationBoundedFormulaCertificate valuation formula) ->
      certificate.compile.payloadLength <=
        hybridFormulaStructuralPayloadBound certificate
    | _, _, .verum valuation => by
        let Gamma := valuationContext
          (⊤ : ValuationFormula).freeVariables valuation
        have hraw := CertifiedPAProof.verumProof_payloadLength_le
        have hweaken := CertifiedPAContextProof.weakenCertified_payloadLength_le
          Gamma CertifiedPAProof.verumProof
        simp only [FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compile,
          hybridFormulaStructuralPayloadBound]
        exact hweaken.trans (Nat.add_le_add_right hraw _)
    | _, _, .positiveAtomic valuation relationSymbol args htruth => by
        simpa only [FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compile,
          hybridFormulaStructuralPayloadBound] using
          compilePositiveRelation_payloadLength_le_resource
            valuation relationSymbol args htruth
    | _, _, .negativeAtomic valuation relationSymbol args htruth => by
        simpa only [FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compile,
          hybridFormulaStructuralPayloadBound] using
          compileNegativeRelation_payloadLength_le_resource
            valuation relationSymbol args htruth
    | _, _, .exponential valuation valueTerm exponentTerm hvalue => by
        let raw := compileExponentialAtValuation
          valuation valueTerm exponentTerm hvalue
        have hcontext :
            exponentialValuationContext valuation valueTerm exponentTerm =
              valuationContext
                (exponentialAtValuationFormula
                  valueTerm exponentTerm).freeVariables valuation := by
          unfold exponentialValuationContext
          rw [exponentialAtValuationFormula_freeVariables]
        let casted := CertifiedPAContextProof.castContext hcontext raw
        have hraw := compileExponentialAtValuation_payloadLength_le_resource
          valuation valueTerm exponentTerm hvalue
        have hcast := CertifiedPAContextProof.castContext_payloadLength
          hcontext raw
        change casted.payloadLength <=
          compileExponentialAtValuationPayloadResource
            valuation valueTerm exponentTerm
        rw [hcast]
        exact hraw
    | _, _, .binaryLength valuation sizeTerm valueTerm hsize => by
        let raw := compileBinaryLengthAtValuation
          valuation sizeTerm valueTerm hsize
        have hcontext :
            binaryLengthValuationContext valuation sizeTerm valueTerm =
              valuationContext
                (binaryLengthAtValuationFormula
                  sizeTerm valueTerm).freeVariables valuation := by
          unfold binaryLengthValuationContext
          rw [binaryLengthAtValuationFormula_freeVariables]
        let casted := CertifiedPAContextProof.castContext hcontext raw
        have hraw := compileBinaryLengthAtValuation_payloadLength_le_resource
          valuation sizeTerm valueTerm hsize
        have hcast := CertifiedPAContextProof.castContext_payloadLength
          hcontext raw
        change casted.payloadLength <=
          compileBinaryLengthAtValuationPayloadResource
            valuation sizeTerm valueTerm
        rw [hcast]
        exact hraw
    | _, _, .binaryBit expected valuation indexTerm valueTerm hbit
        hvariables => by
        let formula := binaryBitAtValuationFormula
          expected indexTerm valueTerm
        let Gamma := valuationContext formula.freeVariables valuation
        let raw := compileBinaryBitLiteralAtValuation
          expected valuation indexTerm valueTerm hbit
        let weakened := CertifiedPAContextProof.weakenContext raw
          (valuationContext_mono valuation hvariables)
        have hraw :=
          compileBinaryBitLiteralAtValuation_payloadLength_le_resource
            expected valuation indexTerm valueTerm hbit
        have hweaken := CertifiedPAContextProof.weakenContext_payloadLength_le
          raw (valuationContext_mono valuation hvariables)
        have hresult : weakened.payloadLength <=
            compileBinaryBitLiteralAtValuationPayloadResource
                expected valuation indexTerm valueTerm +
              weakeningFullAssemblyCost (insert formula Gamma) :=
          hweaken.trans (Nat.add_le_add_right hraw _)
        simpa only [FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compile,
          hybridFormulaStructuralPayloadBound, formula, Gamma, raw, weakened]
          using hresult
    | valuation, _, .conjunction (left := left) (right := right)
        leftCertificate rightCertificate => by
        let Gamma := valuationContext (left ⋏ right).freeVariables valuation
        have hleftVariables : left.freeVariables ⊆
            (left ⋏ right).freeVariables := by simp
        have hrightVariables : right.freeVariables ⊆
            (left ⋏ right).freeVariables := by simp
        let leftRaw := leftCertificate.compile
        let rightRaw := rightCertificate.compile
        let leftProof := CertifiedPAContextProof.weakenContext leftRaw
          (valuationContext_mono valuation hleftVariables)
        let rightProof := CertifiedPAContextProof.weakenContext rightRaw
          (valuationContext_mono valuation hrightVariables)
        have ihLeft := compile_payloadLength_le_structuralPayloadBound
          leftCertificate
        have ihRight := compile_payloadLength_le_structuralPayloadBound
          rightCertificate
        have hleftWeak := CertifiedPAContextProof.weakenContext_payloadLength_le
          leftRaw (valuationContext_mono valuation hleftVariables)
        have hrightWeak := CertifiedPAContextProof.weakenContext_payloadLength_le
          rightRaw (valuationContext_mono valuation hrightVariables)
        have hleft : leftProof.payloadLength <=
            hybridFormulaStructuralPayloadBound leftCertificate +
              weakeningFullAssemblyCost (insert left Gamma) :=
          hleftWeak.trans (Nat.add_le_add_right ihLeft _)
        have hright : rightProof.payloadLength <=
            hybridFormulaStructuralPayloadBound rightCertificate +
              weakeningFullAssemblyCost (insert right Gamma) :=
          hrightWeak.trans (Nat.add_le_add_right ihRight _)
        have hconstructor := CertifiedPAContextProof.conjunction_payloadLength_le
          leftProof rightProof
        simp only [FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compile,
          hybridFormulaStructuralPayloadBound]
        change (CertifiedPAContextProof.conjunction leftProof rightProof).payloadLength <= _
        dsimp only [Gamma] at hleft hright hconstructor ⊢
        omega
    | valuation, _, .disjunctionLeft (left := left) (right := right)
        leftCertificate => by
        let Gamma := valuationContext (left ⋎ right).freeVariables valuation
        have hvariables : left.freeVariables ⊆
            (left ⋎ right).freeVariables := by simp
        let raw := leftCertificate.compile
        let proof := CertifiedPAContextProof.weakenContext raw
          (valuationContext_mono valuation hvariables)
        have ih := compile_payloadLength_le_structuralPayloadBound leftCertificate
        have hweak := CertifiedPAContextProof.weakenContext_payloadLength_le
          raw (valuationContext_mono valuation hvariables)
        have hproof : proof.payloadLength <=
            hybridFormulaStructuralPayloadBound leftCertificate +
              weakeningFullAssemblyCost (insert left Gamma) :=
          hweak.trans (Nat.add_le_add_right ih _)
        have hconstructor := CertifiedPAContextProof.disjunctionLeft_payloadLength_le
          (right := right) proof
        simp only [FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compile,
          hybridFormulaStructuralPayloadBound]
        change (CertifiedPAContextProof.disjunctionLeft (right := right) proof).payloadLength <= _
        dsimp only [Gamma] at hproof hconstructor ⊢
        omega
    | valuation, _, .disjunctionRight (left := left) (right := right)
        rightCertificate => by
        let Gamma := valuationContext (left ⋎ right).freeVariables valuation
        have hvariables : right.freeVariables ⊆
            (left ⋎ right).freeVariables := by simp
        let raw := rightCertificate.compile
        let proof := CertifiedPAContextProof.weakenContext raw
          (valuationContext_mono valuation hvariables)
        have ih := compile_payloadLength_le_structuralPayloadBound rightCertificate
        have hweak := CertifiedPAContextProof.weakenContext_payloadLength_le
          raw (valuationContext_mono valuation hvariables)
        have hproof : proof.payloadLength <=
            hybridFormulaStructuralPayloadBound rightCertificate +
              weakeningFullAssemblyCost (insert right Gamma) :=
          hweak.trans (Nat.add_le_add_right ih _)
        have hconstructor := CertifiedPAContextProof.disjunctionRight_payloadLength_le
          (left := left) proof
        simp only [FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compile,
          hybridFormulaStructuralPayloadBound]
        change (CertifiedPAContextProof.disjunctionRight (left := left) proof).payloadLength <= _
        dsimp only [Gamma] at hproof hconstructor ⊢
        omega
    | valuation, _, .existsWitness body witness bodyCertificate => by
        let formula := (∃⁰ body : ValuationFormula)
        let instantiated := body/[shortBinaryNumeralTerm witness]
        let Gamma := valuationContext formula.freeVariables valuation
        have hvariables : instantiated.freeVariables ⊆ formula.freeVariables :=
          (shortBinarySubstitution_freeVariables_subset body witness).trans
            (by
              dsimp only [formula]
              simp)
        let raw := bodyCertificate.compile
        let proof := CertifiedPAContextProof.weakenContext raw
          (valuationContext_mono valuation hvariables)
        have ih := compile_payloadLength_le_structuralPayloadBound bodyCertificate
        have hweak := CertifiedPAContextProof.weakenContext_payloadLength_le
          raw (valuationContext_mono valuation hvariables)
        have hproof : proof.payloadLength <=
            hybridFormulaStructuralPayloadBound bodyCertificate +
              weakeningFullAssemblyCost (insert instantiated Gamma) :=
          hweak.trans (Nat.add_le_add_right ih _)
        have hconstructor := CertifiedPAContextProof.existsIntro_payloadLength_le
          (shortBinaryNumeralTerm witness) proof
        simp only [FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compile,
          hybridFormulaStructuralPayloadBound]
        change (CertifiedPAContextProof.existsIntro
          (shortBinaryNumeralTerm witness) proof).payloadLength <= _
        dsimp only [formula, instantiated, Gamma] at hproof hconstructor ⊢
        omega
    | valuation, _, .boundedUniversal boundSource body branches => by
        let outerFormula := ∀⁰ termBoundedUniversalBody
          (Rew.bShift boundSource) body
        let outerVariables := outerFormula.freeVariables
        let Gamma := valuationContext outerVariables valuation
        let bound := termValue valuation boundSource
        have hboundVariables : boundSource.freeVariables ⊆ outerVariables :=
          boundSource_freeVariables_subset_universal boundSource body
        have hbodyVariables : body.freeVariables ⊆ outerVariables :=
          body_freeVariables_subset_universal boundSource body
        let boundRaw := compileShiftedBoundEquality
          valuation outerVariables boundSource hboundVariables
        let boundEquality : CertifiedPAContextProof
            (Gamma.image Rewriting.shift)
            (“!!(iteratedSuccessorTerm 0 bound) =
              !!(Rew.free (Rew.bShift boundSource))” :
              ValuationFormula) := by
          have hfree := free_bShift_term boundSource
          have hformula :
              (“!!(iteratedSuccessorTerm 0 bound) =
                !!(Rew.shift boundSource)” : ValuationFormula) =
              (“!!(iteratedSuccessorTerm 0 bound) =
                !!(Rew.free (Rew.bShift boundSource))” :
                ValuationFormula) := by
            rw [hfree]
          exact CertifiedPAContextProof.cast hformula boundRaw
        let compiledBranches :=
          FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compileBranches
            branches outerVariables hbodyVariables
        let boundResource := compileShiftedBoundEqualityPayloadResource
          valuation outerVariables boundSource
        let branchResource := hybridBranchesUnderBoundPayloadEnvelope
          outerVariables branches
        have hboundRaw := compileShiftedBoundEquality_payloadLength_le_resource
          valuation outerVariables boundSource hboundVariables
        have hbound : boundEquality.payloadLength <= boundResource := by
          simpa only [boundEquality, boundResource,
            CertifiedPAContextProof.cast_payloadLength] using hboundRaw
        have hbranchesCore :=
          compileBranches_structuralPayloadBound_le_envelope
            branches outerVariables hbodyVariables bound
        have hbranches :
            compiledBranches.compileUnderBoundAssumptionStructuralPayloadBound <=
              branchResource := by
          unfold branchResource hybridBranchesUnderBoundPayloadEnvelope
            contextualBranchesUnderBoundPayloadEnvelope
            CertifiedContextFiniteUniversalBranches.compileUnderBoundAssumptionStructuralPayloadBound
            CertifiedContextFiniteUniversalBranches.underExhaustionStructuralPayloadBound
          dsimp only [compiledBranches, bound] at hbranchesCore ⊢
          omega
        have hstructural :=
          compileContextualTermBoundedUniversal_payloadLength_le_structural
            bound (Rew.bShift boundSource) body boundEquality compiledBranches
        have henvelope :=
          compileContextualTermBoundedUniversalStructuralPayloadBound_le_envelope
            bound (Rew.bShift boundSource) body boundEquality compiledBranches
            boundResource branchResource hbound hbranches
        simp only [FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compile,
          hybridFormulaStructuralPayloadBound]
        change (compileContextualTermBoundedUniversal
          bound (Rew.bShift boundSource) body boundEquality
          compiledBranches).payloadLength <= _
        exact hstructural.trans henvelope
    | _, _, .cast formulaEq sourceCertificate => by
        subst formulaEq
        change sourceCertificate.compile.payloadLength <=
          hybridFormulaStructuralPayloadBound sourceCertificate
        exact compile_payloadLength_le_structuralPayloadBound sourceCertificate

  noncomputable def compileBranches_structuralPayloadBound_le_envelope :
      {valuation : Nat -> Nat} ->
      {body : LO.FirstOrder.ArithmeticSemiformula Nat 1} ->
      {bound : Nat} ->
      (branches : CheckedHybridValuationUniversalBranches valuation body bound) ->
      (outerVariables : Finset Nat) ->
      (hbodyVariables : body.freeVariables ⊆ outerVariables) ->
      (totalBound : Nat) ->
      (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compileBranches
          branches outerVariables hbodyVariables).structuralPayloadBound totalBound <=
        hybridBranchesStructuralPayloadEnvelope
          totalBound outerVariables branches
    | _, _, _, .nil _ _, outerVariables, hbodyVariables, totalBound => by
        rfl
    | valuation, body, _, .snoc (bound := bound) initial last,
        outerVariables, hbodyVariables, totalBound => by
        let Gamma :=
          (valuationContext outerVariables valuation).image Rewriting.shift
        let target := Rewriting.free body
        let caseFormula := finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 bound) (&0)
        let lastRaw := last.compile
        let hlastSubset := freedFormulaValuationContext_subset_branch
          bound valuation body outerVariables hbodyVariables
        let lastProof := CertifiedPAContextProof.weakenContext
          lastRaw hlastSubset
        have ih := compileBranches_structuralPayloadBound_le_envelope
          initial outerVariables hbodyVariables totalBound
        have hlastRaw := compile_payloadLength_le_structuralPayloadBound last
        have hlastWeak := CertifiedPAContextProof.weakenContext_payloadLength_le
          lastRaw hlastSubset
        have hlast : lastProof.payloadLength <=
            hybridFormulaStructuralPayloadBound last +
              weakeningFullAssemblyCost
                (insert target (insert (∼caseFormula) Gamma)) :=
          hlastWeak.trans (Nat.add_le_add_right hlastRaw _)
        simp only [FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compileBranches,
          CertifiedContextFiniteUniversalBranches.structuralPayloadBound,
          hybridBranchesStructuralPayloadEnvelope]
        change
          (FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate.compileBranches
              initial outerVariables hbodyVariables).structuralPayloadBound
                totalBound +
            (lastProof.payloadLength + _) + _ <= _
        dsimp only [Gamma, target, caseFormula] at hlast ⊢
        omega

end

theorem compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    {valuation : Nat -> Nat}
    {formula : ValuationFormula}
    (certificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula) :
    certificate.compile.payloadLength <=
      hybridFormulaStructuralPayloadBound certificate :=
  compile_payloadLength_le_structuralPayloadBound certificate

#print axioms hybridFormulaStructuralPayloadBound
#print axioms hybridBranchesStructuralPayloadEnvelope
#print axioms compile_payloadLength_le_hybridFormulaStructuralPayloadBound

end CheckedHybridValuationBoundedFormulaCertificate

end FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
