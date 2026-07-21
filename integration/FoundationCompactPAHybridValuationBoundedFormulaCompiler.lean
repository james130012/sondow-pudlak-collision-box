import integration.FoundationCompactPABitMembershipValuationContextCompiler
import integration.FoundationCompactPABinaryLengthValuationContextCompiler
import integration.FoundationCompactPAExponentialValuationContextCompiler
import integration.FoundationCompactPAValuationBoundedFormulaCompiler

/-!
# Hybrid valuation compiler for bounded arithmetic

The structural compiler is the checked valuation compiler from A04.17 with
three additional proof-producing leaves.  Complete `expDef`, `lengthDef`, and
positive or negative `bitDef` instances are compiled by their binary
algorithms instead of expanding exponentially large internal bounds.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAHybridValuationBoundedFormulaCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAAxiomCertificate
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPABitMembershipValuationContextCompiler

mutual

  inductive CheckedHybridValuationBoundedFormulaCertificate :
      (valuation : Nat -> Nat) -> ValuationFormula -> Type
    | verum (valuation : Nat -> Nat) :
        CheckedHybridValuationBoundedFormulaCertificate valuation
          (⊤ : ValuationFormula)
    | positiveAtomic
        (valuation : Nat -> Nat)
        (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
        (args : Fin 2 -> ValuationTerm)
        (htruth : formulaValue valuation
          (LO.FirstOrder.Semiformula.rel relationSymbol args)) :
        CheckedHybridValuationBoundedFormulaCertificate valuation
          (LO.FirstOrder.Semiformula.rel relationSymbol args)
    | negativeAtomic
        (valuation : Nat -> Nat)
        (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
        (args : Fin 2 -> ValuationTerm)
        (htruth : formulaValue valuation
          (LO.FirstOrder.Semiformula.nrel relationSymbol args)) :
        CheckedHybridValuationBoundedFormulaCertificate valuation
          (LO.FirstOrder.Semiformula.nrel relationSymbol args)
    | exponential
        (valuation : Nat -> Nat)
        (valueTerm exponentTerm : ValuationTerm)
        (hvalue : termValue valuation valueTerm =
          2 ^ termValue valuation exponentTerm) :
        CheckedHybridValuationBoundedFormulaCertificate valuation
          (exponentialAtValuationFormula valueTerm exponentTerm)
    | binaryLength
        (valuation : Nat -> Nat)
        (sizeTerm valueTerm : ValuationTerm)
        (hsize : termValue valuation sizeTerm =
          Nat.size (termValue valuation valueTerm)) :
        CheckedHybridValuationBoundedFormulaCertificate valuation
          (binaryLengthAtValuationFormula sizeTerm valueTerm)
    | binaryBit
        (expected : Bool)
        (valuation : Nat -> Nat)
        (indexTerm valueTerm : ValuationTerm)
        (hbit : (termValue valuation valueTerm).testBit
          (termValue valuation indexTerm) = expected)
        (hvariables : indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
          (binaryBitAtValuationFormula expected
            indexTerm valueTerm).freeVariables) :
        CheckedHybridValuationBoundedFormulaCertificate valuation
          (binaryBitAtValuationFormula expected indexTerm valueTerm)
    | conjunction
        {valuation : Nat -> Nat}
        {left right : ValuationFormula}
        (leftCertificate :
          CheckedHybridValuationBoundedFormulaCertificate valuation left)
        (rightCertificate :
          CheckedHybridValuationBoundedFormulaCertificate valuation right) :
        CheckedHybridValuationBoundedFormulaCertificate valuation
          (left ⋏ right)
    | disjunctionLeft
        {valuation : Nat -> Nat}
        {left right : ValuationFormula}
        (leftCertificate :
          CheckedHybridValuationBoundedFormulaCertificate valuation left) :
        CheckedHybridValuationBoundedFormulaCertificate valuation
          (left ⋎ right)
    | disjunctionRight
        {valuation : Nat -> Nat}
        {left right : ValuationFormula}
        (rightCertificate :
          CheckedHybridValuationBoundedFormulaCertificate valuation right) :
        CheckedHybridValuationBoundedFormulaCertificate valuation
          (left ⋎ right)
    | existsWitness
        {valuation : Nat -> Nat}
        (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
        (witness : Nat)
        (bodyCertificate : CheckedHybridValuationBoundedFormulaCertificate
          valuation (body/[shortBinaryNumeralTerm witness])) :
        CheckedHybridValuationBoundedFormulaCertificate valuation (∃⁰ body)
    | boundedUniversal
        {valuation : Nat -> Nat}
        (boundSource : ValuationTerm)
        (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
        (branches : CheckedHybridValuationUniversalBranches valuation body
          (termValue valuation boundSource)) :
        CheckedHybridValuationBoundedFormulaCertificate valuation
          (∀⁰ termBoundedUniversalBody
            (Rew.bShift boundSource) body)
    | cast
        {valuation : Nat -> Nat}
        {source target : ValuationFormula}
        (formulaEq : source = target)
        (sourceCertificate :
          CheckedHybridValuationBoundedFormulaCertificate valuation source) :
        CheckedHybridValuationBoundedFormulaCertificate valuation target

  inductive CheckedHybridValuationUniversalBranches :
      (valuation : Nat -> Nat) ->
      (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) ->
      Nat -> Type
    | nil (valuation : Nat -> Nat)
        (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
        CheckedHybridValuationUniversalBranches valuation body 0
    | snoc {valuation : Nat -> Nat}
        {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
        {bound : Nat}
        (initial : CheckedHybridValuationUniversalBranches
          valuation body bound)
        (last : CheckedHybridValuationBoundedFormulaCertificate
          (extendValuation bound valuation) (Rewriting.free body)) :
        CheckedHybridValuationUniversalBranches valuation body (bound + 1)

end

namespace CheckedHybridValuationBoundedFormulaCertificate

mutual

  noncomputable def compile :
      {valuation : Nat -> Nat} -> {formula : ValuationFormula} ->
      CheckedHybridValuationBoundedFormulaCertificate valuation formula ->
      CertifiedPAContextProof
        (valuationContext formula.freeVariables valuation) formula
    | _, _, .verum valuation =>
        CertifiedPAContextProof.weakenCertified _
          FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof.verumProof
    | _, _, .positiveAtomic valuation relationSymbol args htruth =>
        compilePositiveRelation valuation relationSymbol args htruth
    | _, _, .negativeAtomic valuation relationSymbol args htruth =>
        compileNegativeRelation valuation relationSymbol args htruth
    | _, _, .exponential valuation valueTerm exponentTerm hvalue => by
        have hcontext :
            exponentialValuationContext valuation valueTerm exponentTerm =
              valuationContext
                (exponentialAtValuationFormula
                  valueTerm exponentTerm).freeVariables valuation := by
          unfold exponentialValuationContext
          rw [exponentialAtValuationFormula_freeVariables]
        exact CertifiedPAContextProof.castContext hcontext
          (compileExponentialAtValuation
            valuation valueTerm exponentTerm hvalue)
    | _, _, .binaryLength valuation sizeTerm valueTerm hsize => by
        have hcontext :
            binaryLengthValuationContext valuation sizeTerm valueTerm =
              valuationContext
                (binaryLengthAtValuationFormula
                  sizeTerm valueTerm).freeVariables valuation := by
          unfold binaryLengthValuationContext
          rw [binaryLengthAtValuationFormula_freeVariables]
        exact CertifiedPAContextProof.castContext hcontext
          (compileBinaryLengthAtValuation
            valuation sizeTerm valueTerm hsize)
    | _, _, .binaryBit expected valuation indexTerm valueTerm hbit
        hvariables =>
        CertifiedPAContextProof.weakenContext
          (compileBinaryBitLiteralAtValuation
            expected valuation indexTerm valueTerm hbit)
          (valuationContext_mono valuation hvariables)
    | valuation, _, .conjunction (left := left) (right := right)
        leftCertificate rightCertificate => by
        let leftRaw := compile leftCertificate
        let rightRaw := compile rightCertificate
        have hleft : left.freeVariables ⊆
            (left ⋏ right).freeVariables := by simp
        have hright : right.freeVariables ⊆
            (left ⋏ right).freeVariables := by simp
        let leftProof := CertifiedPAContextProof.weakenContext leftRaw
          (valuationContext_mono valuation hleft)
        let rightProof := CertifiedPAContextProof.weakenContext rightRaw
          (valuationContext_mono valuation hright)
        exact CertifiedPAContextProof.conjunction leftProof rightProof
    | valuation, _, .disjunctionLeft (left := left) (right := right)
        leftCertificate => by
        let leftRaw := compile leftCertificate
        have hleft : left.freeVariables ⊆
            (left ⋎ right).freeVariables := by simp
        let leftProof := CertifiedPAContextProof.weakenContext leftRaw
          (valuationContext_mono valuation hleft)
        exact CertifiedPAContextProof.disjunctionLeft leftProof
    | valuation, _, .disjunctionRight (left := left) (right := right)
        rightCertificate => by
        let rightRaw := compile rightCertificate
        have hright : right.freeVariables ⊆
            (left ⋎ right).freeVariables := by simp
        let rightProof := CertifiedPAContextProof.weakenContext rightRaw
          (valuationContext_mono valuation hright)
        exact CertifiedPAContextProof.disjunctionRight rightProof
    | valuation, _, .existsWitness body witness bodyCertificate => by
        let bodyRaw := compile bodyCertificate
        have hvariables :
            (body/[shortBinaryNumeralTerm witness]).freeVariables ⊆
              (∃⁰ body).freeVariables :=
          (shortBinarySubstitution_freeVariables_subset body witness).trans
            (by simp)
        let bodyProof := CertifiedPAContextProof.weakenContext bodyRaw
          (valuationContext_mono valuation hvariables)
        exact CertifiedPAContextProof.existsIntro
          (shortBinaryNumeralTerm witness) bodyProof
    | valuation, _, .boundedUniversal boundSource body branches => by
        let outerFormula := ∀⁰ termBoundedUniversalBody
          (Rew.bShift boundSource) body
        let outerVariables := outerFormula.freeVariables
        have hboundVariables : boundSource.freeVariables ⊆ outerVariables :=
          boundSource_freeVariables_subset_universal boundSource body
        have hbodyVariables : body.freeVariables ⊆ outerVariables :=
          body_freeVariables_subset_universal boundSource body
        let boundRaw := compileShiftedBoundEquality
          valuation outerVariables boundSource hboundVariables
        let boundEquality : CertifiedPAContextProof
            ((valuationContext outerVariables valuation).image
              Rewriting.shift)
            (“!!(iteratedSuccessorTerm 0
                (termValue valuation boundSource)) =
              !!(Rew.free (Rew.bShift boundSource))” :
              ValuationFormula) := by
          have hfree := free_bShift_term boundSource
          have hformula :
              (“!!(iteratedSuccessorTerm 0
                    (termValue valuation boundSource)) =
                !!(Rew.shift boundSource)” : ValuationFormula) =
              (“!!(iteratedSuccessorTerm 0
                    (termValue valuation boundSource)) =
                !!(Rew.free (Rew.bShift boundSource))” :
                ValuationFormula) := by
            rw [hfree]
          exact CertifiedPAContextProof.cast hformula boundRaw
        let compiledBranches := compileBranches
          branches outerVariables hbodyVariables
        exact compileContextualTermBoundedUniversal
          (termValue valuation boundSource)
          (Rew.bShift boundSource) body boundEquality compiledBranches
    | _, _, .cast rfl sourceCertificate =>
        compile sourceCertificate

  noncomputable def compileBranches
      {valuation : Nat -> Nat}
      {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
      {bound : Nat}
      (branches : CheckedHybridValuationUniversalBranches
        valuation body bound)
      (outerVariables : Finset Nat)
      (hbodyVariables : body.freeVariables ⊆ outerVariables) :
      CertifiedContextFiniteUniversalBranches
        ((valuationContext outerVariables valuation).image Rewriting.shift)
        (Rewriting.free body) bound :=
    match branches with
    | .nil _ _ => .nil
    | .snoc initial last =>
        let initialCompiled := compileBranches initial
          outerVariables hbodyVariables
        let lastRaw := compile last
        let lastProof := CertifiedPAContextProof.weakenContext lastRaw
          (freedFormulaValuationContext_subset_branch
            _ _ body outerVariables hbodyVariables)
        .snoc initialCompiled lastProof

end

theorem compile_certificate_valid
    {valuation : Nat -> Nat}
    {formula : ValuationFormula}
    (certificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula) :
    certificateValid
      (CheckedPAProofTree.ofDerivation certificate.compile.derivation)
      certificate.compile.certificate :=
  certificate.compile.certificate_valid

#print axioms compile
#print axioms compile_certificate_valid

end CheckedHybridValuationBoundedFormulaCertificate

end FoundationCompactPAHybridValuationBoundedFormulaCompiler
