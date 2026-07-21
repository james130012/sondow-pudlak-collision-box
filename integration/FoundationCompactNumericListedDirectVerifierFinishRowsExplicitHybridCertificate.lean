import integration.FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierChildResultListRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate

/-!
# Direct explicit certificate for verifier finish rows

This module opens the finish-row graph into its exact checked components.  The
public constructors consume only the original semantic finish-row graph; token
slice witnesses, the singleton child-result row, and the invalid-shape branch
are all materialized internally.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierFinishRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierFinishFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

def compactNumericVerifierFinishNumeralEqFormula
    (left right : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm left) =
    !!(shortBinaryNumeralTerm right)”

def compactNumericVerifierFinishFixedNumeralTerm
    (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

def compactNumericVerifierFinishFixedNumeralEqFormula
    (left right : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm left) =
    !!(compactNumericVerifierFinishFixedNumeralTerm right)”

def compactNumericVerifierFinishFixedNumeralNeFormula
    (left right : Nat) : ValuationFormula :=
  ∼compactNumericVerifierFinishFixedNumeralEqFormula left right

private theorem termValue_compactNumericVerifierFinishFixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation
      (compactNumericVerifierFinishFixedNumeralTerm value) = value := by
  unfold termValue compactNumericVerifierFinishFixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  simpa using
    (LO.FirstOrder.Structure.numeral_eq_numeral
      (L := ℒₒᵣ) (M := Nat) value)

def compactNumericVerifierFinishValidResultFormula
    (tokenTable width tokenCount currentProofCount currentCertificateCount
      currentTaskCount currentValueCount currentValueBoundary
      currentValueValueBound nextStatusBool : Nat) : ValuationFormula :=
  compactNumericVerifierFinishFixedNumeralEqFormula currentProofCount 0 ⋏
    (compactNumericVerifierFinishFixedNumeralEqFormula currentCertificateCount 0 ⋏
      (compactNumericVerifierFinishFixedNumeralEqFormula currentTaskCount 0 ⋏
        (compactNumericVerifierFinishFixedNumeralEqFormula currentValueCount 1 ⋏
          compactNumericChildResultBoundedRowWithBoolClosedFormula
            tokenTable width tokenCount currentValueBoundary
              currentValueValueBound 0 nextStatusBool)))

def compactNumericVerifierFinishInvalidShapeFormula
    (currentProofCount currentCertificateCount currentTaskCount
      currentValueCount : Nat) : ValuationFormula :=
  compactNumericVerifierFinishFixedNumeralNeFormula currentProofCount 0 ⋎
    (compactNumericVerifierFinishFixedNumeralNeFormula currentCertificateCount 0 ⋎
      (compactNumericVerifierFinishFixedNumeralNeFormula currentTaskCount 0 ⋎
        compactNumericVerifierFinishFixedNumeralNeFormula currentValueCount 1))

def compactNumericVerifierFinishInvalidResultFormula
    (currentProofCount currentCertificateCount currentTaskCount
      currentValueCount nextStatusBool : Nat) : ValuationFormula :=
  compactNumericVerifierFinishInvalidShapeFormula
      currentProofCount currentCertificateCount currentTaskCount
        currentValueCount ⋏
    compactNumericVerifierFinishFixedNumeralEqFormula nextStatusBool 0

def compactNumericVerifierFinishRowsClosedFormula
    (tokenTable width tokenCount
      currentStart currentValuesFinish
      currentProofCount currentCertificateCount currentTaskCount
      currentValueCount currentValueBoundary currentValueValueBound
      currentStatusTag
      nextStart nextValuesFinish
      nextProofCount nextCertificateCount nextTaskCount nextValueCount
      nextStatusTag nextStatusBool : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierFinishRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm currentStart,
      shortBinaryNumeralTerm currentValuesFinish,
      shortBinaryNumeralTerm currentProofCount,
      shortBinaryNumeralTerm currentCertificateCount,
      shortBinaryNumeralTerm currentTaskCount,
      shortBinaryNumeralTerm currentValueCount,
      shortBinaryNumeralTerm currentValueBoundary,
      shortBinaryNumeralTerm currentValueValueBound,
      shortBinaryNumeralTerm currentStatusTag,
      shortBinaryNumeralTerm nextStart,
      shortBinaryNumeralTerm nextValuesFinish,
      shortBinaryNumeralTerm nextProofCount,
      shortBinaryNumeralTerm nextCertificateCount,
      shortBinaryNumeralTerm nextTaskCount,
      shortBinaryNumeralTerm nextValueCount,
      shortBinaryNumeralTerm nextStatusTag,
      shortBinaryNumeralTerm nextStatusBool]

def compactNumericVerifierFinishRowsPartsFormula
    (tokenTable width tokenCount
      currentStart currentValuesFinish
      currentProofCount currentCertificateCount currentTaskCount
      currentValueCount currentValueBoundary currentValueValueBound
      currentStatusTag
      nextStart nextValuesFinish
      nextProofCount nextCertificateCount nextTaskCount nextValueCount
      nextStatusTag nextStatusBool : Nat) : ValuationFormula :=
  compactNumericVerifierFinishFixedNumeralEqFormula currentStatusTag 0 ⋏
    (compactNumericVerifierFinishFixedNumeralEqFormula currentTaskCount 0 ⋏
      (compactFixedWidthTokenSlicesEqClosedFormula
          tokenTable width tokenCount currentStart currentValuesFinish
            nextStart nextValuesFinish ⋏
        (compactNumericVerifierFinishNumeralEqFormula
            nextProofCount currentProofCount ⋏
          (compactNumericVerifierFinishNumeralEqFormula
              nextCertificateCount currentCertificateCount ⋏
            (compactNumericVerifierFinishNumeralEqFormula
                nextTaskCount currentTaskCount ⋏
                (compactNumericVerifierFinishNumeralEqFormula
                  nextValueCount currentValueCount ⋏
                (compactNumericVerifierFinishFixedNumeralEqFormula
                    nextStatusTag 1 ⋏
                  (compactNumericVerifierFinishValidResultFormula
                      tokenTable width tokenCount currentProofCount
                        currentCertificateCount currentTaskCount
                        currentValueCount currentValueBoundary
                        currentValueValueBound nextStatusBool ⋎
                    compactNumericVerifierFinishInvalidResultFormula
                      currentProofCount currentCertificateCount
                        currentTaskCount currentValueCount
                        nextStatusBool))))))))

theorem compactNumericVerifierFinishRowsClosedFormula_alignment
    (tokenTable width tokenCount
      currentStart currentValuesFinish
      currentProofCount currentCertificateCount currentTaskCount
      currentValueCount currentValueBoundary currentValueValueBound
      currentStatusTag
      nextStart nextValuesFinish
      nextProofCount nextCertificateCount nextTaskCount nextValueCount
      nextStatusTag nextStatusBool : Nat) :
    compactNumericVerifierFinishRowsClosedFormula
        tokenTable width tokenCount currentStart currentValuesFinish
        currentProofCount currentCertificateCount currentTaskCount
        currentValueCount currentValueBoundary currentValueValueBound
        currentStatusTag nextStart nextValuesFinish nextProofCount
        nextCertificateCount nextTaskCount nextValueCount nextStatusTag
        nextStatusBool =
      compactNumericVerifierFinishRowsPartsFormula
        tokenTable width tokenCount currentStart currentValuesFinish
        currentProofCount currentCertificateCount currentTaskCount
        currentValueCount currentValueBoundary currentValueValueBound
        currentStatusTag nextStart nextValuesFinish nextProofCount
        nextCertificateCount nextTaskCount nextValueCount nextStatusTag
        nextStatusBool := by
  unfold compactNumericVerifierFinishRowsClosedFormula
  unfold compactNumericVerifierFinishRowsPartsFormula
  unfold compactNumericVerifierFinishValidResultFormula
  unfold compactNumericVerifierFinishInvalidResultFormula
  unfold compactNumericVerifierFinishInvalidShapeFormula
  unfold compactNumericVerifierFinishNumeralEqFormula
  unfold compactNumericVerifierFinishFixedNumeralEqFormula
  unfold compactNumericVerifierFinishFixedNumeralNeFormula
  unfold compactNumericVerifierFinishFixedNumeralTerm
  unfold compactNumericVerifierFinishRowsDef
  simp [compactFixedWidthTokenSlicesEqClosedFormula,
    compactNumericChildResultBoundedRowWithBoolClosedFormula,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  case right.left =>
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, Rew.const,
          Semiterm.Operator.numeral_zero,
          Semiterm.Operator.Zero.term_eq,
          Function.comp_def, shortBinaryNumeralTerm,
          FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
          Semiterm.Operator.operator]
      all_goals
        funext index
        exact Fin.elim0 index
    · intro coordinate
      exact Empty.elim coordinate
  all_goals
    first
    | apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, shortBinaryNumeralTerm,
            FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
            Semiterm.Operator.operator]
      · intro coordinate
        exact Empty.elim coordinate
    | congr 1 <;> congr 1 <;>
        first
        | apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [Rew.comp_app, Rew.subst_bvar]
          · intro coordinate
            exact Empty.elim coordinate
        | simp [shortBinaryNumeralTerm,
            FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
            Semiterm.Operator.operator]

private noncomputable def compactNumericVerifierFinishNumeralEqCertificate
    (left right : Nat) (heq : left = right) :
    HybridCertificate
      (compactNumericVerifierFinishNumeralEqFormula left right) := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) =
        termValue zeroValuation (shortBinaryNumeralTerm right)
      simpa only [termValue_shortBinaryNumeralTerm] using heq)
  unfold compactNumericVerifierFinishNumeralEqFormula
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def compactNumericVerifierFinishFixedNumeralEqCertificate
    (left right : Nat) (heq : left = right) :
    HybridCertificate
      (compactNumericVerifierFinishFixedNumeralEqFormula left right) := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm left,
      compactNumericVerifierFinishFixedNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) =
        termValue zeroValuation
          (compactNumericVerifierFinishFixedNumeralTerm right)
      simpa only [termValue_shortBinaryNumeralTerm,
        termValue_compactNumericVerifierFinishFixedNumeralTerm] using heq)
  unfold compactNumericVerifierFinishFixedNumeralEqFormula
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def compactNumericVerifierFinishFixedNumeralNeCertificate
    (left right : Nat) (hne : left ≠ right) :
    HybridCertificate
      (compactNumericVerifierFinishFixedNumeralNeFormula left right) := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm left,
      compactNumericVerifierFinishFixedNumeralTerm right] (by
      change ¬termValue zeroValuation (shortBinaryNumeralTerm left) =
        termValue zeroValuation
          (compactNumericVerifierFinishFixedNumeralTerm right)
      simpa only [termValue_shortBinaryNumeralTerm,
        termValue_compactNumericVerifierFinishFixedNumeralTerm] using hne)
  unfold compactNumericVerifierFinishFixedNumeralNeFormula
  unfold compactNumericVerifierFinishFixedNumeralEqFormula
  exact .cast
    (congrArg (fun formula : ValuationFormula => ∼formula)
      (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm) direct

private noncomputable def compactNumericVerifierFinishValidResultCertificate
    (tokenTable width tokenCount currentProofCount currentCertificateCount
      currentTaskCount currentValueCount currentValueBoundary
      currentValueValueBound nextStatusBool : Nat)
    (hvalid : currentProofCount = 0 ∧
      currentCertificateCount = 0 ∧
      currentTaskCount = 0 ∧
      currentValueCount = 1 ∧
      CompactNumericChildResultBoundedRowWithBool
        tokenTable width tokenCount currentValueBoundary
          currentValueValueBound 0 nextStatusBool) :
    HybridCertificate
      (compactNumericVerifierFinishValidResultFormula
        tokenTable width tokenCount currentProofCount currentCertificateCount
        currentTaskCount currentValueCount currentValueBoundary
        currentValueValueBound nextStatusBool) := by
  rcases hvalid with ⟨hproof, hcertificate, htask, hvalue, hrow⟩
  exact .conjunction
    (compactNumericVerifierFinishFixedNumeralEqCertificate
      currentProofCount 0 hproof)
    (.conjunction
      (compactNumericVerifierFinishFixedNumeralEqCertificate
        currentCertificateCount 0 hcertificate)
      (.conjunction
        (compactNumericVerifierFinishFixedNumeralEqCertificate
          currentTaskCount 0 htask)
        (.conjunction
          (compactNumericVerifierFinishFixedNumeralEqCertificate
            currentValueCount 1 hvalue)
          (compactNumericChildResultBoundedRowWithBoolExplicitHybridCertificate
            tokenTable width tokenCount currentValueBoundary
              currentValueValueBound 0 nextStatusBool hrow))))

private noncomputable def compactNumericVerifierFinishInvalidShapeCertificate
    (currentProofCount currentCertificateCount currentTaskCount
      currentValueCount : Nat)
    (hshape : currentProofCount ≠ 0 ∨
      currentCertificateCount ≠ 0 ∨
      currentTaskCount ≠ 0 ∨
      currentValueCount ≠ 1) :
    HybridCertificate
      (compactNumericVerifierFinishInvalidShapeFormula
        currentProofCount currentCertificateCount currentTaskCount
          currentValueCount) := by
  if hproof : currentProofCount ≠ 0 then
    exact .disjunctionLeft
      (compactNumericVerifierFinishFixedNumeralNeCertificate
        currentProofCount 0 hproof)
  else if hcertificate : currentCertificateCount ≠ 0 then
    exact .disjunctionRight (.disjunctionLeft
      (compactNumericVerifierFinishFixedNumeralNeCertificate
        currentCertificateCount 0 hcertificate))
  else if htask : currentTaskCount ≠ 0 then
    exact .disjunctionRight (.disjunctionRight (.disjunctionLeft
      (compactNumericVerifierFinishFixedNumeralNeCertificate
        currentTaskCount 0 htask)))
  else
    have hvalue : currentValueCount ≠ 1 := by
      rcases hshape with hproof' | hcertificate' | htask' | hvalue'
      · exact False.elim (hproof hproof')
      · exact False.elim (hcertificate hcertificate')
      · exact False.elim (htask htask')
      · exact hvalue'
    exact .disjunctionRight (.disjunctionRight (.disjunctionRight
      (compactNumericVerifierFinishFixedNumeralNeCertificate
        currentValueCount 1 hvalue)))

private noncomputable def compactNumericVerifierFinishInvalidResultCertificate
    (currentProofCount currentCertificateCount currentTaskCount
      currentValueCount nextStatusBool : Nat)
    (hinvalid :
      (currentProofCount ≠ 0 ∨
        currentCertificateCount ≠ 0 ∨
        currentTaskCount ≠ 0 ∨
        currentValueCount ≠ 1) ∧
      nextStatusBool = 0) :
    HybridCertificate
      (compactNumericVerifierFinishInvalidResultFormula
        currentProofCount currentCertificateCount currentTaskCount
          currentValueCount nextStatusBool) :=
  .conjunction
    (compactNumericVerifierFinishInvalidShapeCertificate
      currentProofCount currentCertificateCount currentTaskCount
        currentValueCount hinvalid.1)
    (compactNumericVerifierFinishFixedNumeralEqCertificate
      nextStatusBool 0 hinvalid.2)

/-- Close the exact finish-row formula from its original semantic graph. -/
noncomputable def compactNumericVerifierFinishRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount
      currentStart currentValuesFinish
      currentProofCount currentCertificateCount currentTaskCount
      currentValueCount currentValueBoundary currentValueValueBound
      currentStatusTag
      nextStart nextValuesFinish
      nextProofCount nextCertificateCount nextTaskCount nextValueCount
      nextStatusTag nextStatusBool : Nat)
    (hgraph : CompactNumericVerifierFinishRows
      tokenTable width tokenCount currentStart currentValuesFinish
      currentProofCount currentCertificateCount currentTaskCount
      currentValueCount currentValueBoundary currentValueValueBound
      currentStatusTag nextStart nextValuesFinish nextProofCount
      nextCertificateCount nextTaskCount nextValueCount nextStatusTag
      nextStatusBool) :
    HybridCertificate
      (compactNumericVerifierFinishRowsClosedFormula
        tokenTable width tokenCount currentStart currentValuesFinish
        currentProofCount currentCertificateCount currentTaskCount
        currentValueCount currentValueBoundary currentValueValueBound
        currentStatusTag nextStart nextValuesFinish nextProofCount
        nextCertificateCount nextTaskCount nextValueCount nextStatusTag
        nextStatusBool) := by
  rw [compactNumericVerifierFinishRowsClosedFormula_alignment]
  rcases hgraph with
    ⟨hstatus, htaskZero, hslice, hproof, hcertificate, htask, hvalue,
      hnextStatus, hresult⟩
  let sliceCount := Classical.choose hslice
  have hsliceSpec := Classical.choose_spec hslice
  let sliceCertificate :=
    compactFixedWidthTokenSlicesEqExplicitHybridCertificate
      tokenTable width tokenCount currentStart currentValuesFinish
      nextStart nextValuesFinish sliceCount hsliceSpec.1 hsliceSpec.2.1
      hsliceSpec.2.2.1 hsliceSpec.2.2.2.1 hsliceSpec.2.2.2.2.1
      hsliceSpec.2.2.2.2.2
  let resultCertificate : HybridCertificate
      (compactNumericVerifierFinishValidResultFormula
          tokenTable width tokenCount currentProofCount
            currentCertificateCount currentTaskCount currentValueCount
            currentValueBoundary currentValueValueBound nextStatusBool ⋎
        compactNumericVerifierFinishInvalidResultFormula
          currentProofCount currentCertificateCount currentTaskCount
            currentValueCount nextStatusBool) := by
    classical
    if hvalid : currentProofCount = 0 ∧
        currentCertificateCount = 0 ∧
        currentTaskCount = 0 ∧
        currentValueCount = 1 ∧
        CompactNumericChildResultBoundedRowWithBool
          tokenTable width tokenCount currentValueBoundary
            currentValueValueBound 0 nextStatusBool then
      exact .disjunctionLeft
        (compactNumericVerifierFinishValidResultCertificate
          tokenTable width tokenCount currentProofCount
          currentCertificateCount currentTaskCount currentValueCount
          currentValueBoundary currentValueValueBound nextStatusBool hvalid)
    else
      have hinvalid :
          (currentProofCount ≠ 0 ∨
            currentCertificateCount ≠ 0 ∨
            currentTaskCount ≠ 0 ∨
            currentValueCount ≠ 1) ∧
          nextStatusBool = 0 := by
        rcases hresult with hvalid' | hinvalid'
        · exact False.elim (hvalid hvalid')
        · exact hinvalid'
      exact .disjunctionRight
        (compactNumericVerifierFinishInvalidResultCertificate
          currentProofCount currentCertificateCount currentTaskCount
          currentValueCount nextStatusBool hinvalid)
  exact .conjunction
    (compactNumericVerifierFinishFixedNumeralEqCertificate
      currentStatusTag 0 hstatus)
    (.conjunction
      (compactNumericVerifierFinishFixedNumeralEqCertificate
        currentTaskCount 0 htaskZero)
      (.conjunction sliceCertificate
        (.conjunction
          (compactNumericVerifierFinishNumeralEqCertificate
            nextProofCount currentProofCount hproof)
          (.conjunction
            (compactNumericVerifierFinishNumeralEqCertificate
              nextCertificateCount currentCertificateCount hcertificate)
            (.conjunction
              (compactNumericVerifierFinishNumeralEqCertificate
                nextTaskCount currentTaskCount htask)
              (.conjunction
                (compactNumericVerifierFinishNumeralEqCertificate
                  nextValueCount currentValueCount hvalue)
                (.conjunction
                  (compactNumericVerifierFinishFixedNumeralEqCertificate
                    nextStatusTag 1 hnextStatus)
                  resultCertificate)))))))

theorem compactNumericVerifierFinishRowsAtEnvironmentFormula_eq_closed
    (values : Fin 429 -> Nat) :
    compactNumericVerifierFinishRowsAtEnvironmentFormula values =
      compactNumericVerifierFinishRowsClosedFormula
        (values 0) (values 1) (values 2) (values 3) (values 12)
        (values 6) (values 8) (values 10) (values 13) (values 14)
        (values 23) (values 15) (values 24) (values 33) (values 27)
        (values 29) (values 31) (values 34) (values 36) (values 38) := by
  unfold compactNumericVerifierFinishRowsAtEnvironmentFormula
  unfold compactNumericVerifierStepFinishTerms
  unfold compactNumericVerifierFinishRowsClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStepEnvironmentTerms]
  · intro coordinate
    exact Empty.elim coordinate

/-- The direct finish-row certificate in the exact 429-coordinate step
environment. -/
noncomputable def
    compactNumericVerifierFinishRowsAtEnvironmentExplicitHybridCertificateOfGraph
    (values : Fin 429 -> Nat)
    (hgraph : CompactNumericVerifierFinishRows
      (values 0) (values 1) (values 2) (values 3) (values 12)
      (values 6) (values 8) (values 10) (values 13) (values 14)
      (values 23) (values 15) (values 24) (values 33) (values 27)
      (values 29) (values 31) (values 34) (values 36) (values 38)) :
    HybridCertificate
      (compactNumericVerifierFinishRowsAtEnvironmentFormula values) := by
  rw [compactNumericVerifierFinishRowsAtEnvironmentFormula_eq_closed]
  exact compactNumericVerifierFinishRowsExplicitHybridCertificateOfGraph
    (values 0) (values 1) (values 2) (values 3) (values 12)
    (values 6) (values 8) (values 10) (values 13) (values 14)
    (values 23) (values 15) (values 24) (values 33) (values 27)
    (values 29) (values 31) (values 34) (values 36) (values 38) hgraph

#print axioms compactNumericVerifierFinishRowsClosedFormula_alignment
#print axioms compactNumericVerifierFinishRowsExplicitHybridCertificateOfGraph
#print axioms compactNumericVerifierFinishRowsAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierFinishRowsAtEnvironmentExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectVerifierFinishRowsExplicitHybridCertificate
