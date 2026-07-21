import integration.FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate

/-!
# Explicit checked certificate for the halted verifier rows

The halted-row formula is built from the exact status-tag equality and an
explicit same-table token-slice certificate.  The latter materializes its
existential length witness and both bounded universal layers.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierHaltedRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierHaltedFormula
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
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
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
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

def compactNumericVerifierHaltedStatusEqClosedFormula
    (statusTag : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm statusTag) = 1”

def compactNumericVerifierHaltedRowsClosedFormula
    (tokenTable width tokenCount currentStart currentFinish currentStatusTag
      nextStart nextFinish : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierHaltedRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm currentStart,
      shortBinaryNumeralTerm currentFinish,
      shortBinaryNumeralTerm currentStatusTag,
      shortBinaryNumeralTerm nextStart,
      shortBinaryNumeralTerm nextFinish]

theorem compactNumericVerifierHaltedRowsClosedFormula_alignment
    (tokenTable width tokenCount currentStart currentFinish currentStatusTag
      nextStart nextFinish : Nat) :
    compactNumericVerifierHaltedRowsClosedFormula tokenTable width tokenCount
        currentStart currentFinish currentStatusTag nextStart nextFinish =
      compactNumericVerifierHaltedStatusEqClosedFormula currentStatusTag ⋏
        compactFixedWidthTokenSlicesEqClosedFormula tokenTable width tokenCount
          currentStart currentFinish nextStart nextFinish := by
  unfold compactNumericVerifierHaltedRowsClosedFormula
  unfold compactNumericVerifierHaltedStatusEqClosedFormula
  unfold compactNumericVerifierHaltedRowsDef
  unfold compactFixedWidthTokenSlicesEqClosedFormula
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

private noncomputable def haltedStatusEqExplicitHybridCertificate
    (statusTag : Nat) (hstatus : statusTag = 1) :
    HybridCertificate
      (compactNumericVerifierHaltedStatusEqClosedFormula statusTag) := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm statusTag, (‘1’ : ValuationTerm)] (by
      change termValue zeroValuation (shortBinaryNumeralTerm statusTag) =
        termValue zeroValuation (‘1’ : ValuationTerm)
      have hone : termValue zeroValuation (‘1’ : ValuationTerm) = 1 :=
        termValue_one zeroValuation ![]
      simpa [termValue_shortBinaryNumeralTerm, hone] using hstatus)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

/-- Explicit halted-row certificate on eight closed coordinates. -/
noncomputable def compactNumericVerifierHaltedRowsExplicitHybridCertificate
    (tokenTable width tokenCount currentStart currentFinish currentStatusTag
      nextStart nextFinish count : Nat)
    (hstatus : currentStatusTag = 1)
    (hcountBound : count ≤ tokenCount)
    (hcurrentEndpoint : currentFinish = currentStart + count)
    (hnextEndpoint : nextFinish = nextStart + count)
    (hcurrentFinishBound : currentFinish ≤ tokenCount)
    (hnextFinishBound : nextFinish ≤ tokenCount)
    (hbits : ∀ offset < count, ∀ bitIndex < width,
      tokenTable.testBit
          ((currentStart + offset) * width + bitIndex) =
        tokenTable.testBit
          ((nextStart + offset) * width + bitIndex)) :
    HybridCertificate
      (compactNumericVerifierHaltedRowsClosedFormula tokenTable width tokenCount
        currentStart currentFinish currentStatusTag nextStart nextFinish) := by
  rw [compactNumericVerifierHaltedRowsClosedFormula_alignment]
  exact .conjunction
    (haltedStatusEqExplicitHybridCertificate currentStatusTag hstatus)
    (compactFixedWidthTokenSlicesEqExplicitHybridCertificate
      tokenTable width tokenCount currentStart currentFinish nextStart nextFinish
      count hcountBound hcurrentEndpoint hnextEndpoint hcurrentFinishBound
      hnextFinishBound hbits)

/-- Close the halted-row formula directly from the original semantic graph. -/
noncomputable def
    compactNumericVerifierHaltedRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount currentStart currentFinish currentStatusTag
      nextStart nextFinish : Nat)
    (hgraph : CompactNumericVerifierHaltedRows
      tokenTable width tokenCount currentStart currentFinish currentStatusTag
        nextStart nextFinish) :
    HybridCertificate
      (compactNumericVerifierHaltedRowsClosedFormula tokenTable width tokenCount
        currentStart currentFinish currentStatusTag nextStart nextFinish) := by
  rcases hgraph with ⟨hstatus, hslice⟩
  let count := Classical.choose hslice
  have hsliceSpec := Classical.choose_spec hslice
  exact compactNumericVerifierHaltedRowsExplicitHybridCertificate
    tokenTable width tokenCount currentStart currentFinish currentStatusTag
    nextStart nextFinish count hstatus hsliceSpec.1 hsliceSpec.2.1
    hsliceSpec.2.2.1 hsliceSpec.2.2.2.1 hsliceSpec.2.2.2.2.1
    hsliceSpec.2.2.2.2.2

theorem compactNumericVerifierHaltedRowsAtEnvironmentFormula_eq_closed
    (values : Fin 429 -> Nat) :
    compactNumericVerifierHaltedRowsAtEnvironmentFormula values =
      compactNumericVerifierHaltedRowsClosedFormula
        (values 0) (values 1) (values 2) (values 3) (values 4)
        (values 15) (values 24) (values 25) := by
  unfold compactNumericVerifierHaltedRowsAtEnvironmentFormula
  unfold compactNumericVerifierStepHaltedTerms
  unfold compactNumericVerifierHaltedRowsClosedFormula
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

/-- The same explicit certificate in the exact 429-coordinate step
environment used by the halted branch. -/
noncomputable def
    compactNumericVerifierHaltedRowsAtEnvironmentExplicitHybridCertificate
    (values : Fin 429 -> Nat) (count : Nat)
    (hstatus : values 15 = 1)
    (hcountBound : count ≤ values 2)
    (hcurrentEndpoint : values 4 = values 3 + count)
    (hnextEndpoint : values 25 = values 24 + count)
    (hcurrentFinishBound : values 4 ≤ values 2)
    (hnextFinishBound : values 25 ≤ values 2)
    (hbits : ∀ offset < count, ∀ bitIndex < values 1,
      (values 0).testBit
          ((values 3 + offset) * values 1 + bitIndex) =
        (values 0).testBit
          ((values 24 + offset) * values 1 + bitIndex)) :
    HybridCertificate
      (compactNumericVerifierHaltedRowsAtEnvironmentFormula values) := by
  rw [compactNumericVerifierHaltedRowsAtEnvironmentFormula_eq_closed]
  exact compactNumericVerifierHaltedRowsExplicitHybridCertificate
    (values 0) (values 1) (values 2) (values 3) (values 4) (values 15)
    (values 24) (values 25) count hstatus hcountBound hcurrentEndpoint
    hnextEndpoint hcurrentFinishBound hnextFinishBound hbits

/-- The parameter-free halted-row constructor at the exact 429-coordinate
step environment. -/
noncomputable def
    compactNumericVerifierHaltedRowsAtEnvironmentExplicitHybridCertificateOfGraph
    (values : Fin 429 -> Nat)
    (hgraph : CompactNumericVerifierHaltedRows
      (values 0) (values 1) (values 2) (values 3) (values 4)
      (values 15) (values 24) (values 25)) :
    HybridCertificate
      (compactNumericVerifierHaltedRowsAtEnvironmentFormula values) := by
  rw [compactNumericVerifierHaltedRowsAtEnvironmentFormula_eq_closed]
  exact compactNumericVerifierHaltedRowsExplicitHybridCertificateOfGraph
    (values 0) (values 1) (values 2) (values 3) (values 4)
    (values 15) (values 24) (values 25) hgraph

#print axioms compactNumericVerifierHaltedRowsClosedFormula_alignment
#print axioms compactNumericVerifierHaltedRowsExplicitHybridCertificate
#print axioms
  compactNumericVerifierHaltedRowsExplicitHybridCertificateOfGraph
#print axioms compactNumericVerifierHaltedRowsAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierHaltedRowsAtEnvironmentExplicitHybridCertificate
#print axioms
  compactNumericVerifierHaltedRowsAtEnvironmentExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectVerifierHaltedRowsExplicitHybridCertificate
