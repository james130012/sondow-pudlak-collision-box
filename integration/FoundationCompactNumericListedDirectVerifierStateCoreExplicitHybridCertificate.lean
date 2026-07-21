import integration.FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate

/-!
# Explicit twelve-part assembly of a verifier state core

The closed state-core formula is exposed as its exact eleven common
components followed by an explicitly selected none/some status branch.  The
assembler accepts checked certificates for those immediate components only;
it never derives certificate data from semantic truth of the whole core.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierStateCoreExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierTerminalStepBranchExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev HybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

def compactNumericVerifierStateEnvironmentTerms
    (values : Fin 24 -> Nat) : Fin 24 -> ValuationTerm :=
  fun coordinate => shortBinaryNumeralTerm (values coordinate)

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

def compactNumericVerifierCurrentStateValues
    (values : Fin 429 -> Nat) : Fin 24 -> Nat :=
  ![values 0, values 1, values 2, values 3, values 4, values 5,
    values 6, values 7, values 8, values 9, values 10, values 11,
    values 12, values 13, values 14, values 15, values 16, values 17,
    values 18, values 19, values 20, values 21, values 22, values 23]

def compactNumericVerifierNextStateValues
    (values : Fin 429 -> Nat) : Fin 24 -> Nat :=
  ![values 0, values 1, values 2, values 24, values 25, values 26,
    values 27, values 28, values 29, values 30, values 31, values 32,
    values 33, values 34, values 35, values 36, values 37, values 38,
    values 39, values 40, values 41, values 42, values 43, values 44]

def compactNumericVerifierStateCoreAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierStateCoreGraphDef.val) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateProofSliceAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactAdditiveNatListSliceDef.val ⇜
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #3, #6, #5])) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateCertificateSliceAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactAdditiveNatListSliceDef.val ⇜
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #5, #8, #7])) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateTaskLayoutAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactAdditiveStructuredListLayoutDef.val ⇜
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #7, #10, #9, #11])) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateTaskRowsAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericVerifierTaskListRowsGraphDef.val ⇜
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #11, #10, #20, #21])) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateTaskBoundarySizeAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNatSizeDef.val ⇜
        ![(#18 : Semiterm ℒₒᵣ Empty 24), #11])) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateTaskBoundaryBoundRawFormula :
    ArithmeticSemiformula Empty 24 :=
  “#18 ≤ (#10 + 1) * #2”

def compactNumericVerifierStateTaskBoundaryBoundAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStateTaskBoundaryBoundRawFormula) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateValueLayoutAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactAdditiveStructuredListLayoutDef.val ⇜
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #9, #13, #12, #14])) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateValueRowsAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNumericChildResultListRowsGraphDef.val ⇜
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #14, #13, #22, #23])) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateValueBoundarySizeAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactNatSizeDef.val ⇜
        ![(#19 : Semiterm ℒₒᵣ Empty 24), #14])) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateValueBoundaryBoundRawFormula :
    ArithmeticSemiformula Empty 24 :=
  “#19 ≤ (#13 + 1) * #2”

def compactNumericVerifierStateValueBoundaryBoundAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStateValueBoundaryBoundRawFormula) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateOptionLayoutAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactAdditiveOptionLayoutDef.val ⇜
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #12, #15, #16, #4])) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateStatusTagZeroRawFormula :
    ArithmeticSemiformula Empty 24 := “#15 = 0”

def compactNumericVerifierStateStatusFinishEqRawFormula :
    ArithmeticSemiformula Empty 24 := “#4 = #16”

def compactNumericVerifierStateStatusTagOneRawFormula :
    ArithmeticSemiformula Empty 24 := “#15 = 1”

def compactNumericVerifierStateStatusTagZeroAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStateStatusTagZeroRawFormula) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateStatusFinishEqAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStateStatusFinishEqRawFormula) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateStatusTagOneAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStateStatusTagOneRawFormula) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      (compactAdditiveBoolSliceDef.val ⇜
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #16, #17, #4])) ⇜
    compactNumericVerifierStateEnvironmentTerms values

def compactNumericVerifierStateStatusAtEnvironmentFormula
    (values : Fin 24 -> Nat) : ValuationFormula :=
  (compactNumericVerifierStateStatusTagZeroAtEnvironmentFormula values ⋏
      compactNumericVerifierStateStatusFinishEqAtEnvironmentFormula values) ⋎
    (compactNumericVerifierStateStatusTagOneAtEnvironmentFormula values ⋏
      compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula values)

theorem compactNumericVerifierStateCoreAtEnvironmentFormula_eq_components
    (values : Fin 24 -> Nat) :
    compactNumericVerifierStateCoreAtEnvironmentFormula values =
      compactNumericVerifierStateProofSliceAtEnvironmentFormula values ⋏
      (compactNumericVerifierStateCertificateSliceAtEnvironmentFormula values ⋏
      (compactNumericVerifierStateTaskLayoutAtEnvironmentFormula values ⋏
      (compactNumericVerifierStateTaskRowsAtEnvironmentFormula values ⋏
      (compactNumericVerifierStateTaskBoundarySizeAtEnvironmentFormula values ⋏
      (compactNumericVerifierStateTaskBoundaryBoundAtEnvironmentFormula values ⋏
      (compactNumericVerifierStateValueLayoutAtEnvironmentFormula values ⋏
      (compactNumericVerifierStateValueRowsAtEnvironmentFormula values ⋏
      (compactNumericVerifierStateValueBoundarySizeAtEnvironmentFormula values ⋏
      (compactNumericVerifierStateValueBoundaryBoundAtEnvironmentFormula values ⋏
      (compactNumericVerifierStateOptionLayoutAtEnvironmentFormula values ⋏
        compactNumericVerifierStateStatusAtEnvironmentFormula values)))))))))) := by
  unfold compactNumericVerifierStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierStateProofSliceAtEnvironmentFormula
  unfold compactNumericVerifierStateCertificateSliceAtEnvironmentFormula
  unfold compactNumericVerifierStateTaskLayoutAtEnvironmentFormula
  unfold compactNumericVerifierStateTaskRowsAtEnvironmentFormula
  unfold compactNumericVerifierStateTaskBoundarySizeAtEnvironmentFormula
  unfold compactNumericVerifierStateTaskBoundaryBoundAtEnvironmentFormula
  unfold compactNumericVerifierStateTaskBoundaryBoundRawFormula
  unfold compactNumericVerifierStateValueLayoutAtEnvironmentFormula
  unfold compactNumericVerifierStateValueRowsAtEnvironmentFormula
  unfold compactNumericVerifierStateValueBoundarySizeAtEnvironmentFormula
  unfold compactNumericVerifierStateValueBoundaryBoundAtEnvironmentFormula
  unfold compactNumericVerifierStateValueBoundaryBoundRawFormula
  unfold compactNumericVerifierStateOptionLayoutAtEnvironmentFormula
  unfold compactNumericVerifierStateStatusAtEnvironmentFormula
  unfold compactNumericVerifierStateStatusTagZeroAtEnvironmentFormula
  unfold compactNumericVerifierStateStatusFinishEqAtEnvironmentFormula
  unfold compactNumericVerifierStateStatusTagOneAtEnvironmentFormula
  unfold compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula
  unfold compactNumericVerifierStateStatusTagZeroRawFormula
  unfold compactNumericVerifierStateStatusFinishEqRawFormula
  unfold compactNumericVerifierStateStatusTagOneRawFormula
  unfold compactNumericVerifierStateCoreGraphDef
  rfl

theorem compactNumericVerifierCurrentStateCoreAtEnvironmentFormula_eq_closed
    (values : Fin 429 -> Nat) :
    compactNumericVerifierCurrentStateCoreAtEnvironmentFormula values =
      compactNumericVerifierStateCoreAtEnvironmentFormula
        (compactNumericVerifierCurrentStateValues values) := by
  unfold compactNumericVerifierCurrentStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierParseCurrentStateTerms
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStepEnvironmentTerms,
        compactNumericVerifierStateEnvironmentTerms,
        compactNumericVerifierCurrentStateValues]
  · intro coordinate
    exact Empty.elim coordinate

theorem compactNumericVerifierNextStateCoreAtEnvironmentFormula_eq_closed
    (values : Fin 429 -> Nat) :
    compactNumericVerifierNextStateCoreAtEnvironmentFormula values =
      compactNumericVerifierStateCoreAtEnvironmentFormula
        (compactNumericVerifierNextStateValues values) := by
  unfold compactNumericVerifierNextStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierStateCoreAtEnvironmentFormula
  unfold compactNumericVerifierParseNextStateTerms
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar,
        compactNumericVerifierStepEnvironmentTerms,
        compactNumericVerifierStateEnvironmentTerms,
        compactNumericVerifierNextStateValues]
  · intro coordinate
    exact Empty.elim coordinate

structure CompactNumericVerifierStateCoreImmediateCertificates
    (valuation : Nat -> Nat) (values : Fin 24 -> Nat) where
  proofSlice : HybridCertificate valuation
    (compactNumericVerifierStateProofSliceAtEnvironmentFormula values)
  certificateSlice : HybridCertificate valuation
    (compactNumericVerifierStateCertificateSliceAtEnvironmentFormula values)
  taskLayout : HybridCertificate valuation
    (compactNumericVerifierStateTaskLayoutAtEnvironmentFormula values)
  taskRows : HybridCertificate valuation
    (compactNumericVerifierStateTaskRowsAtEnvironmentFormula values)
  taskBoundarySize : HybridCertificate valuation
    (compactNumericVerifierStateTaskBoundarySizeAtEnvironmentFormula values)
  taskBoundaryBound : HybridCertificate valuation
    (compactNumericVerifierStateTaskBoundaryBoundAtEnvironmentFormula values)
  valueLayout : HybridCertificate valuation
    (compactNumericVerifierStateValueLayoutAtEnvironmentFormula values)
  valueRows : HybridCertificate valuation
    (compactNumericVerifierStateValueRowsAtEnvironmentFormula values)
  valueBoundarySize : HybridCertificate valuation
    (compactNumericVerifierStateValueBoundarySizeAtEnvironmentFormula values)
  valueBoundaryBound : HybridCertificate valuation
    (compactNumericVerifierStateValueBoundaryBoundAtEnvironmentFormula values)
  optionLayout : HybridCertificate valuation
    (compactNumericVerifierStateOptionLayoutAtEnvironmentFormula values)

private noncomputable def compactNumericVerifierStateCoreCertificateOfStatus
    {valuation : Nat -> Nat} {values : Fin 24 -> Nat}
    (parts : CompactNumericVerifierStateCoreImmediateCertificates
      valuation values)
    (status : HybridCertificate valuation
      (compactNumericVerifierStateStatusAtEnvironmentFormula values)) :
    HybridCertificate valuation
      (compactNumericVerifierStateCoreAtEnvironmentFormula values) := by
  rw [compactNumericVerifierStateCoreAtEnvironmentFormula_eq_components]
  exact .conjunction parts.proofSlice
    (.conjunction parts.certificateSlice
    (.conjunction parts.taskLayout
    (.conjunction parts.taskRows
    (.conjunction parts.taskBoundarySize
    (.conjunction parts.taskBoundaryBound
    (.conjunction parts.valueLayout
    (.conjunction parts.valueRows
    (.conjunction parts.valueBoundarySize
    (.conjunction parts.valueBoundaryBound
    (.conjunction parts.optionLayout status))))))))))

/-- Assemble a state core whose option status is absent. -/
noncomputable def compactNumericVerifierStateCoreExplicitHybridCertificateOfNone
    {valuation : Nat -> Nat} {values : Fin 24 -> Nat}
    (parts : CompactNumericVerifierStateCoreImmediateCertificates
      valuation values)
    (tagZero : HybridCertificate valuation
      (compactNumericVerifierStateStatusTagZeroAtEnvironmentFormula values))
    (finishEq : HybridCertificate valuation
      (compactNumericVerifierStateStatusFinishEqAtEnvironmentFormula values)) :
    HybridCertificate valuation
      (compactNumericVerifierStateCoreAtEnvironmentFormula values) :=
  compactNumericVerifierStateCoreCertificateOfStatus parts
    (.disjunctionLeft (.conjunction tagZero finishEq))

/-- Assemble a state core whose option status contains a Boolean. -/
noncomputable def compactNumericVerifierStateCoreExplicitHybridCertificateOfSome
    {valuation : Nat -> Nat} {values : Fin 24 -> Nat}
    (parts : CompactNumericVerifierStateCoreImmediateCertificates
      valuation values)
    (tagOne : HybridCertificate valuation
      (compactNumericVerifierStateStatusTagOneAtEnvironmentFormula values))
    (boolSlice : HybridCertificate valuation
      (compactNumericVerifierStateStatusBoolSliceAtEnvironmentFormula values)) :
    HybridCertificate valuation
      (compactNumericVerifierStateCoreAtEnvironmentFormula values) :=
  compactNumericVerifierStateCoreCertificateOfStatus parts
    (.disjunctionRight (.conjunction tagOne boolSlice))

#print axioms compactNumericVerifierStateCoreAtEnvironmentFormula_eq_components
#print axioms
  compactNumericVerifierCurrentStateCoreAtEnvironmentFormula_eq_closed
#print axioms
  compactNumericVerifierNextStateCoreAtEnvironmentFormula_eq_closed
#print axioms compactNumericVerifierStateCoreExplicitHybridCertificateOfNone
#print axioms compactNumericVerifierStateCoreExplicitHybridCertificateOfSome

end FoundationCompactNumericListedDirectVerifierStateCoreExplicitHybridCertificate
