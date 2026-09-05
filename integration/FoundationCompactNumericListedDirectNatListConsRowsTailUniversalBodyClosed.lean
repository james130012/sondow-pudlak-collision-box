import integration.FoundationCompactNumericListedDirectNatListConsRowsTailSourceTerminalClosed
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyDefinitions
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds

/-! # The one-variable cons-tail universal body has no free variables -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 140000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyClosed

open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailSourceTerminalClosed
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyDefinitions

theorem compactAdditiveNatListConsRowsTailBody_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary).freeVariables = ∅ := by
  let terminal := compactAdditiveNatListConsRowsTailTerminal tokenTable width
    tokenCount sourceBoundary targetBoundary
  let body04 := natListConsRowsTailBodyAfter04 tokenTable width tokenCount
    sourceBoundary targetBoundary
  let body03 := natListConsRowsTailBodyAfter03 tokenTable width tokenCount
    sourceBoundary targetBoundary
  let body02 := natListConsRowsTailBodyAfter02 tokenTable width tokenCount
    sourceBoundary targetBoundary
  have hterminal : terminal.freeVariables = ∅ := by
    dsimp only [terminal]
    exact
      compactAdditiveNatListConsRowsTailSourceTerminal_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary targetBoundary
  have h04subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount terminal
  have h04 : body04.freeVariables = ∅ := by
    apply Finset.subset_empty.mp
    dsimp only [body04, natListConsRowsTailBodyAfter04]
    exact h04subset.trans (by rw [hterminal])
  have h03subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount body04
  have h03 : body03.freeVariables = ∅ := by
    apply Finset.subset_empty.mp
    dsimp only [body03, natListConsRowsTailBodyAfter03]
    exact h03subset.trans (by rw [h04])
  have h02subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount body03
  have h02 : body02.freeVariables = ∅ := by
    apply Finset.subset_empty.mp
    dsimp only [body02, natListConsRowsTailBodyAfter02]
    exact h02subset.trans (by rw [h03])
  have h01subset :=
    explicitBoundedWitnessRecursiveBody_freeVariables_subset tokenCount body02
  have h01 :
      (natListConsRowsTailBodyAfter01 tokenTable width tokenCount
        sourceBoundary targetBoundary).freeVariables = ∅ := by
    apply Finset.subset_empty.mp
    dsimp only [natListConsRowsTailBodyAfter01]
    exact h01subset.trans (by rw [h02])
  rw [compactAdditiveNatListConsRowsTailBody_eq_after01]
  exact h01

#print axioms compactAdditiveNatListConsRowsTailBody_freeVariables_eq_empty

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyClosed
