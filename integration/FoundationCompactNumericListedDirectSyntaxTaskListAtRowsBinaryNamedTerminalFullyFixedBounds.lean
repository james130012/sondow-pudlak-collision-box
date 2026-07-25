import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryBodyFullyFixedBounds

/-!
# Named binary syntax-task row terminal

The genuine three-leaf terminal certificate is named once and connected to
its fully fixed payload endpoint.  Downstream witness installation can import
the compiled object without re-elaborating the certificate tree.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedTerminalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

private theorem termValue_successorIndexTerm_binaryAtRowsNamed
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    termValue valuation (successorIndexTerm term) =
      termValue valuation term + 1 := by
  unfold successorIndexTerm
  rw [show
    (‘!!term + 1’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![term, (‘1’ : ValuationTerm)] by
        simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
          Rew.func, Matrix.fun_eq_vec_two]]
  calc
    termValue valuation
        (Semiterm.func Language.Add.add ![term, (‘1’ : ValuationTerm)]) =
      termValue valuation term +
        termValue valuation (‘1’ : ValuationTerm) :=
          termValue_add valuation ![term, (‘1’ : ValuationTerm)]
    _ = termValue valuation term + 1 := by
      rw [show termValue valuation (‘1’ : ValuationTerm) = 1 by
        exact termValue_one valuation ![]]

noncomputable def syntaxTaskAtRowsBinaryTerminalCertificateOfGraph
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0) :
    let left := Classical.choose hgraph.2
    let leftData := Classical.choose_spec hgraph.2
    let right := Classical.choose leftData.2
    let indexTerm := nativeNumeralTerm index
    let values : Fin 2 -> Nat := ![right, left]
    let body :=
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
        width tokenCount boundaryTable indexTerm (nativeNumeralTerm 1)
        (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)
    CheckedHybridValuationBoundedFormulaCertificate atRowsZeroValuation
      (body ⇜ fun coordinate =>
        shortBinaryNumeralTerm (values coordinate)) := by
  dsimp only
  let left := Classical.choose hgraph.2
  have hleftData := Classical.choose_spec hgraph.2
  let right := Classical.choose hleftData.2
  have hrightData := Classical.choose_spec hleftData.2
  let indexTerm : ValuationTerm := nativeNumeralTerm index
  let values : Fin 2 -> Nat := ![right, left]
  let body :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
      width tokenCount boundaryTable indexTerm (nativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (nativeNumeralTerm 0)
  let parts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm left) (by
          simpa only [indexTerm, termValue_shortBinaryNumeralTerm,
            termValue_nativeNumeralTerm] using hrightData.2.1))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          atRowsZeroValuation (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount) (successorIndexTerm indexTerm)
          (shortBinaryNumeralTerm right) (by
            simpa only [indexTerm, termValue_shortBinaryNumeralTerm,
              termValue_nativeNumeralTerm,
              termValue_successorIndexTerm_binaryAtRowsNamed] using
                hrightData.2.2.1))
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount left right 1 binderArity 0
          (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
          (nativeNumeralTerm 0) (termValue_nativeNumeralTerm · 1)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_nativeNumeralTerm · 0) hrightData.2.2.2))
  apply CheckedHybridValuationBoundedFormulaCertificate.cast _ parts
  have hvalueTerms :
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm right, shortBinaryNumeralTerm left] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [hvalueTerms]
  exact
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal_substitution_alignment
      tokenTable width tokenCount boundaryTable left right indexTerm
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0)).symm

theorem
    syntaxTaskAtRowsBinaryTerminalCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index binderArity
      numericBound bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index 1 binderArity 0)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (hcountValue : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTaskAtRowsBinaryTerminalCertificateOfGraph tokenTable width
          tokenCount boundaryTable count index binderArity hgraph) <=
      syntaxTaskAtRowsBinaryTerminalFullyFixedPayloadEnvelope
        (nativeNumeralTerm index) numericBound bitBound := by
  have h :=
    syntaxTaskAtRowsBinaryTerminalCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount boundaryTable count index binderArity
      numericBound bitBound hgraph hwidthValue htokenCountValue hcountValue
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hbinderSize
  change
    hybridFormulaStructuralPayloadBound
        (syntaxTaskAtRowsBinaryTerminalCertificateOfGraph tokenTable width
          tokenCount boundaryTable count index binderArity hgraph) <=
      syntaxTaskAtRowsBinaryTerminalFullyFixedPayloadEnvelope
        (nativeNumeralTerm index) numericBound bitBound at h
  exact h

#print axioms
  syntaxTaskAtRowsBinaryTerminalCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryNamedTerminalFullyFixedBounds
