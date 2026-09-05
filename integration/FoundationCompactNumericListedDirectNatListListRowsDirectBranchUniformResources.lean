import integration.FoundationCompactNumericListedDirectNatListSliceUniformDirectBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedProof
import integration.FoundationCompactPAValuationContextSingletonCodeBound
import integration.FoundationCompactPAFreeFormulaVariableTransport

/-! # Row-independent resources for additive natural-list-list rows -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectNatListListRowsDirectBranchUniformResources

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationContextSingletonCodeBound
open FoundationCompactPAFreeFormulaVariableTransport
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFixedBounds
open FoundationCompactNumericListedDirectNatListSliceUniformDirectBound

def compactAdditiveNatListListRowsIndexCodeBound : Nat :=
  (binaryTermCode (&0 : ValuationTerm)).length +
    (binaryTermCode (‘&0 + 1’ : ValuationTerm)).length + 1

def compactAdditiveNatListListRowsEntryPayloadResource
    (numericBound bitBound : Nat) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayloadPolynomial numericBound
    bitBound compactAdditiveNatListListRowsIndexCodeBound

def compactAdditiveNatListListRowsSlicePayloadResource
    (numericBound bitBound : Nat) : Nat :=
  compactAdditiveNatListSliceUniformDirectPayloadResource numericBound bitBound

def compactAdditiveNatListListRowsContextCodeResource
    (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length

def compactAdditiveNatListListRowsTerminalSyntaxResource
    (numericBound bitBound : Nat) : Nat :=
  compactAdditiveNatListListRowsContextCodeResource numericBound +
    2 * compactAdditiveNatListListRowsEntryPayloadResource numericBound
      bitBound +
    compactAdditiveNatListListRowsSlicePayloadResource numericBound bitBound +
    2 * (binaryNatCode 4).length + 1

def compactAdditiveNatListListRowsTerminalInnerPayloadResource
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactAdditiveNatListListRowsTerminalSyntaxResource numericBound bitBound)
    (compactAdditiveNatListListRowsEntryPayloadResource numericBound bitBound)
    (compactAdditiveNatListListRowsSlicePayloadResource numericBound bitBound)

def compactAdditiveNatListListRowsTerminalPayloadResource
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactAdditiveNatListListRowsTerminalSyntaxResource numericBound bitBound)
    (compactAdditiveNatListListRowsEntryPayloadResource numericBound bitBound)
    (compactAdditiveNatListListRowsTerminalInnerPayloadResource numericBound
      bitBound)

def compactAdditiveNatListListRowsBranchPayloadResource
    (tokenTable width tokenCount boundaryTable numericBound bitBound : Nat) :
    Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 3
    (compactAdditiveNatListListRowsContextCodeResource numericBound)
    numericBound
    (binaryFormulaCode
      (compactAdditiveNatListListRowsBranchTerminal tokenTable width tokenCount
        boundaryTable)).length
    (compactAdditiveNatListListRowsTerminalPayloadResource numericBound bitBound)

private theorem shiftedShortNumeral_freeVariables_subset_singleton
    (depth value : Nat) :
    (closedShift depth (shortBinaryNumeralTerm value)).freeVariables ⊆ {0} := by
  induction depth with
  | zero =>
      rw [show closedShift 0 (shortBinaryNumeralTerm value) =
        shortBinaryNumeralTerm value by rfl]
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
      simp
  | succ depth inductionHypothesis =>
      simp only [closedShift]
      rw [bShiftTerm_freeVariables_eq]
      exact inductionHypothesis

private theorem shiftedIndex_freeVariables_subset_singleton
    (depth : Nat) :
    (closedShift depth (&0 : ValuationTerm)).freeVariables ⊆ {0} := by
  induction depth with
  | zero => simp [closedShift]
  | succ depth inductionHypothesis =>
      simp only [closedShift]
      rw [bShiftTerm_freeVariables_eq]
      exact inductionHypothesis

private theorem shiftedIndexSuccessor_freeVariables_subset_singleton
    (depth : Nat) :
    (closedShift depth (‘&0 + 1’ : ValuationTerm)).freeVariables ⊆ {0} := by
  induction depth with
  | zero =>
      rw [show closedShift 0 (‘&0 + 1’ : ValuationTerm) =
        (‘&0 + 1’ : ValuationTerm) by rfl]
      rw [arithmeticAddTerm_freeVariables_eq_union]
      simp
  | succ depth inductionHypothesis =>
      simp only [closedShift]
      rw [bShiftTerm_freeVariables_eq]
      exact inductionHypothesis

private theorem boundVariable_freeVariables_subset_singleton
    {arity : Nat} (coordinate : Fin arity) :
    (#coordinate : ArithmeticSemiterm Nat arity).freeVariables ⊆ {0} := by
  simp

theorem
    compactAdditiveNatListListRowsBranchTerminal_freeVariables_subset_singleton
    (tokenTable width tokenCount boundaryTable : Nat) :
    (compactAdditiveNatListListRowsBranchTerminal tokenTable width tokenCount
      boundaryTable).freeVariables ⊆ {0} := by
  let leftTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![closedShift 3 (shortBinaryNumeralTerm boundaryTable),
      closedShift 3 (shortBinaryNumeralTerm tokenCount),
      closedShift 3 (&0 : ValuationTerm), #2]
  let rightTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![closedShift 3 (shortBinaryNumeralTerm boundaryTable),
      closedShift 3 (shortBinaryNumeralTerm tokenCount),
      closedShift 3 (‘&0 + 1’ : ValuationTerm), #1]
  let sliceTerms : Fin 6 -> ArithmeticSemiterm Nat 3 :=
    ![closedShift 3 (shortBinaryNumeralTerm tokenTable),
      closedShift 3 (shortBinaryNumeralTerm width),
      closedShift 3 (shortBinaryNumeralTerm tokenCount), #2, #0, #1]
  let leftFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ leftTerms
  let rightFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ rightTerms
  let sliceFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveNatListSliceDef.val) ⇜ sliceTerms
  have hleft : leftFormula.freeVariables ⊆ {0} := by
    dsimp only [leftFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact shiftedShortNumeral_freeVariables_subset_singleton 3 boundaryTable
    · exact shiftedShortNumeral_freeVariables_subset_singleton 3 tokenCount
    · exact shiftedIndex_freeVariables_subset_singleton 3
    · exact boundVariable_freeVariables_subset_singleton 2
  have hright : rightFormula.freeVariables ⊆ {0} := by
    dsimp only [rightFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact shiftedShortNumeral_freeVariables_subset_singleton 3 boundaryTable
    · exact shiftedShortNumeral_freeVariables_subset_singleton 3 tokenCount
    · exact shiftedIndexSuccessor_freeVariables_subset_singleton 3
    · exact boundVariable_freeVariables_subset_singleton 1
  have hslice : sliceFormula.freeVariables ⊆ {0} := by
    dsimp only [sliceFormula]
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact shiftedShortNumeral_freeVariables_subset_singleton 3 tokenTable
    · exact shiftedShortNumeral_freeVariables_subset_singleton 3 width
    · exact shiftedShortNumeral_freeVariables_subset_singleton 3 tokenCount
    · exact boundVariable_freeVariables_subset_singleton 2
    · exact boundVariable_freeVariables_subset_singleton 0
    · exact boundVariable_freeVariables_subset_singleton 1
  unfold compactAdditiveNatListListRowsBranchTerminal
  change (leftFormula ⋏ (rightFormula ⋏ sliceFormula)).freeVariables ⊆ {0}
  simp only [LO.FirstOrder.Semiformula.freeVariables_and]
  exact Finset.union_subset hleft (Finset.union_subset hright hslice)

private theorem closedShift_freeVariables_eq_empty
    (depth : Nat) (term : ValuationTerm)
    (hterm : term.freeVariables = ∅) :
    (closedShift depth term).freeVariables = ∅ := by
  induction depth with
  | zero => simpa [closedShift]
  | succ depth inductionHypothesis =>
      simp only [closedShift]
      exact bShift_freeVariables_eq_empty_of_empty _ inductionHypothesis

private theorem arithmeticOne_freeVariables_eq_empty
    {arity : Nat} :
    (‘1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem bexsLTSucc_freeVariables_eq_empty_of_empty
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity)
    (hbody : body.freeVariables = ∅)
    (hbound : bound.freeVariables = ∅) :
    (body.bexsLTSucc bound).freeVariables = ∅ := by
  have hsuccessor :
      (‘!!bound + 1’ : ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
    rw [arithmeticAddTerm_freeVariables_eq_union, hbound,
      arithmeticOne_freeVariables_eq_empty]
    simp
  have hshifted :
      (Rew.bShift
        (‘!!bound + 1’ : ArithmeticSemiterm Nat arity)).freeVariables = ∅ :=
    bShift_freeVariables_eq_empty_of_empty _ hsuccessor
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT LO.FirstOrder.bexs
  rw [LO.FirstOrder.Semiformula.freeVariables_exs,
    LO.FirstOrder.Semiformula.freeVariables_and,
    lessThanFormula_freeVariables, hshifted, hbody]
  simp

theorem compactAdditiveNatListListRowsTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable : Nat) :
    (compactAdditiveNatListListRowsTerminal tokenTable width tokenCount
      boundaryTable).freeVariables = ∅ := by
  let leftTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm boundaryTable),
      closedShift 4 (shortBinaryNumeralTerm tokenCount), #3, #2]
  let rightTerms : Fin 4 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm boundaryTable),
      closedShift 4 (shortBinaryNumeralTerm tokenCount), ‘#3 + 1’, #1]
  let sliceTerms : Fin 6 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
      closedShift 4 (shortBinaryNumeralTerm width),
      closedShift 4 (shortBinaryNumeralTerm tokenCount), #2, #0, #1]
  let leftFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ leftTerms
  let rightFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ rightTerms
  let sliceFormula : ArithmeticSemiformula Nat 4 :=
    (Rewriting.emb (ξ := Nat) compactAdditiveNatListSliceDef.val) ⇜ sliceTerms
  have hleftTerms : forall coordinate,
      (leftTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact closedShift_freeVariables_eq_empty 4 _
        (shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable)
    · exact closedShift_freeVariables_eq_empty 4 _
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
    · simp [leftTerms]
    · simp [leftTerms]
  have hrightTerms : forall coordinate,
      (rightTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact closedShift_freeVariables_eq_empty 4 _
        (shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable)
    · exact closedShift_freeVariables_eq_empty 4 _
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
    · change (‘#3 + 1’ : ArithmeticSemiterm Nat 4).freeVariables = ∅
      rw [arithmeticAddTerm_freeVariables_eq_union,
        arithmeticOne_freeVariables_eq_empty]
      simp
    · simp [rightTerms]
  have hsliceTerms : forall coordinate,
      (sliceTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact closedShift_freeVariables_eq_empty 4 _
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
    · exact closedShift_freeVariables_eq_empty 4 _
        (shortBinaryNumeralTerm_freeVariables_eq_empty width)
    · exact closedShift_freeVariables_eq_empty 4 _
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
    · simp [sliceTerms]
    · simp [sliceTerms]
    · simp [sliceTerms]
  have hleft : leftFormula.freeVariables = ∅ :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactFixedWidthEntryDef.val leftTerms hleftTerms
  have hright : rightFormula.freeVariables = ∅ :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactFixedWidthEntryDef.val rightTerms hrightTerms
  have hslice : sliceFormula.freeVariables = ∅ :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactAdditiveNatListSliceDef.val sliceTerms hsliceTerms
  unfold compactAdditiveNatListListRowsTerminal
  change (leftFormula ⋏ (rightFormula ⋏ sliceFormula)).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_and, hleft, hright, hslice]
  simp

theorem compactAdditiveNatListListRowsBody_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable : Nat) :
    (compactAdditiveNatListListRowsBody tokenTable width tokenCount
      boundaryTable).freeVariables = ∅ := by
  let terminal := compactAdditiveNatListListRowsTerminal tokenTable width
    tokenCount boundaryTable
  let bound3 := closedShift 3 (shortBinaryNumeralTerm tokenCount)
  let bound2 := closedShift 2 (shortBinaryNumeralTerm tokenCount)
  let bound1 := closedShift 1 (shortBinaryNumeralTerm tokenCount)
  have hterminal : terminal.freeVariables = ∅ :=
    compactAdditiveNatListListRowsTerminal_freeVariables_eq_empty tokenTable
      width tokenCount boundaryTable
  have hbound3 : bound3.freeVariables = ∅ :=
    closedShift_freeVariables_eq_empty 3 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have hbound2 : bound2.freeVariables = ∅ :=
    closedShift_freeVariables_eq_empty 2 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have hbound1 : bound1.freeVariables = ∅ :=
    closedShift_freeVariables_eq_empty 1 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have hfirst := bexsLTSucc_freeVariables_eq_empty_of_empty terminal bound3
    hterminal hbound3
  have hsecond := bexsLTSucc_freeVariables_eq_empty_of_empty
    (terminal.bexsLTSucc bound3) bound2 hfirst hbound2
  have hthird := bexsLTSucc_freeVariables_eq_empty_of_empty
    ((terminal.bexsLTSucc bound3).bexsLTSucc bound2) bound1 hsecond hbound1
  simpa only [compactAdditiveNatListListRowsBody, terminal, bound3, bound2,
    bound1] using hthird

theorem compactAdditiveNatListListRowsBranchTerminal_context_le
    (tokenTable width tokenCount boundaryTable rowIndex numericBound : Nat)
    (hrowIndex : rowIndex <= numericBound) :
    formulaCodeSum
        (valuationContext
          (compactAdditiveNatListListRowsBranchTerminal tokenTable width
            tokenCount boundaryTable).freeVariables
          (extendValuation rowIndex
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation)) <=
      compactAdditiveNatListListRowsContextCodeResource numericBound := by
  have hvaluation :
      (extendValuation rowIndex
        FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation) 0 <=
          numericBound := by
    simpa only [extendValuation_zero] using hrowIndex
  exact valuationContext_formulaCodeSum_le_singleton _ _ numericBound
    (compactAdditiveNatListListRowsBranchTerminal_freeVariables_subset_singleton
      tokenTable width tokenCount boundaryTable)
    hvaluation

#print axioms
  compactAdditiveNatListListRowsBranchTerminal_freeVariables_subset_singleton
#print axioms compactAdditiveNatListListRowsBody_freeVariables_eq_empty
#print axioms compactAdditiveNatListListRowsBranchTerminal_context_le

end FoundationCompactNumericListedDirectNatListListRowsDirectBranchUniformResources
