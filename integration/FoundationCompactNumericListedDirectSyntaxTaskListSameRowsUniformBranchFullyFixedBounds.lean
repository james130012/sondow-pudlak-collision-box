import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalPayloadFixedBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds

/-!
# Fully fixed branch payload for syntax-task same rows

The original four-witness branch terminal is bounded directly.  Its only free
variable is the shared row index, and its terminal payload is the fixed
five-leaf payload proved in the preceding module.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniformBranchFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity04Bounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsTerminalPayloadFixedBounds

private abbrev taskSameRowsZeroValuationBranchFixed : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate.zeroValuation

private theorem taskClosedShift_freeVariables_eq_empty
    (term : ValuationTerm) (hterm : term.freeVariables = ∅) :
    forall arity,
      (syntaxTaskListSameRowsClosedShift arity term).freeVariables = ∅
  | 0 => by
      simpa only [syntaxTaskListSameRowsClosedShift_zero] using hterm
  | arity + 1 => by
      rw [syntaxTaskListSameRowsClosedShift_succ]
      exact bShift_freeVariables_eq_empty_of_empty
        _ (taskClosedShift_freeVariables_eq_empty term hterm arity)

private theorem arithmeticOneTerm_freeVariables_eq_empty
    {boundArity : Nat} :
    (‘1’ : ArithmeticSemiterm Nat boundArity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_eq_func
    (left right : ArithmeticSemiterm Nat 4) :
    (‘!!left + !!right’ : ArithmeticSemiterm Nat 4) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ArithmeticSemiterm Nat 4) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr
        ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr
        ⟨1, Finset.mem_univ 1, hright⟩

private theorem taskSuccessorIndex_freeVariables_subset :
    (‘&0 + 1’ : ArithmeticSemiterm Nat 4).freeVariables ⊆ {0} := by
  rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
    arithmeticOneTerm_freeVariables_eq_empty]
  simp

private theorem taskSameRowsBranchTerminal_freeVariables_subset_singleton
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    (compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width
      tokenCount sourceBoundary targetBoundary).freeVariables ⊆ {0} := by
  have hshiftedNumeral :
      forall value,
        (syntaxTaskListSameRowsClosedShift 4
          (shortBinaryNumeralTerm value)).freeVariables ⊆ {0} := by
    intro value
    rw [taskClosedShift_freeVariables_eq_empty
      (shortBinaryNumeralTerm value)
      (shortBinaryNumeralTerm_freeVariables_eq_empty value) 4]
    simp
  have hsourceLeft :
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm sourceBoundary),
          syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm tokenCount),
          (&0 : ArithmeticSemiterm Nat 4),
          (#3 : ArithmeticSemiterm Nat 4)])).freeVariables ⊆ {0} := by
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact hshiftedNumeral sourceBoundary
    · exact hshiftedNumeral tokenCount
    · simp
    · simp
  have hsourceRight :
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm sourceBoundary),
          syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm tokenCount),
          (‘&0 + 1’ : ArithmeticSemiterm Nat 4),
          (#2 : ArithmeticSemiterm Nat 4)])).freeVariables ⊆ {0} := by
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact hshiftedNumeral sourceBoundary
    · exact hshiftedNumeral tokenCount
    · exact taskSuccessorIndex_freeVariables_subset
    · simp
  have htargetLeft :
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm targetBoundary),
          syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm tokenCount),
          (&0 : ArithmeticSemiterm Nat 4),
          (#1 : ArithmeticSemiterm Nat 4)])).freeVariables ⊆ {0} := by
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact hshiftedNumeral targetBoundary
    · exact hshiftedNumeral tokenCount
    · simp
    · simp
  have htargetRight :
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm targetBoundary),
          syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm tokenCount),
          (‘&0 + 1’ : ArithmeticSemiterm Nat 4),
          (#0 : ArithmeticSemiterm Nat 4)])).freeVariables ⊆ {0} := by
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact hshiftedNumeral targetBoundary
    · exact hshiftedNumeral tokenCount
    · exact taskSuccessorIndex_freeVariables_subset
    · simp
  have hrow :
      (((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
        ![syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm tokenTable),
          syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm width),
          syntaxTaskListSameRowsClosedShift 4
            (shortBinaryNumeralTerm tokenCount),
          (#3 : ArithmeticSemiterm Nat 4),
          (#2 : ArithmeticSemiterm Nat 4),
          (#1 : ArithmeticSemiterm Nat 4),
          (#0 : ArithmeticSemiterm Nat 4)])).freeVariables ⊆ {0} := by
    apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate
    · exact hshiftedNumeral tokenTable
    · exact hshiftedNumeral width
    · exact hshiftedNumeral tokenCount
    · simp
    · simp
    · simp
    · simp
  unfold compactAdditiveSyntaxTaskListSameRowsBranchTerminal
  simp only [LO.FirstOrder.Semiformula.freeVariables_and]
  exact Finset.union_subset hsourceLeft
    (Finset.union_subset hsourceRight
      (Finset.union_subset htargetLeft
        (Finset.union_subset htargetRight hrow)))

private theorem valuationContextFormulaCodeSum_le_taskSameRowsBranchFixed
    (valuation : Nat -> Nat) {arity : Nat}
    (formula : ArithmeticSemiformula Nat arity)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext formula.freeVariables valuation) <=
      taskSameRowsTerminalContextCodePolynomial numericBound := by
  have hcard : formula.freeVariables.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall index, index ∈ formula.freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact hvaluation
  have htermCodes : forall index, index ∈ formula.freeVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact le_rfl
  have hraw := valuationContext_formulaCodeSum_le_uniform
    formula.freeVariables valuation 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues htermCodes
  simpa only [
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum,
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum,
    taskSameRowsTerminalContextCodePolynomial] using hraw

def taskSameRowsUniformBranchFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity04
    (taskSameRowsTerminalContextCodePolynomial numericBound)
    numericBound
    (taskSameRowsBranchTerminalFormulaCodePolynomial bitBound)
    (taskSameRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound)

theorem
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound : Nat)
    (data : CompactAdditiveSyntaxTaskListSameRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hindexSuccessor : index + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary index data <=
      taskSameRowsUniformBranchFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let valuation := extendValuation index taskSameRowsZeroValuationBranchFixed
  let body := compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable
    width tokenCount sourceBoundary targetBoundary
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact data.targetRight_le
    · exact data.targetLeft_le
    · exact data.sourceRight_le
    · exact data.sourceLeft_le
  have hindex : index <= numericBound := by omega
  have hvaluation : valuation 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext body.freeVariables valuation) <=
        taskSameRowsTerminalContextCodePolynomial numericBound := by
    exact valuationContextFormulaCodeSum_le_taskSameRowsBranchFixed valuation
      body numericBound
      (taskSameRowsBranchTerminal_freeVariables_subset_singleton tokenTable
        width tokenCount sourceBoundary targetBoundary)
      hvaluation
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :=
    compactAdditiveSyntaxTaskListSameRowsBranchTerminal_code_length_le_fixed
      tokenTable width tokenCount sourceBoundary targetBoundary bitBound
      htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
      htargetBoundarySize
  have hterminal :=
    compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary targetBoundary index
      numericBound bitBound data hwidth htokenCount hindexSuccessor
      htokenTableSize hsourceBoundarySize htargetBoundarySize hnumericSize
  have hfixed :=
    explicitBoundedWitnessHybridStructuralPayloadEnvelope_le_fullyFixed_arity04
      (terminalSmall :=
        compactAdditiveSyntaxTaskListSameRowsTerminalStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary index data)
      (terminalLarge :=
        taskSameRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound)
      valuation
      (taskSameRowsTerminalContextCodePolynomial numericBound)
      tokenCount numericBound
      (taskSameRowsBranchTerminalFormulaCodePolynomial bitBound)
      body values hvalues htokenCount hbody hcontext hterminal
  simpa only [
    compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope,
    taskSameRowsUniformBranchFullyFixedPayloadPolynomial, valuation, body,
    values, taskSameRowsZeroValuationBranchFixed] using hfixed

def taskSameRowsAllBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound *
    taskSameRowsUniformBranchFullyFixedPayloadPolynomial numericBound bitBound

theorem
    compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound : Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListSameRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows <=
      taskSameRowsAllBranchesFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let resource :=
    taskSameRowsUniformBranchFullyFixedPayloadPolynomial numericBound bitBound
  have hsum :
      (∑ index : Fin sourceCount,
        compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary index
          (rows index)) <=
        ∑ _index : Fin sourceCount, resource := by
    apply Finset.sum_le_sum
    intro index _
    have hindexSuccessor : index.val + 1 <= numericBound :=
      (Nat.succ_le_of_lt index.isLt).trans hsourceCount
    exact
      compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary targetBoundary index
        numericBound bitBound (rows index) hwidth htokenCount
        hindexSuccessor htokenTableSize hsourceBoundarySize
        htargetBoundarySize hnumericSize
  have hsum' :
      (∑ index : Fin sourceCount,
        compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope
          tokenTable width tokenCount sourceBoundary targetBoundary index
          (rows index)) <= sourceCount * resource := by
    simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] using hsum
  have hcount :
      sourceCount * resource <= numericBound * resource :=
    Nat.mul_le_mul_right resource hsourceCount
  unfold compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum
    taskSameRowsAllBranchesFullyFixedPayloadPolynomial
  simpa only [resource] using hsum'.trans hcount

#print axioms taskSameRowsBranchTerminal_freeVariables_subset_singleton
#print axioms
  compactAdditiveSyntaxTaskListSameRowsBranchStructuralPayloadEnvelope_le_fullyFixed
#print axioms
  compactAdditiveSyntaxTaskListSameRowsBranchPayloadResourceSum_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsUniformBranchFullyFixedBounds
