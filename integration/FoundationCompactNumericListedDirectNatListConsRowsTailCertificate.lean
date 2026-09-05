import integration.FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

/-! # Exact five-leaf terminal certificate for natural-list cons tail rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 280000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

private abbrev consRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

def consRowsTailValuation (index : Nat) : Nat -> Nat :=
  extendValuation index consRowsZeroValuation

def consRowsTailIndexTerm : ValuationTerm := &0

def consRowsTailSuccessorTerm : ValuationTerm := ‘&0 + 1’

def consRowsTailSecondSuccessorTerm : ValuationTerm := ‘&0 + 2’

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (Semiterm.func functionSymbol ![left, right]).freeVariables =
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
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticTwoTerm_freeVariables_eq_empty :
    (‘2’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  change termValue valuation
    (Semiterm.Operator.operator
      (Semiterm.Operator.numeral ℒₒᵣ 2) ![]) = 2
  unfold termValue
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext coordinate
        exact Fin.elim0 coordinate]
  simp

@[simp] theorem termValue_consRowsTailIndexTerm (index : Nat) :
    termValue (consRowsTailValuation index) consRowsTailIndexTerm = index := by
  simp [consRowsTailValuation, consRowsTailIndexTerm, consRowsZeroValuation,
    extendValuation]

@[simp] theorem termValue_consRowsTailSuccessorTerm (index : Nat) :
    termValue (consRowsTailValuation index) consRowsTailSuccessorTerm =
      index + 1 := by
  simp [consRowsTailValuation, consRowsTailSuccessorTerm,
    consRowsZeroValuation, termValue_arithmeticAdd, termValue_arithmeticOne,
    extendValuation]

@[simp] theorem termValue_consRowsTailSecondSuccessorTerm (index : Nat) :
    termValue (consRowsTailValuation index) consRowsTailSecondSuccessorTerm =
      index + 2 := by
  simp [consRowsTailValuation, consRowsTailSecondSuccessorTerm,
    consRowsZeroValuation, termValue_arithmeticAdd, termValue_arithmeticTwo,
    extendValuation]

theorem consRowsTailIndexTerm_freeVariables_subset :
    consRowsTailIndexTerm.freeVariables ⊆ {0} := by
  simp [consRowsTailIndexTerm]

theorem consRowsTailSuccessorTerm_freeVariables_subset :
    consRowsTailSuccessorTerm.freeVariables ⊆ {0} := by
  unfold consRowsTailSuccessorTerm
  rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
    arithmeticOneTerm_freeVariables_eq_empty]
  simp

theorem consRowsTailSecondSuccessorTerm_freeVariables_subset :
    consRowsTailSecondSuccessorTerm.freeVariables ⊆ {0} := by
  unfold consRowsTailSecondSuccessorTerm
  rw [arithmeticAddTerm_eq_func, binaryFunctionTerm_freeVariables,
    arithmeticTwoTerm_freeVariables_eq_empty]
  simp

def compactAdditiveNatListConsTailValues
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) : Fin 4 -> Nat :=
  ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]

theorem compactAdditiveNatListConsTailValues_le
    {tokenTable width tokenCount sourceBoundary targetBoundary index : Nat}
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    forall coordinate, compactAdditiveNatListConsTailValues data coordinate <=
      tokenCount := by
  intro coordinate
  fin_cases coordinate
  · exact data.targetRight_le
  · exact data.targetLeft_le
  · exact data.sourceRight_le
  · exact data.sourceLeft_le

def consRowsTailSourceLeftFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary)
    (shortBinaryNumeralTerm tokenCount) consRowsTailIndexTerm
    (shortBinaryNumeralTerm data.sourceLeft)

def consRowsTailSourceRightFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary)
    (shortBinaryNumeralTerm tokenCount) consRowsTailSuccessorTerm
    (shortBinaryNumeralTerm data.sourceRight)

def consRowsTailTargetLeftFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) consRowsTailSuccessorTerm
    (shortBinaryNumeralTerm data.targetLeft)

def consRowsTailTargetRightFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) : ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) consRowsTailSecondSuccessorTerm
    (shortBinaryNumeralTerm data.targetRight)

def consRowsTailAtomicRowFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) : ValuationFormula :=
  compactAdditiveAtomicRowEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm data.sourceLeft)
    (shortBinaryNumeralTerm data.sourceRight)
    (shortBinaryNumeralTerm data.targetLeft)
    (shortBinaryNumeralTerm data.targetRight)

def consRowsTailPartsFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) : ValuationFormula :=
  consRowsTailSourceLeftFormula tokenTable width tokenCount sourceBoundary
      targetBoundary index data ⋏
    (consRowsTailSourceRightFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data ⋏
      (consRowsTailTargetLeftFormula tokenTable width tokenCount sourceBoundary
          targetBoundary index data ⋏
        (consRowsTailTargetRightFormula tokenTable width tokenCount
            sourceBoundary targetBoundary index data ⋏
          consRowsTailAtomicRowFormula tokenTable width tokenCount
            sourceBoundary targetBoundary index data)))

theorem consRowsTailSourceLeftEntry
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CompactFixedWidthEntry sourceBoundary tokenCount
      (termValue (consRowsTailValuation index) consRowsTailIndexTerm)
      data.sourceLeft := by
  simpa only [termValue_consRowsTailIndexTerm] using data.sourceLeft_entry

theorem consRowsTailSourceRightEntry
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CompactFixedWidthEntry sourceBoundary tokenCount
      (termValue (consRowsTailValuation index) consRowsTailSuccessorTerm)
      data.sourceRight := by
  simpa only [termValue_consRowsTailSuccessorTerm] using data.sourceRight_entry

theorem consRowsTailTargetLeftEntry
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CompactFixedWidthEntry targetBoundary tokenCount
      (termValue (consRowsTailValuation index) consRowsTailSuccessorTerm)
      data.targetLeft := by
  simpa only [termValue_consRowsTailSuccessorTerm] using data.targetLeft_entry

theorem consRowsTailTargetRightEntry
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CompactFixedWidthEntry targetBoundary tokenCount
      (termValue (consRowsTailValuation index)
        consRowsTailSecondSuccessorTerm) data.targetRight := by
  simpa only [termValue_consRowsTailSecondSuccessorTerm] using
    data.targetRight_entry

theorem consRowsTailSourceLeftEntryAtTerms
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CompactFixedWidthEntry
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm sourceBoundary))
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm tokenCount))
      (termValue (consRowsTailValuation index) consRowsTailIndexTerm)
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm data.sourceLeft)) := by
  simpa only [termValue_shortBinaryNumeralTerm] using
    (consRowsTailSourceLeftEntry tokenTable width tokenCount sourceBoundary
      targetBoundary index data)

theorem consRowsTailSourceRightEntryAtTerms
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CompactFixedWidthEntry
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm sourceBoundary))
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm tokenCount))
      (termValue (consRowsTailValuation index) consRowsTailSuccessorTerm)
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm data.sourceRight)) := by
  simpa only [termValue_shortBinaryNumeralTerm] using
    (consRowsTailSourceRightEntry tokenTable width tokenCount sourceBoundary
      targetBoundary index data)

theorem consRowsTailTargetLeftEntryAtTerms
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CompactFixedWidthEntry
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm targetBoundary))
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm tokenCount))
      (termValue (consRowsTailValuation index) consRowsTailSuccessorTerm)
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm data.targetLeft)) := by
  simpa only [termValue_shortBinaryNumeralTerm] using
    (consRowsTailTargetLeftEntry tokenTable width tokenCount sourceBoundary
      targetBoundary index data)

theorem consRowsTailTargetRightEntryAtTerms
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CompactFixedWidthEntry
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm targetBoundary))
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm tokenCount))
      (termValue (consRowsTailValuation index)
        consRowsTailSecondSuccessorTerm)
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm data.targetRight)) := by
  simpa only [termValue_shortBinaryNumeralTerm] using
    (consRowsTailTargetRightEntry tokenTable width tokenCount sourceBoundary
      targetBoundary index data)

theorem consRowsTailAtomicRowAtTerms
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CompactAdditiveAtomicRowEq
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm tokenTable))
      (termValue (consRowsTailValuation index) (shortBinaryNumeralTerm width))
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm tokenCount))
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm data.sourceLeft))
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm data.sourceRight))
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm data.targetLeft))
      (termValue (consRowsTailValuation index)
        (shortBinaryNumeralTerm data.targetRight)) := by
  simpa only [termValue_shortBinaryNumeralTerm] using data.atomic_row_eq

noncomputable def consRowsTailSourceLeftCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (consRowsTailValuation index)
      (consRowsTailSourceLeftFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data) :=
  compactFixedWidthEntryAtValuationExplicitHybridCertificate
    (consRowsTailValuation index) (shortBinaryNumeralTerm sourceBoundary)
    (shortBinaryNumeralTerm tokenCount) consRowsTailIndexTerm
    (shortBinaryNumeralTerm data.sourceLeft)
    (consRowsTailSourceLeftEntryAtTerms tokenTable width tokenCount
      sourceBoundary targetBoundary index data)

noncomputable def consRowsTailSourceRightCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (consRowsTailValuation index)
      (consRowsTailSourceRightFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data) :=
  compactFixedWidthEntryAtValuationExplicitHybridCertificate
    (consRowsTailValuation index) (shortBinaryNumeralTerm sourceBoundary)
    (shortBinaryNumeralTerm tokenCount) consRowsTailSuccessorTerm
    (shortBinaryNumeralTerm data.sourceRight)
    (consRowsTailSourceRightEntryAtTerms tokenTable width tokenCount
      sourceBoundary targetBoundary index data)

noncomputable def consRowsTailTargetLeftCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (consRowsTailValuation index)
      (consRowsTailTargetLeftFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data) :=
  compactFixedWidthEntryAtValuationExplicitHybridCertificate
    (consRowsTailValuation index) (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) consRowsTailSuccessorTerm
    (shortBinaryNumeralTerm data.targetLeft)
    (consRowsTailTargetLeftEntryAtTerms tokenTable width tokenCount
      sourceBoundary targetBoundary index data)

noncomputable def consRowsTailTargetRightCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (consRowsTailValuation index)
      (consRowsTailTargetRightFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data) :=
  compactFixedWidthEntryAtValuationExplicitHybridCertificate
    (consRowsTailValuation index) (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) consRowsTailSecondSuccessorTerm
    (shortBinaryNumeralTerm data.targetRight)
    (consRowsTailTargetRightEntryAtTerms tokenTable width tokenCount
      sourceBoundary targetBoundary index data)

noncomputable def consRowsTailAtomicRowCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (consRowsTailValuation index)
      (consRowsTailAtomicRowFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data) :=
  compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate
    (consRowsTailValuation index) (shortBinaryNumeralTerm tokenTable)
    (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm data.sourceLeft)
    (shortBinaryNumeralTerm data.sourceRight)
    (shortBinaryNumeralTerm data.targetLeft)
    (shortBinaryNumeralTerm data.targetRight)
    (consRowsTailAtomicRowAtTerms tokenTable width tokenCount sourceBoundary
      targetBoundary index data)

noncomputable def compactAdditiveNatListConsRowsTailPartsCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (consRowsTailValuation index)
      (consRowsTailPartsFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data) :=
  CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (consRowsTailSourceLeftCertificate tokenTable width tokenCount
      sourceBoundary targetBoundary index data)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (consRowsTailSourceRightCertificate tokenTable width tokenCount
        sourceBoundary targetBoundary index data)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (consRowsTailTargetLeftCertificate tokenTable width tokenCount
          sourceBoundary targetBoundary index data)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (consRowsTailTargetRightCertificate tokenTable width tokenCount
            sourceBoundary targetBoundary index data)
          (consRowsTailAtomicRowCertificate tokenTable width tokenCount
            sourceBoundary targetBoundary index data))))

theorem consRowsTailPartsFormula_eq_substitutedTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    consRowsTailPartsFormula tokenTable width tokenCount sourceBoundary
        targetBoundary index data =
      ((compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
          tokenCount sourceBoundary targetBoundary) ⇜
        fun coordinate : Fin 4 => shortBinaryNumeralTerm
          (compactAdditiveNatListConsTailValues data coordinate)) := by
  unfold consRowsTailPartsFormula consRowsTailSourceLeftFormula
    consRowsTailSourceRightFormula consRowsTailTargetLeftFormula
    consRowsTailTargetRightFormula consRowsTailAtomicRowFormula
  rw [show
      (fun coordinate : Fin 4 => shortBinaryNumeralTerm
        (compactAdditiveNatListConsTailValues data coordinate)) =
        ![shortBinaryNumeralTerm data.targetRight,
          shortBinaryNumeralTerm data.targetLeft,
          shortBinaryNumeralTerm data.sourceRight,
          shortBinaryNumeralTerm data.sourceLeft] by
        funext coordinate
        fin_cases coordinate <;> rfl]
  exact
    (compactAdditiveNatListConsRowsTailBranchTerminal_substitution_alignment
      tokenTable width tokenCount sourceBoundary targetBoundary data.sourceLeft
        data.sourceRight data.targetLeft data.targetRight).symm

noncomputable def compactAdditiveNatListConsRowsTailTerminalCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (consRowsTailValuation index)
      ((compactAdditiveNatListConsRowsTailBranchTerminal tokenTable width
          tokenCount sourceBoundary targetBoundary) ⇜
        fun coordinate : Fin 4 => shortBinaryNumeralTerm
          (compactAdditiveNatListConsTailValues data coordinate)) :=
  CheckedHybridValuationBoundedFormulaCertificate.cast
    (consRowsTailPartsFormula_eq_substitutedTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary index data)
    (compactAdditiveNatListConsRowsTailPartsCertificate tokenTable width
      tokenCount sourceBoundary targetBoundary index data)

#print axioms termValue_consRowsTailIndexTerm
#print axioms termValue_consRowsTailSuccessorTerm
#print axioms termValue_consRowsTailSecondSuccessorTerm
#print axioms consRowsTailSourceLeftEntry
#print axioms consRowsTailSourceRightEntry
#print axioms consRowsTailTargetLeftEntry
#print axioms consRowsTailTargetRightEntry
#print axioms consRowsTailSourceLeftEntryAtTerms
#print axioms consRowsTailSourceRightEntryAtTerms
#print axioms consRowsTailTargetLeftEntryAtTerms
#print axioms consRowsTailTargetRightEntryAtTerms
#print axioms consRowsTailAtomicRowAtTerms
#print axioms consRowsTailSourceLeftCertificate
#print axioms consRowsTailSourceRightCertificate
#print axioms consRowsTailTargetLeftCertificate
#print axioms consRowsTailTargetRightCertificate
#print axioms consRowsTailAtomicRowCertificate
#print axioms compactAdditiveNatListConsRowsTailPartsCertificate
#print axioms consRowsTailPartsFormula_eq_substitutedTerminal
#print axioms compactAdditiveNatListConsRowsTailTerminalCertificate

end FoundationCompactNumericListedDirectNatListConsRowsTailCertificate
