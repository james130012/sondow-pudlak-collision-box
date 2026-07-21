import integration.FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

/-!
# Explicit hybrid certificate for the accepted final witness-table row

The three public coordinates are closed with short binary numerals.  The
resulting formula is split into its exact column-36 and column-38 fixed-width
entry instances, whose certificates are assembled explicitly.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAFixedWidthEntryHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

private def zeroValuation : Nat -> Nat := fun _ => 0

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right :
      LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ :
        LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Mul.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left * !!right’) =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

/-- The original three-coordinate predicate closed by short binary numerals. -/
def compactNumericVerifierAcceptedWitnessTableRowClosedFormula
    (tableWidth table rowIndex : Nat) : ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierAcceptedWitnessTableRowDef.val) ⇜
    ![shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm table,
      shortBinaryNumeralTerm rowIndex]

/-- The original syntactic index term for column 36. -/
def compactNumericVerifierAcceptedWitnessTableRowColumn36IndexTerm
    (rowIndex : Nat) : ValuationTerm :=
  ‘!!(shortBinaryNumeralTerm rowIndex) * 429 + 36’

/-- The original syntactic index term for column 38. -/
def compactNumericVerifierAcceptedWitnessTableRowColumn38IndexTerm
    (rowIndex : Nat) : ValuationTerm :=
  ‘!!(shortBinaryNumeralTerm rowIndex) * 429 + 38’

/-- The two exact fixed-width-entry instances exposed by the parent formula. -/
def compactNumericVerifierAcceptedWitnessTableRowEntriesClosedFormula
    (tableWidth table rowIndex : Nat) : ArithmeticProposition :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table)
      (shortBinaryNumeralTerm tableWidth)
      (compactNumericVerifierAcceptedWitnessTableRowColumn36IndexTerm
        rowIndex)
      (‘1’ : ValuationTerm) ⋏
    compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table)
      (shortBinaryNumeralTerm tableWidth)
      (compactNumericVerifierAcceptedWitnessTableRowColumn38IndexTerm
        rowIndex)
      (‘1’ : ValuationTerm)

/-- Closing the original formula exposes exactly columns 36 and 38. -/
theorem compactNumericVerifierAcceptedWitnessTableRowClosedFormula_eq_entries
    (tableWidth table rowIndex : Nat) :
    compactNumericVerifierAcceptedWitnessTableRowClosedFormula
        tableWidth table rowIndex =
      compactNumericVerifierAcceptedWitnessTableRowEntriesClosedFormula
        tableWidth table rowIndex := by
  unfold compactNumericVerifierAcceptedWitnessTableRowClosedFormula
  unfold compactNumericVerifierAcceptedWitnessTableRowEntriesClosedFormula
  unfold compactNumericVerifierAcceptedWitnessTableRowColumn36IndexTerm
  unfold compactNumericVerifierAcceptedWitnessTableRowColumn38IndexTerm
  unfold compactNumericVerifierAcceptedWitnessTableRowDef
  unfold compactFixedWidthEntryAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app]
    · intro index
      exact Empty.elim index
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app]
    · intro index
      exact Empty.elim index

@[simp] theorem
    termValue_compactNumericVerifierAcceptedWitnessTableRowColumn36IndexTerm
    (rowIndex : Nat) :
    termValue zeroValuation
        (compactNumericVerifierAcceptedWitnessTableRowColumn36IndexTerm
          rowIndex) =
      rowIndex * 429 + 36 := by
  rw [compactNumericVerifierAcceptedWitnessTableRowColumn36IndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue_shortBinaryNumeralTerm]
  norm_num [termValue, LO.FirstOrder.Semiterm.val_operator]

@[simp] theorem
    termValue_compactNumericVerifierAcceptedWitnessTableRowColumn38IndexTerm
    (rowIndex : Nat) :
    termValue zeroValuation
        (compactNumericVerifierAcceptedWitnessTableRowColumn38IndexTerm
          rowIndex) =
      rowIndex * 429 + 38 := by
  rw [compactNumericVerifierAcceptedWitnessTableRowColumn38IndexTerm,
    termValue_arithmeticAdd, termValue_arithmeticMul,
    termValue_shortBinaryNumeralTerm]
  norm_num [termValue, LO.FirstOrder.Semiterm.val_operator]

/-- Explicit certificate from the two semantic fixed-width entry facts. -/
noncomputable def
    compactNumericVerifierAcceptedWitnessTableRowExplicitHybridCertificateOfEntries
    (tableWidth table rowIndex : Nat)
    (hcolumn36 : CompactFixedWidthEntry table tableWidth
      (rowIndex * 429 + 36) 1)
    (hcolumn38 : CompactFixedWidthEntry table tableWidth
      (rowIndex * 429 + 38) 1) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactNumericVerifierAcceptedWitnessTableRowClosedFormula
        tableWidth table rowIndex) := by
  let entriesCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm table)
        (shortBinaryNumeralTerm tableWidth)
        (compactNumericVerifierAcceptedWitnessTableRowColumn36IndexTerm
          rowIndex)
        (‘1’ : ValuationTerm) (by
          simpa [termValue_shortBinaryNumeralTerm,
            termValue_arithmeticOne] using hcolumn36))
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm table)
        (shortBinaryNumeralTerm tableWidth)
        (compactNumericVerifierAcceptedWitnessTableRowColumn38IndexTerm
          rowIndex)
        (‘1’ : ValuationTerm) (by
          simpa [termValue_shortBinaryNumeralTerm,
            termValue_arithmeticOne] using hcolumn38))
  exact .cast
    (compactNumericVerifierAcceptedWitnessTableRowClosedFormula_eq_entries
      tableWidth table rowIndex).symm entriesCertificate

/-- Explicit certificate from the public accepted-row semantic predicate. -/
noncomputable def compactNumericVerifierAcceptedWitnessTableRowExplicitHybridCertificate
    (tableWidth table rowIndex : Nat)
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table rowIndex) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactNumericVerifierAcceptedWitnessTableRowClosedFormula
        tableWidth table rowIndex) := by
  apply
    compactNumericVerifierAcceptedWitnessTableRowExplicitHybridCertificateOfEntries
  · simpa [compactNumericVerifierStepWitnessColumnCount] using haccepted.1
  · simpa [compactNumericVerifierStepWitnessColumnCount] using haccepted.2

theorem
    compactNumericVerifierAcceptedWitnessTableRowClosedFormula_freeVariables_eq_empty
    (tableWidth table rowIndex : Nat) :
    (compactNumericVerifierAcceptedWitnessTableRowClosedFormula
      tableWidth table rowIndex).freeVariables = ∅ := by
  unfold compactNumericVerifierAcceptedWitnessTableRowClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

/-- Checked PA proof in the empty context compiled from the explicit certificate. -/
noncomputable def compileCompactNumericVerifierAcceptedWitnessTableRowExplicitHybridContext
    (tableWidth table rowIndex : Nat)
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table rowIndex) :
    CertifiedPAContextProof ∅
      (compactNumericVerifierAcceptedWitnessTableRowClosedFormula
        tableWidth table rowIndex) := by
  let raw :=
    (compactNumericVerifierAcceptedWitnessTableRowExplicitHybridCertificate
      tableWidth table rowIndex haccepted).compile
  have hcontext :
      valuationContext
          (compactNumericVerifierAcceptedWitnessTableRowClosedFormula
            tableWidth table rowIndex).freeVariables zeroValuation = ∅ := by
    rw [
      compactNumericVerifierAcceptedWitnessTableRowClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

/-- Proof-free recursive resource for the fully explicit hybrid certificate. -/
noncomputable def
    compactNumericVerifierAcceptedWitnessTableRowExplicitHybridStructuralResource
    (tableWidth table rowIndex : Nat)
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table rowIndex) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactNumericVerifierAcceptedWitnessTableRowExplicitHybridCertificate
      tableWidth table rowIndex haccepted)

theorem
    compileCompactNumericVerifierAcceptedWitnessTableRowExplicitHybridContext_payloadLength_le
    (tableWidth table rowIndex : Nat)
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table rowIndex) :
    (compileCompactNumericVerifierAcceptedWitnessTableRowExplicitHybridContext
      tableWidth table rowIndex haccepted).payloadLength ≤
      compactNumericVerifierAcceptedWitnessTableRowExplicitHybridStructuralResource
        tableWidth table rowIndex haccepted := by
  unfold
    compileCompactNumericVerifierAcceptedWitnessTableRowExplicitHybridContext
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactNumericVerifierAcceptedWitnessTableRowExplicitHybridCertificate
        tableWidth table rowIndex haccepted)

#print axioms
  compactNumericVerifierAcceptedWitnessTableRowClosedFormula_eq_entries
#print axioms
  compactNumericVerifierAcceptedWitnessTableRowExplicitHybridCertificateOfEntries
#print axioms
  compactNumericVerifierAcceptedWitnessTableRowExplicitHybridCertificate
#print axioms
  compileCompactNumericVerifierAcceptedWitnessTableRowExplicitHybridContext
#print axioms
  compactNumericVerifierAcceptedWitnessTableRowExplicitHybridStructuralResource
#print axioms
  compileCompactNumericVerifierAcceptedWitnessTableRowExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowExplicitHybridCertificate
