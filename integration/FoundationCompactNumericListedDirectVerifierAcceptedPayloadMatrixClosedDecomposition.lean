import integration.FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrix
import integration.FoundationCompactNumericListedDirectCanonicalFormulaTableHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedProofWitness

/-!
# Closed decomposition of the accepted-payload matrix

The sixteen public coordinates are installed once and the resulting formula is
identified with its three exact conjuncts.  This is formula alignment only; the
three checked certificates are supplied by their independent explicit routes.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrixClosedDecomposition

open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputSplit
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula
open FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrix
open FoundationCompactNumericListedDirectCanonicalFormulaTableHybridCertificate
open FoundationCompactNumericListedDirectBoundedProofWitness
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

def compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula
    (code tokenCount tokenTable offsetTable width : Nat) :
    ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat)
      compactCanonicalPackedTokenStreamTableauAtWidthDef.val) ⇜
    ![shortBinaryNumeralTerm code,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm offsetTable,
      shortBinaryNumeralTerm width]

theorem compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula_eq_atCode
    (tokens : List Nat) (code tokenCount tokenTable offsetTable width : Nat)
    (htokenCount : tokenCount = tokens.length)
    (hwidth : width = (compactBinaryNatPayloadBits tokens).length)
    (htokenTable : tokenTable = compactFixedWidthTableCode width tokens)
    (hoffsetTable : offsetTable = compactFixedWidthTableCode width
      (compactBinaryNatTokenOffsets tokens)) :
    compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula
        code tokenCount tokenTable offsetTable width =
      compactCanonicalFormulaTableClosedFormulaAtCode tokens code := by
  subst tokenCount
  subst tokenTable
  subst offsetTable
  subst width
  rfl

theorem boundedWitnessInputTableauClosedFormula_eq_atCode
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    let witness := bounded.witness
    compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula
        witness.proofCode witness.inputTokenCount witness.inputTable
        witness.inputOffsetTable witness.inputWidth =
      compactCanonicalFormulaTableClosedFormulaAtCode
        (bounded.proofTokens ++ bounded.certificateTokens)
        witness.proofCode := by
  exact compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula_eq_atCode
    (bounded.proofTokens ++ bounded.certificateTokens)
    bounded.witness.proofCode bounded.witness.inputTokenCount
    bounded.witness.inputTable bounded.witness.inputOffsetTable
    bounded.witness.inputWidth
    bounded.inputTokenCount_eq bounded.inputWidth_eq bounded.inputTable_eq
    bounded.inputOffsetTable_eq

/-- The canonical proof-code input tableau, explicitly certified on the exact
coordinates stored by the bounded direct witness. -/
noncomputable def boundedWitnessInputTableauExplicitCertificate
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    CheckedHybridValuationBoundedFormulaCertificate (fun _ => 0)
      (compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula
        bounded.witness.proofCode bounded.witness.inputTokenCount
        bounded.witness.inputTable bounded.witness.inputOffsetTable
        bounded.witness.inputWidth) :=
  .cast (boundedWitnessInputTableauClosedFormula_eq_atCode bounded).symm
    (compactCanonicalFormulaTableExplicitCertificateAtCode
      (bounded.proofTokens ++ bounded.certificateTokens)
      bounded.witness.proofCode bounded.proofCode_eq)

theorem boundedWitnessFormulaTableauClosedFormula_eq_atCode
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    let witness := bounded.witness
    compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula
        formulaCode witness.formulaTokenCount witness.formulaTable
        witness.formulaOffsetTable witness.formulaWidth =
      compactCanonicalFormulaTableClosedFormulaAtCode
        bounded.formulaTokens formulaCode := by
  exact compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula_eq_atCode
    bounded.formulaTokens formulaCode bounded.witness.formulaTokenCount
    bounded.witness.formulaTable bounded.witness.formulaOffsetTable
    bounded.witness.formulaWidth
    bounded.formulaTokenCount_eq bounded.formulaWidth_eq
    bounded.formulaTable_eq bounded.formulaOffsetTable_eq

/-- The conclusion formula tableau, explicitly certified on the exact direct
witness coordinates. -/
noncomputable def boundedWitnessFormulaTableauExplicitCertificate
    {bound formulaCode : Nat}
    (bounded : CompactListedPADirectBoundedWitness bound formulaCode) :
    CheckedHybridValuationBoundedFormulaCertificate (fun _ => 0)
      (compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula
        formulaCode bounded.witness.formulaTokenCount
        bounded.witness.formulaTable bounded.witness.formulaOffsetTable
        bounded.witness.formulaWidth) :=
  .cast (boundedWitnessFormulaTableauClosedFormula_eq_atCode bounded).symm
    (compactCanonicalFormulaTableExplicitCertificateAtCode
      bounded.formulaTokens formulaCode bounded.formulaCode_eq)

def compactNumericVerifierAcceptedTraceInputSplitClosedFormula
    (inputTable inputWidth inputTokenCount
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split : Nat) :
    ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierAcceptedTraceInputSplitDef.val) ⇜
    ![shortBinaryNumeralTerm inputTable,
      shortBinaryNumeralTerm inputWidth,
      shortBinaryNumeralTerm inputTokenCount,
      shortBinaryNumeralTerm sourceTable,
      shortBinaryNumeralTerm sourceWidth,
      shortBinaryNumeralTerm sourceTokenCount,
      shortBinaryNumeralTerm proofStart,
      shortBinaryNumeralTerm proofFinish,
      shortBinaryNumeralTerm certificateStart,
      shortBinaryNumeralTerm certificateFinish,
      shortBinaryNumeralTerm split]

def compactNumericVerifierAcceptedTraceTableClosedFormula
    (traceWidth traceTable traceValueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat)
    (fuelTerm : ValuationTerm) : ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierAcceptedTraceTableDef.val) ⇜
    ![shortBinaryNumeralTerm traceWidth,
      shortBinaryNumeralTerm traceTable,
      shortBinaryNumeralTerm traceValueBound,
      fuelTerm,
      shortBinaryNumeralTerm proofTable,
      shortBinaryNumeralTerm proofWidth,
      shortBinaryNumeralTerm proofTokenCount,
      shortBinaryNumeralTerm proofStart,
      shortBinaryNumeralTerm proofFinish,
      shortBinaryNumeralTerm certificateTable,
      shortBinaryNumeralTerm certificateWidth,
      shortBinaryNumeralTerm certificateTokenCount,
      shortBinaryNumeralTerm certificateStart,
      shortBinaryNumeralTerm certificateFinish]

def compactNumericVerifierAcceptedPayloadMatrixClosedFormula
    (code inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound : Nat) : ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierAcceptedPayloadMatrixDef.val) ⇜
    ![shortBinaryNumeralTerm code,
      shortBinaryNumeralTerm inputTokenCount,
      shortBinaryNumeralTerm inputTable,
      shortBinaryNumeralTerm inputOffsetTable,
      shortBinaryNumeralTerm inputWidth,
      shortBinaryNumeralTerm sourceTable,
      shortBinaryNumeralTerm sourceWidth,
      shortBinaryNumeralTerm sourceTokenCount,
      shortBinaryNumeralTerm proofStart,
      shortBinaryNumeralTerm proofFinish,
      shortBinaryNumeralTerm certificateStart,
      shortBinaryNumeralTerm certificateFinish,
      shortBinaryNumeralTerm split,
      shortBinaryNumeralTerm traceWidth,
      shortBinaryNumeralTerm traceTable,
      shortBinaryNumeralTerm traceValueBound]

def compactNumericVerifierAcceptedPayloadMatrixDecomposedFormula
    (code inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound : Nat) : ArithmeticProposition :=
  compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula
      code inputTokenCount inputTable inputOffsetTable inputWidth ⋏
    (compactNumericVerifierAcceptedTraceInputSplitClosedFormula
        inputTable inputWidth inputTokenCount
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split ⋏
      compactNumericVerifierAcceptedTraceTableClosedFormula
        traceWidth traceTable traceValueBound
        sourceTable sourceWidth sourceTokenCount proofStart proofFinish
        sourceTable sourceWidth sourceTokenCount
        certificateStart certificateFinish
        ‘(4 * (!!(shortBinaryNumeralTerm inputTokenCount) + 1) + 8)’)

theorem compactNumericVerifierAcceptedPayloadMatrixClosedFormula_eq_decomposed
    (code inputTokenCount inputTable inputOffsetTable inputWidth
      sourceTable sourceWidth sourceTokenCount
      proofStart proofFinish certificateStart certificateFinish split
      traceWidth traceTable traceValueBound : Nat) :
    compactNumericVerifierAcceptedPayloadMatrixClosedFormula
        code inputTokenCount inputTable inputOffsetTable inputWidth
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split
        traceWidth traceTable traceValueBound =
      compactNumericVerifierAcceptedPayloadMatrixDecomposedFormula
        code inputTokenCount inputTable inputOffsetTable inputWidth
        sourceTable sourceWidth sourceTokenCount
        proofStart proofFinish certificateStart certificateFinish split
        traceWidth traceTable traceValueBound := by
  unfold compactNumericVerifierAcceptedPayloadMatrixClosedFormula
  unfold compactNumericVerifierAcceptedPayloadMatrixDecomposedFormula
  unfold compactCanonicalPackedTokenStreamTableauAtWidthClosedFormula
  unfold compactNumericVerifierAcceptedTraceInputSplitClosedFormula
  unfold compactNumericVerifierAcceptedTraceTableClosedFormula
  unfold compactNumericVerifierAcceptedPayloadMatrixDef
  simp [← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app]
    · intro index
      exact Empty.elim index
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

#print axioms
  compactNumericVerifierAcceptedPayloadMatrixClosedFormula_eq_decomposed
#print axioms boundedWitnessInputTableauExplicitCertificate
#print axioms boundedWitnessFormulaTableauExplicitCertificate

end FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrixClosedDecomposition
