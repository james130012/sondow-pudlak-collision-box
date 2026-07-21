import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRows
import integration.FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryHybridCompiler
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for one formula-transform state row

The right table lookup preserves the original `index + 1` term.  The final
conjunct is the explicit seventeen-coordinate state-core certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFixedWidthEntryHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate

def compactFormulaTransformStateAtRowsZeroValuation : Nat -> Nat := fun _ => 0

private abbrev zeroValuation := compactFormulaTransformStateAtRowsZeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private noncomputable def closedLtCertificate
    (left right : Nat) (hlt : left < right) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) <
        termValue zeroValuation (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

private noncomputable def valuationLtCertificate
    (leftTerm : ValuationTerm) (right : Nat)
    (hlt : termValue zeroValuation leftTerm < right) :
    HybridCertificate
      “!!leftTerm < !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![leftTerm, shortBinaryNumeralTerm right] (by
      change termValue zeroValuation leftTerm <
        termValue zeroValuation (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

def compactFormulaTransformStateAtRowsClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFormulaTransformStateAtRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm index,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.parserFinish,
      shortBinaryNumeralTerm coordinates.parserTokensFinish,
      shortBinaryNumeralTerm coordinates.parserTasksFinish,
      shortBinaryNumeralTerm coordinates.parserTokensBoundary,
      shortBinaryNumeralTerm coordinates.parserTokensCount,
      shortBinaryNumeralTerm coordinates.parserTasksBoundary,
      shortBinaryNumeralTerm coordinates.parserTasksCount,
      shortBinaryNumeralTerm coordinates.outputBoundary,
      shortBinaryNumeralTerm coordinates.outputCount,
      shortBinaryNumeralTerm sizeWitness.parserTokensBoundarySize,
      shortBinaryNumeralTerm sizeWitness.parserTasksBoundarySize,
      shortBinaryNumeralTerm sizeWitness.outputBoundarySize]

def compactFormulaTransformStateAtRowsExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm index) <
      !!(shortBinaryNumeralTerm stateCount)” ⋏
    (compactFixedWidthEntryClosedFormula
        stateBoundary tokenCount index coordinates.start ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm stateBoundary)
          (shortBinaryNumeralTerm tokenCount)
          ‘!!(shortBinaryNumeralTerm index) + 1’
          (shortBinaryNumeralTerm coordinates.finish) ⋏
        compactFormulaTransformStateCoreClosedFormula
          tokenTable width tokenCount coordinates sizeWitness))

def compactFormulaTransformStateAtRowsAtValuationIndexFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFormulaTransformStateAtRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      indexTerm,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.parserFinish,
      shortBinaryNumeralTerm coordinates.parserTokensFinish,
      shortBinaryNumeralTerm coordinates.parserTasksFinish,
      shortBinaryNumeralTerm coordinates.parserTokensBoundary,
      shortBinaryNumeralTerm coordinates.parserTokensCount,
      shortBinaryNumeralTerm coordinates.parserTasksBoundary,
      shortBinaryNumeralTerm coordinates.parserTasksCount,
      shortBinaryNumeralTerm coordinates.outputBoundary,
      shortBinaryNumeralTerm coordinates.outputCount,
      shortBinaryNumeralTerm sizeWitness.parserTokensBoundarySize,
      shortBinaryNumeralTerm sizeWitness.parserTasksBoundarySize,
      shortBinaryNumeralTerm sizeWitness.outputBoundarySize]

def compactFormulaTransformStateAtRowsAtValuationIndexExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    ValuationFormula :=
  “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)” ⋏
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount)
        indexTerm
        (shortBinaryNumeralTerm coordinates.start) ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm stateBoundary)
          (shortBinaryNumeralTerm tokenCount)
          ‘!!indexTerm + 1’
          (shortBinaryNumeralTerm coordinates.finish) ⋏
        compactFormulaTransformStateCoreClosedFormula
          tokenTable width tokenCount coordinates sizeWitness))

theorem compactFormulaTransformStateAtRowsClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformStateAtRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness =
      compactFormulaTransformStateAtRowsExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness := by
  unfold compactFormulaTransformStateAtRowsClosedFormula
  unfold compactFormulaTransformStateAtRowsExplicitFormula
  unfold compactFormulaTransformStateAtRowsDef
  unfold compactFixedWidthEntryClosedFormula
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactFormulaTransformStateCoreClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactFormulaTransformStateAtRowsAtValuationIndexFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformStateAtRowsAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm
          coordinates sizeWitness =
      compactFormulaTransformStateAtRowsAtValuationIndexExplicitFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm
          coordinates sizeWitness := by
  unfold compactFormulaTransformStateAtRowsAtValuationIndexFormula
  unfold compactFormulaTransformStateAtRowsAtValuationIndexExplicitFormula
  unfold compactFormulaTransformStateAtRowsDef
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactFormulaTransformStateCoreClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

noncomputable def
    compactFormulaTransformStateAtRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness) :
    HybridCertificate
      (compactFormulaTransformStateAtRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness) := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedLtCertificate index stateCount hindex)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryExplicitHybridCertificate
        stateBoundary tokenCount index coordinates.start hstart)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm stateBoundary)
          (shortBinaryNumeralTerm tokenCount)
          nextIndexTerm
          (shortBinaryNumeralTerm coordinates.finish) (by
            simpa [nextIndexTerm, termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using hfinish))
        (compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates sizeWitness hcore)))
  exact .cast
    (compactFormulaTransformStateAtRowsClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness).symm parts

noncomputable def
    compactFormulaTransformStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
        (termValue compactFormulaTransformStateAtRowsZeroValuation indexTerm)
          coordinates sizeWitness) :
    HybridCertificate
      (compactFormulaTransformStateAtRowsAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm
          coordinates sizeWitness) := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (valuationLtCertificate indexTerm stateCount (by
      simpa [compactFormulaTransformStateAtRowsZeroValuation] using hindex))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount)
        indexTerm
        (shortBinaryNumeralTerm coordinates.start) (by
          simpa [compactFormulaTransformStateAtRowsZeroValuation,
            termValue_shortBinaryNumeralTerm] using hstart))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm stateBoundary)
          (shortBinaryNumeralTerm tokenCount)
          nextIndexTerm
          (shortBinaryNumeralTerm coordinates.finish) (by
            simpa [nextIndexTerm,
              compactFormulaTransformStateAtRowsZeroValuation,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne]
              using hfinish))
        (compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates sizeWitness hcore)))
  exact .cast
    (compactFormulaTransformStateAtRowsAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm
        coordinates sizeWitness).symm parts

noncomputable def compileCompactFormulaTransformStateAtRowsExplicitHybridContext
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformStateAtRowsClosedFormula
          tokenTable width tokenCount stateBoundary stateCount index
            coordinates sizeWitness).freeVariables zeroValuation)
      (compactFormulaTransformStateAtRowsClosedFormula
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness) :=
  (compactFormulaTransformStateAtRowsExplicitHybridCertificateOfGraph
    tokenTable width tokenCount stateBoundary stateCount index
      coordinates sizeWitness hgraph).compile

noncomputable def compactFormulaTransformStateAtRowsExplicitStructuralResource
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformStateAtRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness hgraph)

theorem
    compileCompactFormulaTransformStateAtRowsExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness) :
    (compileCompactFormulaTransformStateAtRowsExplicitHybridContext
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness hgraph).payloadLength ≤
      compactFormulaTransformStateAtRowsExplicitStructuralResource
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformStateAtRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness hgraph)

#print axioms compactFormulaTransformStateAtRowsClosedFormula_alignment
#print axioms
  compactFormulaTransformStateAtRowsExplicitHybridCertificateOfGraph
#print axioms compactFormulaTransformStateAtRowsAtValuationIndexFormula_alignment
#print axioms
  compactFormulaTransformStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformStateAtRowsExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
