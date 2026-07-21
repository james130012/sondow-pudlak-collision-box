import integration.FoundationCompactNumericListedDirectChildResultRowEquality
import integration.FoundationCompactNumericListedDirectVerifierChildResultCoreExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListSameRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificates for direct child-result-row equality graphs

The seventeen-coordinate row-equality graph is the conjunction of two closed
child-result cores, the closed equality graph for their natural-list-list
rows, and a closed numeric equality atom for their Boolean tags.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectChildResultRowEqGraphExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectChildResultRowEquality
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierChildResultCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListSameRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

/-- Close all seventeen row-equality coordinates by short binary numerals. -/
def compactNumericChildResultRowEqGraphClosedFormula
    (tokenTable width tokenCount : Nat)
    (sourceCoordinates targetCoordinates :
      CompactNumericChildResultRowCoordinates)
    (sourceSizeWitness targetSizeWitness :
      CompactNumericChildResultSizeWitness) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultRowEqGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceCoordinates.start,
      shortBinaryNumeralTerm sourceCoordinates.finish,
      shortBinaryNumeralTerm sourceCoordinates.gammaFinish,
      shortBinaryNumeralTerm sourceCoordinates.gammaCount,
      shortBinaryNumeralTerm sourceCoordinates.gammaBoundary,
      shortBinaryNumeralTerm sourceCoordinates.boolValue,
      shortBinaryNumeralTerm sourceSizeWitness.gammaBoundarySize,
      shortBinaryNumeralTerm targetCoordinates.start,
      shortBinaryNumeralTerm targetCoordinates.finish,
      shortBinaryNumeralTerm targetCoordinates.gammaFinish,
      shortBinaryNumeralTerm targetCoordinates.gammaCount,
      shortBinaryNumeralTerm targetCoordinates.gammaBoundary,
      shortBinaryNumeralTerm targetCoordinates.boolValue,
      shortBinaryNumeralTerm targetSizeWitness.gammaBoundarySize]

/-- The four immediate components of the closed row-equality graph. -/
def compactNumericChildResultRowEqGraphPartsFormula
    (tokenTable width tokenCount : Nat)
    (sourceCoordinates targetCoordinates :
      CompactNumericChildResultRowCoordinates)
    (sourceSizeWitness targetSizeWitness :
      CompactNumericChildResultSizeWitness) : ValuationFormula :=
  compactNumericChildResultCoreClosedFormula
      tokenTable width tokenCount sourceCoordinates sourceSizeWitness ⋏
    (compactNumericChildResultCoreClosedFormula
        tokenTable width tokenCount targetCoordinates targetSizeWitness ⋏
      (compactAdditiveNatListListSameRowsClosedFormula
          tokenTable width tokenCount
          sourceCoordinates.gammaBoundary sourceCoordinates.gammaCount
          targetCoordinates.gammaBoundary targetCoordinates.gammaCount ⋏
        “!!(shortBinaryNumeralTerm sourceCoordinates.boolValue) =
          !!(shortBinaryNumeralTerm targetCoordinates.boolValue)”))

/-- Exact syntactic alignment of the closed row graph with its four parts. -/
theorem compactNumericChildResultRowEqGraphClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (sourceCoordinates targetCoordinates :
      CompactNumericChildResultRowCoordinates)
    (sourceSizeWitness targetSizeWitness :
      CompactNumericChildResultSizeWitness) :
    compactNumericChildResultRowEqGraphClosedFormula
        tokenTable width tokenCount sourceCoordinates targetCoordinates
          sourceSizeWitness targetSizeWitness =
      compactNumericChildResultRowEqGraphPartsFormula
        tokenTable width tokenCount sourceCoordinates targetCoordinates
          sourceSizeWitness targetSizeWitness := by
  rcases sourceCoordinates with
    ⟨sourceStart, sourceFinish, sourceGammaFinish, sourceGammaCount,
      sourceGammaBoundary, sourceBoolValue⟩
  rcases targetCoordinates with
    ⟨targetStart, targetFinish, targetGammaFinish, targetGammaCount,
      targetGammaBoundary, targetBoolValue⟩
  rcases sourceSizeWitness with ⟨sourceGammaBoundarySize⟩
  rcases targetSizeWitness with ⟨targetGammaBoundarySize⟩
  unfold compactNumericChildResultRowEqGraphClosedFormula
  unfold compactNumericChildResultRowEqGraphPartsFormula
  unfold compactNumericChildResultRowEqGraphDef
  simp [compactNumericChildResultCoreClosedFormula,
    compactAdditiveNatListListSameRowsClosedFormula,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private noncomputable def closedBoolEqualityCertificate
    (sourceBoolValue targetBoolValue : Nat)
    (heq : sourceBoolValue = targetBoolValue) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm sourceBoolValue) =
        !!(shortBinaryNumeralTerm targetBoolValue)” := by
  exact .positiveAtomic zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm sourceBoolValue,
      shortBinaryNumeralTerm targetBoolValue] (by
        change termValue zeroValuation
            (shortBinaryNumeralTerm sourceBoolValue) =
          termValue zeroValuation
            (shortBinaryNumeralTerm targetBoolValue)
        simpa [termValue_shortBinaryNumeralTerm] using heq)

/-- Build the explicit certificate directly from the public row-equality graph. -/
noncomputable def compactNumericChildResultRowEqGraphExplicitHybridCertificate
    {tokenTable width tokenCount : Nat}
    {sourceCoordinates targetCoordinates :
      CompactNumericChildResultRowCoordinates}
    {sourceSizeWitness targetSizeWitness :
      CompactNumericChildResultSizeWitness}
    (hgraph : CompactNumericChildResultRowEqGraph
      tokenTable width tokenCount sourceCoordinates targetCoordinates
        sourceSizeWitness targetSizeWitness) :
    HybridCertificate
      (compactNumericChildResultRowEqGraphClosedFormula
        tokenTable width tokenCount sourceCoordinates targetCoordinates
          sourceSizeWitness targetSizeWitness) := by
  rw [compactNumericChildResultRowEqGraphClosedFormula_alignment]
  rcases hgraph with ⟨hsourceCore, htargetCore, hsameRows, hboolEq⟩
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactNumericChildResultCoreExplicitHybridCertificate hsourceCore)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactNumericChildResultCoreExplicitHybridCertificate htargetCore)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListListSameRowsExplicitHybridCertificate
          tokenTable width tokenCount
          sourceCoordinates.gammaBoundary sourceCoordinates.gammaCount
          targetCoordinates.gammaBoundary targetCoordinates.gammaCount
          hsameRows)
        (closedBoolEqualityCertificate
          sourceCoordinates.boolValue targetCoordinates.boolValue hboolEq)))

#print axioms compactNumericChildResultRowEqGraphClosedFormula_alignment
#print axioms compactNumericChildResultRowEqGraphExplicitHybridCertificate

end FoundationCompactNumericListedDirectChildResultRowEqGraphExplicitHybridCertificate
