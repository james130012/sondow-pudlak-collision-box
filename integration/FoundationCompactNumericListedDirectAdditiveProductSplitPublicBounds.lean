import integration.FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Transparent structural resource for additive product splits

The three checked inequalities are charged by their public atomic compilers and
two explicit conjunction envelopes.  The resource depends only on the four
numeric inputs and never on the graph proof.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate

def closedShortLtStructuralPayloadPolynomial (left right : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial zeroValuation
    Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right]

theorem closedLtCertificate_structuralPayloadBound_le_public
    (left right : Nat) (hlt : left < right) :
    hybridFormulaStructuralPayloadBound (closedLtCertificate left right hlt) <=
      closedShortLtStructuralPayloadPolynomial left right := by
  have hraw := compilePositiveRelationPayloadResource_le_publicPolynomial
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right]
    (by
      change (shortBinaryNumeralTerm left).freeVariables ⊆ {0}
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
      simp)
    (by
      change (shortBinaryNumeralTerm right).freeVariables ⊆ {0}
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
      simp)
  simpa only [closedLtCertificate, hybridFormulaStructuralPayloadBound,
    closedShortLtStructuralPayloadPolynomial] using hraw

def closedShortLeStructuralPayloadPolynomial (left right : Nat) : Nat :=
  if left = right then
    transparentHybridDisjunctionLeftPayloadEnvelope zeroValuation
      (LO.FirstOrder.Semiformula.rel Language.Eq.eq
        ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right])
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right])
      (compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq
        ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right])
  else
    transparentHybridDisjunctionRightPayloadEnvelope zeroValuation
      (LO.FirstOrder.Semiformula.rel Language.Eq.eq
        ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right])
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right])
      (compilePositiveRelationPayloadPolynomial zeroValuation
        Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right])

theorem closedLeCertificate_structuralPayloadBound_le_public
    (left right : Nat) (hle : left <= right) :
    hybridFormulaStructuralPayloadBound (closedLeCertificate left right hle) <=
      closedShortLeStructuralPayloadPolynomial left right := by
  let args : Fin 2 -> ValuationTerm :=
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm left).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm right).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  by_cases heq : left = right
  · let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.Eq.eq args (by
          change termValue zeroValuation (shortBinaryNumeralTerm left) =
            termValue zeroValuation (shortBinaryNumeralTerm right)
          simpa [termValue_shortBinaryNumeralTerm] using heq)
    have hequality := compilePositiveRelationPayloadResource_le_publicPolynomial
      zeroValuation Language.Eq.eq args hfirst hsecond
    have hdisjunction := transparentHybridDisjunctionLeftPayloadBound_le
      (right :=
        LO.FirstOrder.Semiformula.rel Language.LT.lt args)
      equality
      (compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq
        args)
      (by simpa only [hybridFormulaStructuralPayloadBound, equality] using
        hequality)
    have hcertificate : closedLeCertificate left right hle =
        CheckedHybridValuationBoundedFormulaCertificate.cast
          (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            equality) := by
      simp [closedLeCertificate, heq, equality, args]
    rw [hcertificate]
    unfold closedShortLeStructuralPayloadPolynomial
    rw [if_pos heq]
    simpa only [hybridFormulaStructuralPayloadBound, args, equality] using
      hdisjunction
  · have hlt : left < right := Nat.lt_of_le_of_ne hle heq
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.ORing.Rel.lt args (by
          change termValue zeroValuation (shortBinaryNumeralTerm left) <
            termValue zeroValuation (shortBinaryNumeralTerm right)
          simpa [termValue_shortBinaryNumeralTerm] using hlt)
    have hltSymbol : Language.ORing.Rel.lt =
        (Language.LT.lt : LO.FirstOrder.Language.Rel ℒₒᵣ 2) := by
      rfl
    let strictLT : CheckedHybridValuationBoundedFormulaCertificate
        zeroValuation
        (LO.FirstOrder.Semiformula.rel Language.LT.lt args) :=
      CheckedHybridValuationBoundedFormulaCertificate.cast
        (congrArg (fun relationSymbol =>
          LO.FirstOrder.Semiformula.rel relationSymbol args) hltSymbol)
        strict
    have hstrict := compilePositiveRelationPayloadResource_le_publicPolynomial
      zeroValuation Language.ORing.Rel.lt args hfirst hsecond
    have hstrictLT : hybridFormulaStructuralPayloadBound strictLT <=
        compilePositiveRelationPayloadPolynomial zeroValuation
          Language.ORing.Rel.lt args := by
      simpa only [strictLT, strict, hybridFormulaStructuralPayloadBound] using
        hstrict
    have hdisjunction := transparentHybridDisjunctionRightPayloadBound_le
      (left :=
        LO.FirstOrder.Semiformula.rel Language.Eq.eq args)
      strictLT
      (compilePositiveRelationPayloadPolynomial zeroValuation
        Language.ORing.Rel.lt args)
      hstrictLT
    have hcertificate : closedLeCertificate left right hle =
        CheckedHybridValuationBoundedFormulaCertificate.cast
          (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            strict) := by
      simp [closedLeCertificate, heq, strict, args]
    rw [hcertificate]
    unfold closedShortLeStructuralPayloadPolynomial
    rw [if_neg heq]
    simpa only [hybridFormulaStructuralPayloadBound, args, strict, strictLT]
      using hdisjunction

def compactAdditiveProductSplitStructuralPayloadPolynomial
    (tokenCount start middle finish : Nat) : Nat :=
  let firstFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm start) <
      !!(shortBinaryNumeralTerm middle)”
  let secondFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm middle) <
      !!(shortBinaryNumeralTerm finish)”
  let lastFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm finish) ≤
      !!(shortBinaryNumeralTerm tokenCount)”
  let tailFormula := secondFormula ⋏ lastFormula
  let tailResource := transparentHybridConjunctionPayloadEnvelope zeroValuation
    secondFormula lastFormula
    (closedShortLtStructuralPayloadPolynomial middle finish)
    (closedShortLeStructuralPayloadPolynomial finish tokenCount)
  transparentHybridConjunctionPayloadEnvelope zeroValuation firstFormula
    tailFormula (closedShortLtStructuralPayloadPolynomial start middle)
    tailResource

theorem
    compactAdditiveProductSplitExplicitHybridCertificate_structuralPayloadBound_le_public
    (tokenCount start middle finish : Nat)
    (hgraph : CompactAdditiveProductSplit tokenCount start middle finish) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveProductSplitExplicitHybridCertificateOfGraph
          tokenCount start middle finish hgraph) <=
      compactAdditiveProductSplitStructuralPayloadPolynomial
        tokenCount start middle finish := by
  let firstCertificate := closedLtCertificate start middle hgraph.1
  let secondCertificate := closedLtCertificate middle finish hgraph.2.1
  let lastCertificate := closedLeCertificate finish tokenCount hgraph.2.2
  have hfirst := closedLtCertificate_structuralPayloadBound_le_public
    start middle hgraph.1
  have hsecond := closedLtCertificate_structuralPayloadBound_le_public
    middle finish hgraph.2.1
  have hlast := closedLeCertificate_structuralPayloadBound_le_public
    finish tokenCount hgraph.2.2
  have htail := transparentHybridConjunctionPayloadBound_le
    secondCertificate lastCertificate
    (closedShortLtStructuralPayloadPolynomial middle finish)
    (closedShortLeStructuralPayloadPolynomial finish tokenCount)
    hsecond hlast
  have houter := transparentHybridConjunctionPayloadBound_le
    firstCertificate
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      secondCertificate lastCertificate)
    (closedShortLtStructuralPayloadPolynomial start middle)
    (transparentHybridConjunctionPayloadEnvelope zeroValuation
      (“!!(shortBinaryNumeralTerm middle) <
          !!(shortBinaryNumeralTerm finish)” : ValuationFormula)
      (“!!(shortBinaryNumeralTerm finish) ≤
          !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)
      (closedShortLtStructuralPayloadPolynomial middle finish)
      (closedShortLeStructuralPayloadPolynomial finish tokenCount))
    hfirst htail
  simpa only [compactAdditiveProductSplitExplicitHybridCertificateOfGraph,
    compactAdditiveProductSplitStructuralPayloadPolynomial,
    firstCertificate, secondCertificate, lastCertificate,
    hybridFormulaStructuralPayloadBound] using houter

#print axioms closedLtCertificate_structuralPayloadBound_le_public
#print axioms closedLeCertificate_structuralPayloadBound_le_public
#print axioms
  compactAdditiveProductSplitExplicitHybridCertificate_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds
