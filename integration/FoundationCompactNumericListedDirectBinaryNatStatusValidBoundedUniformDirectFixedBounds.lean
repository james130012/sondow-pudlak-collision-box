import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectCompiler
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectFixedBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Fixed payload bound for the three-way bounded binary-Nat status terminal

The running, failed, and completed branches are compiled directly.  All three
are charged to one numeric coordinate, one bit-width coordinate, and one
syntax coordinate; no finite enumeration of the witness range is used.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPABoundedWitnessGuardCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity04
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusUniformDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

private abbrev statusFixedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

private theorem threeShortNumeralRewritingFormula_code_length_le_uniform
    (formula : LO.FirstOrder.ArithmeticSemisentence 3)
    (value0 value1 value2 bitBound : Nat)
    (hsize0 : Nat.size value0 <= bitBound)
    (hsize1 : Nat.size value1 <= bitBound)
    (hsize2 : Nat.size value2 <= bitBound) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) formula) ⇜
        ![shortBinaryNumeralTerm value0, shortBinaryNumeralTerm value1,
          shortBinaryNumeralTerm value2])).length <=
      uniformRewritingFormulaCodeEnvelope
        (binaryNumeralTermCodeEnvelope bitBound)
        (binaryFormulaCode (Rewriting.emb (ξ := Nat) formula)).length := by
  let rewriting : Rew ℒₒᵣ Nat 3 Nat 0 := Rew.subst
    ![shortBinaryNumeralTerm value0, shortBinaryNumeralTerm value1,
      shortBinaryNumeralTerm value2]
  have hrewriting : RewritingImageCodeBound rewriting
      (binaryNumeralTermCodeEnvelope bitBound) := by
    constructor
    · intro coordinate
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      fin_cases coordinate
      · exact binaryNumeralTerm_code_length_le_envelope value0 bitBound hsize0
      · exact binaryNumeralTerm_code_length_le_envelope value1 bitBound hsize1
      · exact binaryNumeralTerm_code_length_le_envelope value2 bitBound hsize2
    · intro coordinate
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (binaryNumeralTermCodeEnvelope bitBound) hrewriting
    (Rewriting.emb (ξ := Nat) formula)
  simpa only [rewriting] using hraw

private theorem twoShortNumeralRewritingFormula_code_length_le_uniform
    (formula : LO.FirstOrder.ArithmeticSemisentence 2)
    (value0 value1 bitBound : Nat)
    (hsize0 : Nat.size value0 <= bitBound)
    (hsize1 : Nat.size value1 <= bitBound) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) formula) ⇜
        ![shortBinaryNumeralTerm value0,
          shortBinaryNumeralTerm value1])).length <=
      uniformRewritingFormulaCodeEnvelope
        (binaryNumeralTermCodeEnvelope bitBound)
        (binaryFormulaCode (Rewriting.emb (ξ := Nat) formula)).length := by
  let rewriting : Rew ℒₒᵣ Nat 2 Nat 0 := Rew.subst
    ![shortBinaryNumeralTerm value0, shortBinaryNumeralTerm value1]
  have hrewriting : RewritingImageCodeBound rewriting
      (binaryNumeralTermCodeEnvelope bitBound) := by
    constructor
    · intro coordinate
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      fin_cases coordinate
      · exact binaryNumeralTerm_code_length_le_envelope value0 bitBound hsize0
      · exact binaryNumeralTerm_code_length_le_envelope value1 bitBound hsize1
    · intro coordinate
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (binaryNumeralTermCodeEnvelope bitBound) hrewriting
    (Rewriting.emb (ξ := Nat) formula)
  simpa only [rewriting] using hraw

private theorem threeShortNumeralRewritingFormula_freeVariables_eq_empty
    (formula : LO.FirstOrder.ArithmeticSemisentence 3)
    (value0 value1 value2 : Nat) :
    ((Rewriting.emb (ξ := Nat) formula) ⇜
      ![shortBinaryNumeralTerm value0, shortBinaryNumeralTerm value1,
        shortBinaryNumeralTerm value2]).freeVariables = ∅ := by
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value0
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value1
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value2

def compactBinaryNatStatusAreaSourceFormula :
    LO.FirstOrder.ArithmeticSemisentence 3 :=
  “#2 ≤ (#0 + 1) * #1”

private theorem compactBinaryNatCompletedAreaFormula_alignment
    (tokenCount outputCount outputBoundarySize : Nat) :
    ((Rewriting.emb (ξ := Nat) compactBinaryNatStatusAreaSourceFormula) ⇜
        ![shortBinaryNumeralTerm outputCount,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm outputBoundarySize]) =
      (“!!(shortBinaryNumeralTerm outputBoundarySize) ≤
        (!!(shortBinaryNumeralTerm outputCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula) := by
  simp [compactBinaryNatStatusAreaSourceFormula]

def compactBinaryNatRunningStatusFormulaCodePolynomial (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactBinaryNatRunningStatusSliceDef.val)).length

def compactBinaryNatFailedStatusFormulaCodePolynomial (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactBinaryNatFailedStatusSliceDef.val)).length

def compactBinaryNatCompletedPrefixFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactBinaryNatCompletedStatusPrefixDef.val)).length

def compactBinaryNatCompletedLayoutFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactAdditiveStructuredListLayoutDef.val)).length

def compactBinaryNatCompletedUnitFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactAdditiveUnitBoundaryRowsDef.val)).length

def compactBinaryNatCompletedSizeFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactNatSizeDef.val)).length

def compactBinaryNatCompletedAreaFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactBinaryNatStatusAreaSourceFormula)).length

def compactBinaryNatCompletedStatusFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  compactBinaryNatCompletedPrefixFormulaCodePolynomial bitBound +
    compactBinaryNatCompletedLayoutFormulaCodePolynomial bitBound +
    compactBinaryNatCompletedUnitFormulaCodePolynomial bitBound +
    compactBinaryNatCompletedSizeFormulaCodePolynomial bitBound +
    compactBinaryNatCompletedAreaFormulaCodePolynomial bitBound +
    4 * (binaryNatCode 4).length

def compactBinaryNatStatusTerminalSyntaxPolynomial (bitBound : Nat) : Nat :=
  compactBinaryNatRunningStatusFormulaCodePolynomial bitBound +
    compactBinaryNatFailedStatusFormulaCodePolynomial bitBound +
    compactBinaryNatCompletedStatusFormulaCodePolynomial bitBound +
    2 * (binaryNatCode 5).length + 1

private theorem compactBinaryNatRunningStatusFormula_code_length_le_fixed
    (tokenTable width tokenCount start finish bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound) :
    (binaryFormulaCode
      (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width
        tokenCount start finish)).length <=
      compactBinaryNatRunningStatusFormulaCodePolynomial bitBound := by
  have hraw := fiveShortNumeralRewritingFormula_code_length_le_uniform
    compactBinaryNatRunningStatusSliceDef.val tokenTable width tokenCount start
    finish bitBound htokenTableSize hwidthSize htokenCountSize hstartSize
    hfinishSize
  simpa only [compactBinaryNatRunningStatusSliceClosedFormula,
    compactBinaryNatRunningStatusFormulaCodePolynomial] using hraw

private theorem compactBinaryNatFailedStatusFormula_code_length_le_fixed
    (tokenTable width tokenCount start finish bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound) :
    (binaryFormulaCode
      (compactBinaryNatFailedStatusSliceClosedFormula tokenTable width
        tokenCount start finish)).length <=
      compactBinaryNatFailedStatusFormulaCodePolynomial bitBound := by
  have hraw := fiveShortNumeralRewritingFormula_code_length_le_uniform
    compactBinaryNatFailedStatusSliceDef.val tokenTable width tokenCount start
    finish bitBound htokenTableSize hwidthSize htokenCountSize hstartSize
    hfinishSize
  simpa only [compactBinaryNatFailedStatusSliceClosedFormula,
    compactBinaryNatFailedStatusFormulaCodePolynomial] using hraw

private theorem compactBinaryNatCompletedPrefixFormula_code_length_le_fixed
    (tokenTable width tokenCount start outputStart bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (houtputStartSize : Nat.size outputStart <= bitBound) :
    (binaryFormulaCode
      (compactBinaryNatCompletedStatusPrefixClosedFormula tokenTable width
        tokenCount start outputStart)).length <=
      compactBinaryNatCompletedPrefixFormulaCodePolynomial bitBound := by
  have hraw := fiveShortNumeralRewritingFormula_code_length_le_uniform
    compactBinaryNatCompletedStatusPrefixDef.val tokenTable width tokenCount
    start outputStart bitBound htokenTableSize hwidthSize htokenCountSize
    hstartSize houtputStartSize
  simpa only [compactBinaryNatCompletedStatusPrefixClosedFormula,
    compactBinaryNatCompletedPrefixFormulaCodePolynomial] using hraw

private theorem compactBinaryNatCompletedLayoutFormula_code_length_le_fixed
    (tokenTable width tokenCount outputStart outputCount finish outputBoundary
      bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (houtputStartSize : Nat.size outputStart <= bitBound)
    (houtputCountSize : Nat.size outputCount <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (hboundaryTableSize : Nat.size outputBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveStructuredListLayoutClosedFormula tokenTable width
        tokenCount outputStart outputCount finish outputBoundary)).length <=
      compactBinaryNatCompletedLayoutFormulaCodePolynomial bitBound := by
  have hraw := compactAdditiveStructuredListLayoutRewriting_code_length_le_fixed
    tokenTable width tokenCount outputStart outputCount finish outputBoundary
    bitBound htokenTableSize hwidthSize htokenCountSize houtputStartSize
    houtputCountSize hfinishSize hboundaryTableSize
  simpa only [compactAdditiveStructuredListLayoutClosedFormula,
    compactBinaryNatCompletedLayoutFormulaCodePolynomial,
    structuredListLayoutClosedTerms, structuredListLayoutSourceFormula] using
      hraw

private theorem compactBinaryNatCompletedUnitFormula_code_length_le_fixed
    (tokenCount outputCount outputBoundary bitBound : Nat)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (houtputCountSize : Nat.size outputCount <= bitBound)
    (hboundaryTableSize : Nat.size outputBoundary <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveUnitBoundaryRowsClosedFormula tokenCount outputCount
        outputBoundary)).length <=
      compactBinaryNatCompletedUnitFormulaCodePolynomial bitBound := by
  have hraw := threeShortNumeralRewritingFormula_code_length_le_uniform
    compactAdditiveUnitBoundaryRowsDef.val tokenCount outputCount outputBoundary
    bitBound htokenCountSize houtputCountSize hboundaryTableSize
  simpa only [compactAdditiveUnitBoundaryRowsClosedFormula,
    compactBinaryNatCompletedUnitFormulaCodePolynomial] using hraw

private theorem compactBinaryNatCompletedSizeFormula_code_length_le_fixed
    (outputBoundarySize outputBoundary bitBound : Nat)
    (houtputBoundarySizeSize : Nat.size outputBoundarySize <= bitBound)
    (hboundaryTableSize : Nat.size outputBoundary <= bitBound) :
    (binaryFormulaCode
      (compactNatSizeClosedFormula outputBoundarySize outputBoundary)).length <=
      compactBinaryNatCompletedSizeFormulaCodePolynomial bitBound := by
  have hraw := twoShortNumeralRewritingFormula_code_length_le_uniform
    compactNatSizeDef.val outputBoundarySize outputBoundary bitBound
    houtputBoundarySizeSize hboundaryTableSize
  simpa only [compactNatSizeClosedFormula,
    compactBinaryNatCompletedSizeFormulaCodePolynomial] using hraw

private theorem compactBinaryNatCompletedAreaFormula_code_length_le_fixed
    (tokenCount outputCount outputBoundarySize bitBound : Nat)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (houtputCountSize : Nat.size outputCount <= bitBound)
    (houtputBoundarySizeSize : Nat.size outputBoundarySize <= bitBound) :
    (binaryFormulaCode
      (“!!(shortBinaryNumeralTerm outputBoundarySize) ≤
        (!!(shortBinaryNumeralTerm outputCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)).length <=
      compactBinaryNatCompletedAreaFormulaCodePolynomial bitBound := by
  have hraw := threeShortNumeralRewritingFormula_code_length_le_uniform
    compactBinaryNatStatusAreaSourceFormula outputCount tokenCount
    outputBoundarySize bitBound houtputCountSize htokenCountSize
    houtputBoundarySizeSize
  rw [← compactBinaryNatCompletedAreaFormula_alignment tokenCount outputCount
    outputBoundarySize]
  simpa only [compactBinaryNatCompletedAreaFormulaCodePolynomial] using hraw

private theorem compactBinaryNatCompletedStatusFormula_code_length_le_fixed
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (houtputStartSize : Nat.size outputStart <= bitBound)
    (houtputCountSize : Nat.size outputCount <= bitBound)
    (hboundaryTableSize : Nat.size outputBoundary <= bitBound)
    (houtputBoundarySizeSize : Nat.size outputBoundarySize <= bitBound) :
    (binaryFormulaCode
      (compactBinaryNatCompletedStatusUniformDirectFormula tokenTable width
        tokenCount start finish outputStart outputBoundary outputBoundarySize
        outputCount)).length <=
      compactBinaryNatCompletedStatusFormulaCodePolynomial bitBound := by
  have hprefix := compactBinaryNatCompletedPrefixFormula_code_length_le_fixed
    tokenTable width tokenCount start outputStart bitBound htokenTableSize
    hwidthSize htokenCountSize hstartSize houtputStartSize
  have hlayout := compactBinaryNatCompletedLayoutFormula_code_length_le_fixed
    tokenTable width tokenCount outputStart outputCount finish outputBoundary
    bitBound htokenTableSize hwidthSize htokenCountSize houtputStartSize
    houtputCountSize hfinishSize hboundaryTableSize
  have hunit := compactBinaryNatCompletedUnitFormula_code_length_le_fixed
    tokenCount outputCount outputBoundary bitBound htokenCountSize
    houtputCountSize hboundaryTableSize
  have hsize := compactBinaryNatCompletedSizeFormula_code_length_le_fixed
    outputBoundarySize outputBoundary bitBound houtputBoundarySizeSize
    hboundaryTableSize
  have harea := compactBinaryNatCompletedAreaFormula_code_length_le_fixed
    tokenCount outputCount outputBoundarySize bitBound htokenCountSize
    houtputCountSize houtputBoundarySizeSize
  unfold compactBinaryNatCompletedStatusUniformDirectFormula
    compactBinaryNatCompletedStatusFormulaCodePolynomial
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem compactBinaryNatStatusTerminalFormula_code_length_le_fixed
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound)
    (houtputStartSize : Nat.size outputStart <= bitBound)
    (houtputCountSize : Nat.size outputCount <= bitBound)
    (hboundaryTableSize : Nat.size outputBoundary <= bitBound)
    (houtputBoundarySizeSize : Nat.size outputBoundarySize <= bitBound) :
    (binaryFormulaCode
      (compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula
        tokenTable width tokenCount start finish outputStart outputBoundary
        outputBoundarySize outputCount)).length <=
      compactBinaryNatStatusTerminalSyntaxPolynomial bitBound := by
  have hrunning := compactBinaryNatRunningStatusFormula_code_length_le_fixed
    tokenTable width tokenCount start finish bitBound htokenTableSize hwidthSize
    htokenCountSize hstartSize hfinishSize
  have hfailed := compactBinaryNatFailedStatusFormula_code_length_le_fixed
    tokenTable width tokenCount start finish bitBound htokenTableSize hwidthSize
    htokenCountSize hstartSize hfinishSize
  have hcompleted :=
    compactBinaryNatCompletedStatusFormula_code_length_le_fixed tokenTable width
      tokenCount start finish outputStart outputBoundary outputBoundarySize
      outputCount bitBound htokenTableSize hwidthSize htokenCountSize hstartSize
      hfinishSize houtputStartSize houtputCountSize hboundaryTableSize
      houtputBoundarySizeSize
  unfold compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula
    compactBinaryNatStatusTerminalSyntaxPolynomial
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem compactBinaryNatRunningStatusFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start finish : Nat) :
    (compactBinaryNatRunningStatusSliceClosedFormula tokenTable width tokenCount
      start finish).freeVariables = ∅ := by
  simpa only [compactBinaryNatRunningStatusSliceClosedFormula] using
    fiveShortNumeralRewritingFormula_freeVariables_eq_empty
      compactBinaryNatRunningStatusSliceDef.val tokenTable width tokenCount
      start finish

private theorem compactBinaryNatCompletedStatusFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) :
    (compactBinaryNatCompletedStatusUniformDirectFormula tokenTable width
      tokenCount start finish outputStart outputBoundary outputBoundarySize
      outputCount).freeVariables = ∅ := by
  have hprefix :=
    compactBinaryNatCompletedStatusPrefixClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount start outputStart
  have hlayout :=
    compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
  have hunit := compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
    tokenCount outputCount outputBoundary
  have hsize : (compactNatSizeClosedFormula outputBoundarySize
      outputBoundary).freeVariables = ∅ := by
    unfold compactNatSizeClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty outputBoundarySize
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty outputBoundary
  have harea :
      (“!!(shortBinaryNumeralTerm outputBoundarySize) ≤
        (!!(shortBinaryNumeralTerm outputCount) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” :
        ValuationFormula).freeVariables = ∅ := by
    rw [← compactBinaryNatCompletedAreaFormula_alignment tokenCount outputCount
      outputBoundarySize]
    exact threeShortNumeralRewritingFormula_freeVariables_eq_empty
      compactBinaryNatStatusAreaSourceFormula outputCount tokenCount
      outputBoundarySize
  unfold compactBinaryNatCompletedStatusUniformDirectFormula
  simp only [LO.FirstOrder.Semiformula.freeVariables_and, hprefix, hlayout,
    hunit, hsize, harea]
  simp

private theorem compactBinaryNatStatusTerminalFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) :
    (compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula tokenTable
      width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount).freeVariables = ∅ := by
  have hrunning := compactBinaryNatRunningStatusFormula_freeVariables_eq_empty
    tokenTable width tokenCount start finish
  have hfailed :=
    compactBinaryNatFailedStatusSliceClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount start finish
  have hcompleted :=
    compactBinaryNatCompletedStatusFormula_freeVariables_eq_empty tokenTable
      width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount
  unfold compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_or, hrunning,
    LO.FirstOrder.Semiformula.freeVariables_or, hfailed, hcompleted]
  simp

private theorem closedShift_four_code_length_le_nine
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    (binaryTermCode (closedShift 4 term)).length <= 9 * bound := by
  have hsymbols : termSymbolCount term <= bound :=
    (termSymbolCount_le_binaryTermCode_length term).trans hterm
  have hfirstRaw := binaryTermCode_bShift_length_le_add_symbols term
  have hfirst : (binaryTermCode (Rew.bShift term)).length <= 3 * bound := by
    omega
  have hfirstSymbols : termSymbolCount (Rew.bShift term) <= bound := by
    rw [termSymbolCount_bShift]
    exact hsymbols
  have hsecondRaw :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift term)
  have hsecond :
      (binaryTermCode (Rew.bShift (Rew.bShift term))).length <=
        5 * bound := by
    omega
  have hsecondSymbols :
      termSymbolCount (Rew.bShift (Rew.bShift term)) <= bound := by
    rw [termSymbolCount_bShift, termSymbolCount_bShift]
    exact hsymbols
  have hthirdRaw := binaryTermCode_bShift_length_le_add_symbols
    (Rew.bShift (Rew.bShift term))
  have hthird :
      (binaryTermCode
        (Rew.bShift (Rew.bShift (Rew.bShift term)))).length <=
        7 * bound := by
    omega
  have hthirdSymbols :
      termSymbolCount
        (Rew.bShift (Rew.bShift (Rew.bShift term))) <= bound := by
    rw [termSymbolCount_bShift, termSymbolCount_bShift,
      termSymbolCount_bShift]
    exact hsymbols
  have hfourthRaw := binaryTermCode_bShift_length_le_add_symbols
    (Rew.bShift (Rew.bShift (Rew.bShift term)))
  change
    (binaryTermCode
      (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift term))))).length <=
        9 * bound
  omega

private theorem closedShift_freeVariables_eq_empty
    (arity : Nat) (term : ValuationTerm)
    (hterm : term.freeVariables = ∅) :
    (closedShift arity term).freeVariables = ∅ := by
  induction arity with
  | zero => simpa [closedShift] using hterm
  | succ arity ih =>
      change (Rew.bShift (closedShift arity term)).freeVariables = ∅
      exact bShift_freeVariables_eq_empty_of_empty _ ih

private theorem statusRawEmbeddedSubstitution_code_length_le_uniform
    {sourceArity targetArity : Nat}
    (formula : LO.FirstOrder.ArithmeticSemisentence sourceArity)
    (terms : Fin sourceArity ->
      LO.FirstOrder.ArithmeticSemiterm Nat targetArity)
    (termCodeBound : Nat)
    (hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCodeBound) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) formula) ⇜ terms)).length <=
      uniformRewritingFormulaCodeEnvelope termCodeBound
        (binaryFormulaCode (Rewriting.emb (ξ := Nat) formula)).length := by
  let rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity := Rew.subst terms
  have hrewriting : RewritingImageCodeBound rewriting termCodeBound := by
    constructor
    · intro coordinate
      dsimp only [rewriting]
      simpa only [Rew.subst_bvar] using hterms coordinate
    · intro coordinate
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    termCodeBound hrewriting (Rewriting.emb (ξ := Nat) formula)
  simpa only [rewriting] using hraw

def compactBinaryNatStatusRawSubstitutionTermCodePolynomial
    (bitBound : Nat) : Nat :=
  9 * binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length +
    (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length + 1

def compactBinaryNatStatusRawRunningFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (compactBinaryNatStatusRawSubstitutionTermCodePolynomial bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactBinaryNatRunningStatusSliceDef.val)).length

def compactBinaryNatStatusRawFailedFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (compactBinaryNatStatusRawSubstitutionTermCodePolynomial bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactBinaryNatFailedStatusSliceDef.val)).length

def compactBinaryNatStatusRawCompletedPrefixFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (compactBinaryNatStatusRawSubstitutionTermCodePolynomial bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactBinaryNatCompletedStatusPrefixDef.val)).length

def compactBinaryNatStatusRawCompletedLayoutFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (compactBinaryNatStatusRawSubstitutionTermCodePolynomial bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactAdditiveStructuredListLayoutDef.val)).length

def compactBinaryNatStatusRawCompletedUnitFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (compactBinaryNatStatusRawSubstitutionTermCodePolynomial bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactAdditiveUnitBoundaryRowsDef.val)).length

def compactBinaryNatStatusRawCompletedSizeFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (compactBinaryNatStatusRawSubstitutionTermCodePolynomial bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactNatSizeDef.val)).length

def compactBinaryNatStatusRawCompletedAreaFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    (compactBinaryNatStatusRawSubstitutionTermCodePolynomial bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactBinaryNatStatusAreaSourceFormula)).length

def compactBinaryNatStatusRawTerminalFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  compactBinaryNatStatusRawRunningFormulaCodePolynomial bitBound +
    compactBinaryNatStatusRawFailedFormulaCodePolynomial bitBound +
    compactBinaryNatStatusRawCompletedPrefixFormulaCodePolynomial bitBound +
    compactBinaryNatStatusRawCompletedLayoutFormulaCodePolynomial bitBound +
    compactBinaryNatStatusRawCompletedUnitFormulaCodePolynomial bitBound +
    compactBinaryNatStatusRawCompletedSizeFormulaCodePolynomial bitBound +
    compactBinaryNatStatusRawCompletedAreaFormulaCodePolynomial bitBound +
    4 * (binaryNatCode 4).length + 2 * (binaryNatCode 5).length + 1

private theorem compactBinaryNatStatusRawAreaFormula_alignment
    (tokenCount : Nat) :
    ((Rewriting.emb (ξ := Nat) compactBinaryNatStatusAreaSourceFormula) ⇜
        ![(#0 : ArithmeticSemiterm Nat 4),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          (#1 : ArithmeticSemiterm Nat 4)]) =
      (“#1 ≤ (#0 + 1) *
        !!(closedShift 4 (shortBinaryNumeralTerm tokenCount))” :
        ArithmeticSemiformula Nat 4) := by
  simp [compactBinaryNatStatusAreaSourceFormula]

private def compactBinaryNatStatusValidBoundedRawTerminalPublicShiftFormula
    (tokenTable width tokenCount start finish : Nat) :
    ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactBinaryNatRunningStatusSliceDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
        closedShift 4 (shortBinaryNumeralTerm width),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        closedShift 4 (shortBinaryNumeralTerm start),
        closedShift 4 (shortBinaryNumeralTerm finish)]) ⋎
    (((Rewriting.emb (ξ := Nat) compactBinaryNatFailedStatusSliceDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
          closedShift 4 (shortBinaryNumeralTerm width),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          closedShift 4 (shortBinaryNumeralTerm start),
          closedShift 4 (shortBinaryNumeralTerm finish)]) ⋎
      (((Rewriting.emb (ξ := Nat)
            compactBinaryNatCompletedStatusPrefixDef.val) ⇜
          ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
            closedShift 4 (shortBinaryNumeralTerm width),
            closedShift 4 (shortBinaryNumeralTerm tokenCount),
            closedShift 4 (shortBinaryNumeralTerm start),
            (#3 : ArithmeticSemiterm Nat 4)]) ⋏
        (((Rewriting.emb (ξ := Nat)
              compactAdditiveStructuredListLayoutDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
              closedShift 4 (shortBinaryNumeralTerm width),
              closedShift 4 (shortBinaryNumeralTerm tokenCount),
              (#3 : ArithmeticSemiterm Nat 4),
              (#0 : ArithmeticSemiterm Nat 4),
              closedShift 4 (shortBinaryNumeralTerm finish),
              (#2 : ArithmeticSemiterm Nat 4)]) ⋏
          (((Rewriting.emb (ξ := Nat)
                compactAdditiveUnitBoundaryRowsDef.val) ⇜
              ![closedShift 4 (shortBinaryNumeralTerm tokenCount),
                (#0 : ArithmeticSemiterm Nat 4),
                (#2 : ArithmeticSemiterm Nat 4)]) ⋏
            (((Rewriting.emb (ξ := Nat) compactNatSizeDef.val) ⇜
                ![(#1 : ArithmeticSemiterm Nat 4),
                  (#2 : ArithmeticSemiterm Nat 4)]) ⋏
              “#1 ≤ (#0 + 1) *
                !!(closedShift 4 (shortBinaryNumeralTerm tokenCount))”)))))

private theorem
    compactBinaryNatStatusValidBoundedRawTerminal_eq_publicShiftFormula
    (tokenTable width tokenCount start finish : Nat) :
    compactBinaryNatStatusValidBoundedRawTerminal tokenTable width tokenCount
        start finish =
      compactBinaryNatStatusValidBoundedRawTerminalPublicShiftFormula
        tokenTable width tokenCount start finish := by
  rfl

private theorem
    compactBinaryNatStatusValidBoundedRawTerminal_code_length_le_fixed
    (tokenTable width tokenCount start finish bitBound : Nat)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound) :
    (binaryFormulaCode
      (compactBinaryNatStatusValidBoundedRawTerminal tokenTable width
        tokenCount start finish)).length <=
      compactBinaryNatStatusRawTerminalFormulaCodePolynomial bitBound := by
  let termCode :=
    compactBinaryNatStatusRawSubstitutionTermCodePolynomial bitBound
  have htokenTableBase := binaryNumeralTerm_code_length_le_envelope tokenTable
    bitBound htokenTableSize
  have hwidthBase := binaryNumeralTerm_code_length_le_envelope width bitBound
    hwidthSize
  have htokenCountBase := binaryNumeralTerm_code_length_le_envelope tokenCount
    bitBound htokenCountSize
  have hstartBase := binaryNumeralTerm_code_length_le_envelope start bitBound
    hstartSize
  have hfinishBase := binaryNumeralTerm_code_length_le_envelope finish bitBound
    hfinishSize
  have htokenTableShift :
      (binaryTermCode
        (closedShift 4 (shortBinaryNumeralTerm tokenTable))).length <=
        termCode :=
    (closedShift_four_code_length_le_nine _ _ htokenTableBase).trans (by
      dsimp only [termCode]
      unfold compactBinaryNatStatusRawSubstitutionTermCodePolynomial
      omega)
  have hwidthShift :
      (binaryTermCode
        (closedShift 4 (shortBinaryNumeralTerm width))).length <= termCode :=
    (closedShift_four_code_length_le_nine _ _ hwidthBase).trans (by
      dsimp only [termCode]
      unfold compactBinaryNatStatusRawSubstitutionTermCodePolynomial
      omega)
  have htokenCountShift :
      (binaryTermCode
        (closedShift 4 (shortBinaryNumeralTerm tokenCount))).length <=
        termCode :=
    (closedShift_four_code_length_le_nine _ _ htokenCountBase).trans (by
      dsimp only [termCode]
      unfold compactBinaryNatStatusRawSubstitutionTermCodePolynomial
      omega)
  have hstartShift :
      (binaryTermCode
        (closedShift 4 (shortBinaryNumeralTerm start))).length <= termCode :=
    (closedShift_four_code_length_le_nine _ _ hstartBase).trans (by
      dsimp only [termCode]
      unfold compactBinaryNatStatusRawSubstitutionTermCodePolynomial
      omega)
  have hfinishShift :
      (binaryTermCode
        (closedShift 4 (shortBinaryNumeralTerm finish))).length <= termCode :=
    (closedShift_four_code_length_le_nine _ _ hfinishBase).trans (by
      dsimp only [termCode]
      unfold compactBinaryNatStatusRawSubstitutionTermCodePolynomial
      omega)
  have hbvar0 :
      (binaryTermCode (#0 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold compactBinaryNatStatusRawSubstitutionTermCodePolynomial
    omega
  have hbvar1 :
      (binaryTermCode (#1 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold compactBinaryNatStatusRawSubstitutionTermCodePolynomial
    omega
  have hbvar2 :
      (binaryTermCode (#2 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold compactBinaryNatStatusRawSubstitutionTermCodePolynomial
    omega
  have hbvar3 :
      (binaryTermCode (#3 : ArithmeticSemiterm Nat 4)).length <= termCode := by
    dsimp only [termCode]
    unfold compactBinaryNatStatusRawSubstitutionTermCodePolynomial
    omega
  let statusTerms : Fin 5 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
      closedShift 4 (shortBinaryNumeralTerm width),
      closedShift 4 (shortBinaryNumeralTerm tokenCount),
      closedShift 4 (shortBinaryNumeralTerm start),
      closedShift 4 (shortBinaryNumeralTerm finish)]
  have hstatusTerms : forall coordinate,
      (binaryTermCode (statusTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTableShift
    · exact hwidthShift
    · exact htokenCountShift
    · exact hstartShift
    · exact hfinishShift
  let prefixTerms : Fin 5 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
      closedShift 4 (shortBinaryNumeralTerm width),
      closedShift 4 (shortBinaryNumeralTerm tokenCount),
      closedShift 4 (shortBinaryNumeralTerm start), #3]
  have hprefixTerms : forall coordinate,
      (binaryTermCode (prefixTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTableShift
    · exact hwidthShift
    · exact htokenCountShift
    · exact hstartShift
    · exact hbvar3
  let layoutTerms : Fin 7 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
      closedShift 4 (shortBinaryNumeralTerm width),
      closedShift 4 (shortBinaryNumeralTerm tokenCount), #3, #0,
      closedShift 4 (shortBinaryNumeralTerm finish), #2]
  have hlayoutTerms : forall coordinate,
      (binaryTermCode (layoutTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTableShift
    · exact hwidthShift
    · exact htokenCountShift
    · exact hbvar3
    · exact hbvar0
    · exact hfinishShift
    · exact hbvar2
  let unitTerms : Fin 3 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm tokenCount), #0, #2]
  have hunitTerms : forall coordinate,
      (binaryTermCode (unitTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htokenCountShift
    · exact hbvar0
    · exact hbvar2
  let sizeTerms : Fin 2 -> ArithmeticSemiterm Nat 4 := ![#1, #2]
  have hsizeTerms : forall coordinate,
      (binaryTermCode (sizeTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact hbvar1
    · exact hbvar2
  let areaTerms : Fin 3 -> ArithmeticSemiterm Nat 4 :=
    ![#0, closedShift 4 (shortBinaryNumeralTerm tokenCount), #1]
  have hareaTerms : forall coordinate,
      (binaryTermCode (areaTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact hbvar0
    · exact htokenCountShift
    · exact hbvar1
  have hrunningRaw := statusRawEmbeddedSubstitution_code_length_le_uniform
    compactBinaryNatRunningStatusSliceDef.val statusTerms termCode hstatusTerms
  have hrunning :
      (binaryFormulaCode
        ((Rewriting.emb (ξ := Nat)
            compactBinaryNatRunningStatusSliceDef.val) ⇜
          statusTerms)).length <=
        compactBinaryNatStatusRawRunningFormulaCodePolynomial bitBound := by
    simpa only [termCode,
      compactBinaryNatStatusRawRunningFormulaCodePolynomial] using hrunningRaw
  have hfailedRaw := statusRawEmbeddedSubstitution_code_length_le_uniform
    compactBinaryNatFailedStatusSliceDef.val statusTerms termCode hstatusTerms
  have hfailed :
      (binaryFormulaCode
        ((Rewriting.emb (ξ := Nat)
            compactBinaryNatFailedStatusSliceDef.val) ⇜
          statusTerms)).length <=
        compactBinaryNatStatusRawFailedFormulaCodePolynomial bitBound := by
    simpa only [termCode,
      compactBinaryNatStatusRawFailedFormulaCodePolynomial] using hfailedRaw
  have hprefixRaw := statusRawEmbeddedSubstitution_code_length_le_uniform
    compactBinaryNatCompletedStatusPrefixDef.val prefixTerms termCode
      hprefixTerms
  have hprefix :
      (binaryFormulaCode
        ((Rewriting.emb (ξ := Nat)
            compactBinaryNatCompletedStatusPrefixDef.val) ⇜
          prefixTerms)).length <=
        compactBinaryNatStatusRawCompletedPrefixFormulaCodePolynomial
          bitBound := by
    simpa only [termCode,
      compactBinaryNatStatusRawCompletedPrefixFormulaCodePolynomial] using
        hprefixRaw
  have hlayoutRaw := statusRawEmbeddedSubstitution_code_length_le_uniform
    compactAdditiveStructuredListLayoutDef.val layoutTerms termCode
      hlayoutTerms
  have hlayout :
      (binaryFormulaCode
        ((Rewriting.emb (ξ := Nat)
            compactAdditiveStructuredListLayoutDef.val) ⇜
          layoutTerms)).length <=
        compactBinaryNatStatusRawCompletedLayoutFormulaCodePolynomial
          bitBound := by
    simpa only [termCode,
      compactBinaryNatStatusRawCompletedLayoutFormulaCodePolynomial] using
        hlayoutRaw
  have hunitRaw := statusRawEmbeddedSubstitution_code_length_le_uniform
    compactAdditiveUnitBoundaryRowsDef.val unitTerms termCode hunitTerms
  have hunit :
      (binaryFormulaCode
        ((Rewriting.emb (ξ := Nat)
            compactAdditiveUnitBoundaryRowsDef.val) ⇜
          unitTerms)).length <=
        compactBinaryNatStatusRawCompletedUnitFormulaCodePolynomial
          bitBound := by
    simpa only [termCode,
      compactBinaryNatStatusRawCompletedUnitFormulaCodePolynomial] using
        hunitRaw
  have hsizeRaw := statusRawEmbeddedSubstitution_code_length_le_uniform
    compactNatSizeDef.val sizeTerms termCode hsizeTerms
  have hsize :
      (binaryFormulaCode
        ((Rewriting.emb (ξ := Nat) compactNatSizeDef.val) ⇜
          sizeTerms)).length <=
        compactBinaryNatStatusRawCompletedSizeFormulaCodePolynomial
          bitBound := by
    simpa only [termCode,
      compactBinaryNatStatusRawCompletedSizeFormulaCodePolynomial] using
        hsizeRaw
  have hareaRaw := statusRawEmbeddedSubstitution_code_length_le_uniform
    compactBinaryNatStatusAreaSourceFormula areaTerms termCode hareaTerms
  have harea :
      (binaryFormulaCode
        (“#1 ≤ (#0 + 1) *
          !!(closedShift 4 (shortBinaryNumeralTerm tokenCount))” :
          ArithmeticSemiformula Nat 4)).length <=
        compactBinaryNatStatusRawCompletedAreaFormulaCodePolynomial
          bitBound := by
    rw [← compactBinaryNatStatusRawAreaFormula_alignment tokenCount]
    simpa only [areaTerms, termCode,
      compactBinaryNatStatusRawCompletedAreaFormulaCodePolynomial] using
        hareaRaw
  rw [compactBinaryNatStatusValidBoundedRawTerminal_eq_publicShiftFormula]
  unfold compactBinaryNatStatusValidBoundedRawTerminalPublicShiftFormula
    compactBinaryNatStatusRawTerminalFormulaCodePolynomial
  dsimp only [statusTerms, prefixTerms, layoutTerms, unitTerms, sizeTerms] at hrunning hfailed hprefix hlayout hunit hsize
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem
    compactBinaryNatStatusValidBoundedRawTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount start finish : Nat) :
    (compactBinaryNatStatusValidBoundedRawTerminal tokenTable width tokenCount
      start finish).freeVariables = ∅ := by
  have htokenTableShift :
      (closedShift 4
        (shortBinaryNumeralTerm tokenTable)).freeVariables = ∅ :=
    closedShift_freeVariables_eq_empty 4 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable)
  have hwidthShift :
      (closedShift 4 (shortBinaryNumeralTerm width)).freeVariables = ∅ :=
    closedShift_freeVariables_eq_empty 4 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty width)
  have htokenCountShift :
      (closedShift 4
        (shortBinaryNumeralTerm tokenCount)).freeVariables = ∅ :=
    closedShift_freeVariables_eq_empty 4 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
  have hstartShift :
      (closedShift 4 (shortBinaryNumeralTerm start)).freeVariables = ∅ :=
    closedShift_freeVariables_eq_empty 4 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty start)
  have hfinishShift :
      (closedShift 4 (shortBinaryNumeralTerm finish)).freeVariables = ∅ :=
    closedShift_freeVariables_eq_empty 4 _
      (shortBinaryNumeralTerm_freeVariables_eq_empty finish)
  let statusTerms : Fin 5 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
      closedShift 4 (shortBinaryNumeralTerm width),
      closedShift 4 (shortBinaryNumeralTerm tokenCount),
      closedShift 4 (shortBinaryNumeralTerm start),
      closedShift 4 (shortBinaryNumeralTerm finish)]
  have hstatusTerms : forall coordinate,
      (statusTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTableShift
    · exact hwidthShift
    · exact htokenCountShift
    · exact hstartShift
    · exact hfinishShift
  let prefixTerms : Fin 5 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
      closedShift 4 (shortBinaryNumeralTerm width),
      closedShift 4 (shortBinaryNumeralTerm tokenCount),
      closedShift 4 (shortBinaryNumeralTerm start), #3]
  have hprefixTerms : forall coordinate,
      (prefixTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTableShift
    · exact hwidthShift
    · exact htokenCountShift
    · exact hstartShift
    · change (#3 : ArithmeticSemiterm Nat 4).freeVariables = ∅
      simp
  let layoutTerms : Fin 7 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
      closedShift 4 (shortBinaryNumeralTerm width),
      closedShift 4 (shortBinaryNumeralTerm tokenCount), #3, #0,
      closedShift 4 (shortBinaryNumeralTerm finish), #2]
  have hlayoutTerms : forall coordinate,
      (layoutTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact htokenTableShift
    · exact hwidthShift
    · exact htokenCountShift
    · change (#3 : ArithmeticSemiterm Nat 4).freeVariables = ∅
      simp
    · change (#0 : ArithmeticSemiterm Nat 4).freeVariables = ∅
      simp
    · exact hfinishShift
    · change (#2 : ArithmeticSemiterm Nat 4).freeVariables = ∅
      simp
  let unitTerms : Fin 3 -> ArithmeticSemiterm Nat 4 :=
    ![closedShift 4 (shortBinaryNumeralTerm tokenCount), #0, #2]
  have hunitTerms : forall coordinate,
      (unitTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact htokenCountShift
    · change (#0 : ArithmeticSemiterm Nat 4).freeVariables = ∅
      simp
    · change (#2 : ArithmeticSemiterm Nat 4).freeVariables = ∅
      simp
  let sizeTerms : Fin 2 -> ArithmeticSemiterm Nat 4 := ![#1, #2]
  have hsizeTerms : forall coordinate,
      (sizeTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · change (#1 : ArithmeticSemiterm Nat 4).freeVariables = ∅
      simp
    · change (#2 : ArithmeticSemiterm Nat 4).freeVariables = ∅
      simp
  let areaTerms : Fin 3 -> ArithmeticSemiterm Nat 4 :=
    ![#0, closedShift 4 (shortBinaryNumeralTerm tokenCount), #1]
  have hareaTerms : forall coordinate,
      (areaTerms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · change (#0 : ArithmeticSemiterm Nat 4).freeVariables = ∅
      simp
    · exact htokenCountShift
    · change (#1 : ArithmeticSemiterm Nat 4).freeVariables = ∅
      simp
  have hrunning :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactBinaryNatRunningStatusSliceDef.val statusTerms hstatusTerms
  have hfailed :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactBinaryNatFailedStatusSliceDef.val statusTerms hstatusTerms
  have hprefix :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactBinaryNatCompletedStatusPrefixDef.val prefixTerms hprefixTerms
  have hlayout :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactAdditiveStructuredListLayoutDef.val layoutTerms hlayoutTerms
  have hunit :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactAdditiveUnitBoundaryRowsDef.val unitTerms hunitTerms
  have hsize :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactNatSizeDef.val sizeTerms hsizeTerms
  have hareaRaw :=
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
      compactBinaryNatStatusAreaSourceFormula areaTerms hareaTerms
  have harea :
      (“#1 ≤ (#0 + 1) *
        !!(closedShift 4 (shortBinaryNumeralTerm tokenCount))” :
        ArithmeticSemiformula Nat 4).freeVariables = ∅ := by
    rw [← compactBinaryNatStatusRawAreaFormula_alignment tokenCount]
    simpa only [areaTerms] using hareaRaw
  rw [compactBinaryNatStatusValidBoundedRawTerminal_eq_publicShiftFormula]
  unfold compactBinaryNatStatusValidBoundedRawTerminalPublicShiftFormula
  dsimp only [statusTerms, prefixTerms, layoutTerms, unitTerms, sizeTerms] at hrunning hfailed hprefix hlayout hunit hsize
  simp only [LO.FirstOrder.Semiformula.freeVariables_or,
    LO.FirstOrder.Semiformula.freeVariables_and, hrunning, hfailed, hprefix,
    hlayout, hunit, hsize, harea]
  simp

private theorem boundedWitnessNumeralTermCodeEnvelope_mono_status
    {small large : Nat} (hbound : small <= large) :
    boundedWitnessNumeralTermCodeEnvelope small <=
      boundedWitnessNumeralTermCodeEnvelope large := by
  unfold boundedWitnessNumeralTermCodeEnvelope
  exact binaryNumeralTermCodeEnvelope_mono_short (Nat.size_le_size hbound)

private theorem uniformRewritingFormulaCodeEnvelope_mono_status
    {smallImage largeImage smallFormula largeFormula : Nat}
    (himage : smallImage <= largeImage)
    (hformula : smallFormula <= largeFormula) :
    uniformRewritingFormulaCodeEnvelope smallImage smallFormula <=
      uniformRewritingFormulaCodeEnvelope largeImage largeFormula := by
  unfold uniformRewritingFormulaCodeEnvelope
  gcongr

private theorem
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_status
    (contextCodeBound : Nat)
    {smallBound largeBound smallBody largeBody : Nat}
    (hbound : smallBound <= largeBound)
    (hbody : smallBody <= largeBody) :
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
        smallBound smallBody <=
      explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
        largeBound largeBody := by
  have hnumeral := boundedWitnessNumeralTermCodeEnvelope_mono_status hbound
  have hlifted : liftedRewritingImageCodeBound
      (boundedWitnessNumeralTermCodeEnvelope smallBound) <=
      liftedRewritingImageCodeBound
        (boundedWitnessNumeralTermCodeEnvelope largeBound) := by
    unfold liftedRewritingImageCodeBound
    omega
  have htail : explicitWitnessBodyAfterTailPublicCodeEnvelope smallBound
        smallBody <=
      explicitWitnessBodyAfterTailPublicCodeEnvelope largeBound
        largeBody := by
    unfold explicitWitnessBodyAfterTailPublicCodeEnvelope
    exact uniformRewritingFormulaCodeEnvelope_mono_status hlifted hbody
  have hinstalled : explicitWitnessInstalledPublicCodeEnvelope smallBound
        smallBody <=
      explicitWitnessInstalledPublicCodeEnvelope largeBound largeBody := by
    unfold explicitWitnessInstalledPublicCodeEnvelope
    exact uniformRewritingFormulaCodeEnvelope_mono_status hnumeral hbody
  have hsuccessor : boundedWitnessSuccessorTermCodeEnvelope smallBound <=
      boundedWitnessSuccessorTermCodeEnvelope largeBound := by
    unfold boundedWitnessSuccessorTermCodeEnvelope
    omega
  have hshifted : boundedWitnessShiftedSuccessorTermCodeEnvelope smallBound <=
      boundedWitnessShiftedSuccessorTermCodeEnvelope largeBound := by
    unfold boundedWitnessShiftedSuccessorTermCodeEnvelope
    exact Nat.mul_le_mul_left 3 hsuccessor
  have hguardCode : boundedWitnessGuardFormulaCodeEnvelope smallBound <=
      boundedWitnessGuardFormulaCodeEnvelope largeBound := by
    unfold boundedWitnessGuardFormulaCodeEnvelope
    omega
  have hopenGuard : boundedWitnessOpenGuardFormulaCodeEnvelope smallBound <=
      boundedWitnessOpenGuardFormulaCodeEnvelope largeBound := by
    unfold boundedWitnessOpenGuardFormulaCodeEnvelope
    omega
  have hmatrix : explicitBoundedWitnessMatrixPublicCodeEnvelope smallBound
        smallBody <=
      explicitBoundedWitnessMatrixPublicCodeEnvelope largeBound largeBody := by
    unfold explicitBoundedWitnessMatrixPublicCodeEnvelope
    omega
  have hbounded :
      explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope smallBound
          smallBody <=
        explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope largeBound
          largeBody := by
    unfold explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope
    omega
  have hinstantiated :
      explicitBoundedWitnessInstantiatedPublicCodeEnvelope smallBound
          smallBody <=
        explicitBoundedWitnessInstantiatedPublicCodeEnvelope largeBound
          largeBody := by
    unfold explicitBoundedWitnessInstantiatedPublicCodeEnvelope
    exact substitutionFormulaCodeEnvelope_mono_local hbounded hnumeral
  have hexistential :
      explicitBoundedWitnessExistentialPublicCodeEnvelope smallBound
          smallBody <=
        explicitBoundedWitnessExistentialPublicCodeEnvelope largeBound
          largeBody := by
    unfold explicitBoundedWitnessExistentialPublicCodeEnvelope
    omega
  have hsyntax :
      explicitBoundedWitnessDirectHeadPublicSyntaxResource contextCodeBound
          smallBound smallBody <=
        explicitBoundedWitnessDirectHeadPublicSyntaxResource contextCodeBound
          largeBound largeBody := by
    unfold explicitBoundedWitnessDirectHeadPublicSyntaxResource
    omega
  have hsize : Nat.size smallBound <= Nat.size largeBound :=
    Nat.size_le_size hbound
  have hguardWidth : boundedWitnessGuardUniformBitWidth smallBound <=
      boundedWitnessGuardUniformBitWidth largeBound := by
    unfold boundedWitnessGuardUniformBitWidth boundedWitnessGuardBitWidth
    omega
  have hguardPayload :=
    boundedWitnessGuardPayloadPolynomial_mono_uniform hguardWidth
  have hassembly := generalContextAssemblyEnvelope_mono_uniform hsyntax
  unfold explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
  omega

private theorem explicitBoundedWitnessDirectPublicPayloadEnvelope_four_mono
    (contextCodeBound terminalResource : Nat)
    {smallBound largeBound smallBody largeBody : Nat}
    (hbound : smallBound <= largeBound)
    (hbody : smallBody <= largeBody) :
    explicitBoundedWitnessDirectPublicPayloadEnvelope 4 contextCodeBound
        smallBound smallBody terminalResource <=
      explicitBoundedWitnessDirectPublicPayloadEnvelope 4 contextCodeBound
        largeBound largeBody terminalResource := by
  have hbody1 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_completed 3
      hbound hbody
  have hbody2 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_completed 2
      hbound hbody1
  have hbody3 :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_completed 1
      hbound hbody2
  have hhead0 :=
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_status
      contextCodeBound hbound hbody
  have hhead1 :=
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_status
      contextCodeBound hbound hbody1
  have hhead2 :=
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_status
      contextCodeBound hbound hbody2
  have hhead3 :=
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono_status
      contextCodeBound hbound hbody3
  change
    terminalResource +
          explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
            contextCodeBound smallBound smallBody +
        explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
          contextCodeBound smallBound
          (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3
            smallBound smallBody) +
      explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
        contextCodeBound smallBound
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 smallBound
          (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 smallBound
            smallBody)) +
      explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
        contextCodeBound smallBound
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 smallBound
          (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 smallBound
            (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3
              smallBound smallBody))) <=
    terminalResource +
          explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
            contextCodeBound largeBound largeBody +
        explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
          contextCodeBound largeBound
          (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3
            largeBound largeBody) +
      explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
        contextCodeBound largeBound
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 largeBound
          (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3 largeBound
            largeBody)) +
      explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
        contextCodeBound largeBound
        (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 largeBound
          (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2 largeBound
            (explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 3
              largeBound largeBody)))
  omega

def compactBinaryNatStatusTerminalFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound +
    binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial
      numericBound bitBound +
    compactBinaryNatCompletedStatusFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    4 * generalContextAssemblyEnvelope
      (compactBinaryNatStatusTerminalSyntaxPolynomial bitBound)

noncomputable def
    compactBinaryNatStatusValidBoundedUniformDirectFixedTerminalBoundOfCanonicalBundle
    (tokenTable width tokenCount start finish valueBound numericBound bitBound :
      Nat)
    (bundle : CompactBinaryNatStatusValidBoundedCanonicalDataBundle
      tokenTable width tokenCount start finish valueBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstartValue : start <= numericBound)
    (hfinishValue : finish <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound statusFixedZeroValuation
      (compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula
        tokenTable width tokenCount start finish bundle.data.outputStart
        bundle.data.outputBoundary bundle.data.outputBoundarySize
        bundle.data.outputCount)
      (compactBinaryNatStatusTerminalFixedPayloadPolynomial numericBound
        bitBound) := by
  let data := bundle.data
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let failedFormula := compactBinaryNatFailedStatusSliceClosedFormula
    tokenTable width tokenCount start finish
  let completedFormula := compactBinaryNatCompletedStatusUniformDirectFormula
    tokenTable width tokenCount start finish data.outputStart
    data.outputBoundary data.outputBoundarySize data.outputCount
  let innerFormula := failedFormula ⋎ completedFormula
  let terminalFormula := runningFormula ⋎ innerFormula
  let runningResource :=
    compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound
  let failedResource := binaryNatStatusDoubleSliceFullyUniformPayloadPolynomial
    numericBound bitBound
  let completedResource :=
    compactBinaryNatCompletedStatusFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let syntaxResource := compactBinaryNatStatusTerminalSyntaxPolynomial bitBound
  let innerGeneral := hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (failedResource + completedResource)
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidthValue).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstartSize : Nat.size start <= bitBound :=
    (Nat.size_le_size hstartValue).trans hnumericSize
  have hfinishSize : Nat.size finish <= bitBound :=
    (Nat.size_le_size hfinishValue).trans hnumericSize
  have houtputStartValue : data.outputStart <= numericBound :=
    bundle.outputStart_le_tokenCount.trans htokenCount
  have houtputCountValue : data.outputCount <= numericBound :=
    bundle.outputCount_le_tokenCount.trans htokenCount
  have houtputStartSize : Nat.size data.outputStart <= bitBound :=
    (Nat.size_le_size houtputStartValue).trans hnumericSize
  have houtputCountSize : Nat.size data.outputCount <= bitBound :=
    (Nat.size_le_size houtputCountValue).trans hnumericSize
  have hboundaryTableSize : Nat.size data.outputBoundary <= bitBound :=
    bundle.outputBoundary_size_le_area.trans hareaBit
  have houtputBoundarySizeValue : data.outputBoundarySize <= numericBound :=
    bundle.outputBoundarySize_le_area.trans hareaNumeric
  have houtputBoundarySizeSize : Nat.size data.outputBoundarySize <= bitBound :=
    (Nat.size_le_size houtputBoundarySizeValue).trans hnumericSize
  have hrunningCode : (binaryFormulaCode runningFormula).length <=
      compactBinaryNatRunningStatusFormulaCodePolynomial bitBound := by
    simpa only [runningFormula] using
      compactBinaryNatRunningStatusFormula_code_length_le_fixed tokenTable width
        tokenCount start finish bitBound htokenTableSize hwidthSize
        htokenCountSize hstartSize hfinishSize
  have hfailedCode : (binaryFormulaCode failedFormula).length <=
      compactBinaryNatFailedStatusFormulaCodePolynomial bitBound := by
    simpa only [failedFormula] using
      compactBinaryNatFailedStatusFormula_code_length_le_fixed tokenTable width
        tokenCount start finish bitBound htokenTableSize hwidthSize
        htokenCountSize hstartSize hfinishSize
  have hcompletedCode : (binaryFormulaCode completedFormula).length <=
      compactBinaryNatCompletedStatusFormulaCodePolynomial bitBound := by
    simpa only [completedFormula] using
      compactBinaryNatCompletedStatusFormula_code_length_le_fixed tokenTable
        width tokenCount start finish data.outputStart data.outputBoundary
        data.outputBoundarySize data.outputCount bitBound htokenTableSize
        hwidthSize htokenCountSize hstartSize hfinishSize houtputStartSize
        houtputCountSize hboundaryTableSize houtputBoundarySizeSize
  have hinnerCode : (binaryFormulaCode innerFormula).length <= syntaxResource := by
    dsimp only [innerFormula]
    simp only [binaryFormulaCode, List.length_append]
    dsimp only [syntaxResource]
    unfold compactBinaryNatStatusTerminalSyntaxPolynomial
    omega
  have hterminalCode : (binaryFormulaCode terminalFormula).length <=
      syntaxResource := by
    simpa only [terminalFormula, innerFormula, runningFormula, failedFormula,
      completedFormula, syntaxResource,
      compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula] using
      compactBinaryNatStatusTerminalFormula_code_length_le_fixed tokenTable
        width tokenCount start finish data.outputStart data.outputBoundary
        data.outputBoundarySize data.outputCount bitBound htokenTableSize
        hwidthSize htokenCountSize hstartSize hfinishSize houtputStartSize
        houtputCountSize hboundaryTableSize houtputBoundarySizeSize
  have hrunningSyntax : (binaryFormulaCode runningFormula).length <=
      syntaxResource := hrunningCode.trans (by
    dsimp only [syntaxResource]
    unfold compactBinaryNatStatusTerminalSyntaxPolynomial
    omega)
  have hfailedSyntax : (binaryFormulaCode failedFormula).length <=
      syntaxResource := hfailedCode.trans (by
    dsimp only [syntaxResource]
    unfold compactBinaryNatStatusTerminalSyntaxPolynomial
    omega)
  have hcompletedSyntax : (binaryFormulaCode completedFormula).length <=
      syntaxResource := hcompletedCode.trans (by
    dsimp only [syntaxResource]
    unfold compactBinaryNatStatusTerminalSyntaxPolynomial
    omega)
  have hrunningClosed : runningFormula.freeVariables = ∅ := by
    simpa only [runningFormula] using
      compactBinaryNatRunningStatusFormula_freeVariables_eq_empty tokenTable
        width tokenCount start finish
  have hfailedClosed : failedFormula.freeVariables = ∅ := by
    simpa only [failedFormula] using
      compactBinaryNatFailedStatusSliceClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount start finish
  have hcompletedClosed : completedFormula.freeVariables = ∅ := by
    simpa only [completedFormula] using
      compactBinaryNatCompletedStatusFormula_freeVariables_eq_empty tokenTable
        width tokenCount start finish data.outputStart data.outputBoundary
        data.outputBoundarySize data.outputCount
  have hinnerClosed : innerFormula.freeVariables = ∅ := by
    dsimp only [innerFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hfailedClosed,
      hcompletedClosed]
    simp
  have hterminalClosed : terminalFormula.freeVariables = ∅ := by
    simpa only [terminalFormula, innerFormula, runningFormula, failedFormula,
      completedFormula,
      compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula] using
      compactBinaryNatStatusTerminalFormula_freeVariables_eq_empty tokenTable
        width tokenCount start finish data.outputStart data.outputBoundary
        data.outputBoundarySize data.outputCount
  have hsyntaxPositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold compactBinaryNatStatusTerminalSyntaxPolynomial
    omega
  have hinnerContext : formulaCodeSum
      (valuationContext innerFormula.freeVariables statusFixedZeroValuation) <=
        syntaxResource := by
    rw [hinnerClosed]
    simp [valuationContext, formulaCodeSum]
  have hterminalContext : formulaCodeSum
      (valuationContext terminalFormula.freeVariables statusFixedZeroValuation) <=
        syntaxResource := by
    rw [hterminalClosed]
    simp [valuationContext, formulaCodeSum]
  by_cases hrunning : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish
  · let runningCertificate :=
      compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount start finish hrunning
    let runningProof := runningCertificate.compile
    let direct := compileDirectDisjunctionLeft
      (right := innerFormula) runningProof
    have hrunningProof : runningProof.payloadLength <= runningResource :=
      (compile_payloadLength_le_structuralPayloadBound runningCertificate).trans
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
          tokenTable width tokenCount start finish numericBound bitBound
          hwidthValue hstartValue htokenTableSize hwidthSize htokenCountSize
          hstartSize hfinishSize hrunning)
    have hraw := compileDirectDisjunctionLeft_payloadLength_le
      (right := innerFormula) runningProof runningResource hrunningProof
    have henvelope :=
      transparentHybridDisjunctionLeftPayloadEnvelope_le_general
        statusFixedZeroValuation runningFormula innerFormula runningResource
        syntaxResource hsyntaxPositive hterminalContext hrunningSyntax
        hinnerCode hterminalCode
    refine { proof := direct, payloadLength_le := ?_ }
    exact (hraw.trans henvelope).trans (by
      dsimp only [direct, runningResource, failedResource, completedResource,
        syntaxResource]
      unfold compactBinaryNatStatusTerminalFixedPayloadPolynomial
        hybridDisjunctionGeneralPayloadEnvelope
      omega)
  · by_cases hfailed : CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount start finish
    · have hdeterministic :=
        compactBinaryNatFailedStatusSlice_deterministicWitness tokenTable width
          tokenCount start finish hfailed
      have hinnerValue : start + 1 <= numericBound :=
        hdeterministic.1.trans htokenCount
      have hinnerSize : Nat.size (start + 1) <= bitBound :=
        (Nat.size_le_size hinnerValue).trans hnumericSize
      let failedCertificate :=
        compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start finish hfailed
      let failedProof := failedCertificate.compile
      let inner := compileDirectDisjunctionLeft
        (right := completedFormula) failedProof
      let direct := compileDirectDisjunctionRight
        (left := runningFormula) inner
      have hfailedProof : failedProof.payloadLength <= failedResource :=
        (compile_payloadLength_le_structuralPayloadBound failedCertificate).trans
          (compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
            tokenTable width tokenCount start finish numericBound bitBound
            hwidthValue hstartValue hinnerValue htokenTableSize hwidthSize
            htokenCountSize hstartSize hfinishSize hinnerSize hbitPositive
            hfailed)
      have hinnerRaw := compileDirectDisjunctionLeft_payloadLength_le
        (right := completedFormula) failedProof failedResource hfailedProof
      have hinnerEnvelope :=
        transparentHybridDisjunctionLeftPayloadEnvelope_le_general
          statusFixedZeroValuation failedFormula completedFormula failedResource
          syntaxResource hsyntaxPositive hinnerContext hfailedSyntax
          hcompletedSyntax hinnerCode
      have hinnerPayload : inner.payloadLength <= innerGeneral :=
        (hinnerRaw.trans hinnerEnvelope).trans (by
          dsimp only [innerGeneral]
          unfold hybridDisjunctionGeneralPayloadEnvelope
          omega)
      have houterRaw := compileDirectDisjunctionRight_payloadLength_le
        (left := runningFormula) inner innerGeneral hinnerPayload
      have houterEnvelope :=
        transparentHybridDisjunctionRightPayloadEnvelope_le_general
          statusFixedZeroValuation runningFormula innerFormula innerGeneral
          syntaxResource hsyntaxPositive hterminalContext hrunningSyntax
          hinnerCode hterminalCode
      refine { proof := direct, payloadLength_le := ?_ }
      exact (houterRaw.trans houterEnvelope).trans (by
        dsimp only [direct, innerGeneral, runningResource, failedResource,
          completedResource, syntaxResource]
        unfold compactBinaryNatStatusTerminalFixedPayloadPolynomial
          hybridDisjunctionGeneralPayloadEnvelope
        omega)
    · let hcompleted := compactBinaryNatCompletedStatusValidRows_of_data
        data hrunning hfailed
      let completedProof :=
        compileCompactBinaryNatCompletedStatusFullyUniformDirect tokenTable width
          tokenCount start finish data.outputStart data.outputBoundary
          data.outputBoundarySize data.outputCount numericBound bitBound
          hcompleted htokenCount houtputCountValue hboundaryTableSize
          hnumericSize
      let inner := compileDirectDisjunctionRight
        (left := failedFormula) completedProof
      let direct := compileDirectDisjunctionRight
        (left := runningFormula) inner
      have hcompletedProof : completedProof.payloadLength <=
          completedResource :=
        compileCompactBinaryNatCompletedStatusFullyUniformDirect_payloadLength_le_fixed
          tokenTable width tokenCount start finish data.outputStart
          data.outputBoundary data.outputBoundarySize data.outputCount
          numericBound bitBound hcompleted hwidthValue htokenCount
          houtputCountValue htokenTableSize hboundaryTableSize hnumericSize
          hbitPositive
      have hinnerRaw := compileDirectDisjunctionRight_payloadLength_le
        (left := failedFormula) completedProof completedResource hcompletedProof
      have hinnerEnvelope :=
        transparentHybridDisjunctionRightPayloadEnvelope_le_general
          statusFixedZeroValuation failedFormula completedFormula
          completedResource syntaxResource hsyntaxPositive hinnerContext
          hfailedSyntax hcompletedSyntax hinnerCode
      have hinnerPayload : inner.payloadLength <= innerGeneral :=
        (hinnerRaw.trans hinnerEnvelope).trans (by
          dsimp only [innerGeneral]
          unfold hybridDisjunctionGeneralPayloadEnvelope
          omega)
      have houterRaw := compileDirectDisjunctionRight_payloadLength_le
        (left := runningFormula) inner innerGeneral hinnerPayload
      have houterEnvelope :=
        transparentHybridDisjunctionRightPayloadEnvelope_le_general
          statusFixedZeroValuation runningFormula innerFormula innerGeneral
          syntaxResource hsyntaxPositive hterminalContext hrunningSyntax
          hinnerCode hterminalCode
      refine { proof := direct, payloadLength_le := ?_ }
      exact (houterRaw.trans houterEnvelope).trans (by
        dsimp only [direct, innerGeneral, runningResource, failedResource,
          completedResource, syntaxResource]
        unfold compactBinaryNatStatusTerminalFixedPayloadPolynomial
          hybridDisjunctionGeneralPayloadEnvelope
        omega)

def compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 4 0 numericBound
    (compactBinaryNatStatusRawTerminalFormulaCodePolynomial bitBound)
    (compactBinaryNatStatusTerminalFixedPayloadPolynomial numericBound
      bitBound)

noncomputable def
    compactBinaryNatStatusValidBoundedUniformDirectFixedBoundOfCanonicalBundle
    (tokenTable width tokenCount start finish valueBound numericBound bitBound :
      Nat)
    (bundle : CompactBinaryNatStatusValidBoundedCanonicalDataBundle
      tokenTable width tokenCount start finish valueBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstartValue : start <= numericBound)
    (hfinishValue : finish <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound statusFixedZeroValuation
      (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
        tokenCount start finish valueBound)
      (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
        numericBound bitBound) := by
  let data := bundle.data
  let values := compactBinaryNatStatusValidBoundedValues data
  let rawBody := compactBinaryNatStatusValidBoundedRawTerminal tokenTable width
    tokenCount start finish
  let terminalFormula :=
    compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula tokenTable
      width tokenCount start finish data.outputStart data.outputBoundary
      data.outputBoundarySize data.outputCount
  let bodyCodeBound :=
    compactBinaryNatStatusRawTerminalFormulaCodePolynomial bitBound
  let terminalResource :=
    compactBinaryNatStatusTerminalFixedPayloadPolynomial numericBound bitBound
  let terminalBound :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedTerminalBoundOfCanonicalBundle
      tokenTable width tokenCount start finish valueBound numericBound bitBound
      bundle hwidthValue htokenCount hstartValue hfinishValue hareaNumeric
      hareaBit htokenTableSize hnumericSize hbitPositive
  let terminalRaw := terminalBound.proof
  have hvalueTerms :
      (fun index : Fin 4 => shortBinaryNumeralTerm (values index)) =
        ![shortBinaryNumeralTerm data.outputCount,
          shortBinaryNumeralTerm data.outputBoundarySize,
          shortBinaryNumeralTerm data.outputBoundary,
          shortBinaryNumeralTerm data.outputStart] := by
    funext index
    fin_cases index <;> rfl
  have hterminalFormula : terminalFormula =
      rawBody ⇜ fun index => shortBinaryNumeralTerm (values index) := by
    rw [hvalueTerms]
    simpa only [terminalFormula,
      compactBinaryNatStatusValidBoundedUniformDirectTerminalFormula,
      compactBinaryNatCompletedStatusUniformDirectFormula, rawBody, data,
      values] using
      (compactBinaryNatStatusValidBoundedRawTerminal_alignment tokenTable
        width tokenCount start finish data.outputStart data.outputBoundary
        data.outputBoundarySize data.outputCount).symm
  let terminalProof := castValuationContextProof hterminalFormula terminalRaw
  have hterminalRaw : terminalRaw.payloadLength <= terminalResource := by
    exact terminalBound.payloadLength_le
  have hterminal : terminalProof.payloadLength <= terminalResource := by
    dsimp only [terminalProof]
    rw [castValuationContextProof_payloadLength_eq]
    exact hterminalRaw
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidthValue).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstartSize : Nat.size start <= bitBound :=
    (Nat.size_le_size hstartValue).trans hnumericSize
  have hfinishSize : Nat.size finish <= bitBound :=
    (Nat.size_le_size hfinishValue).trans hnumericSize
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound := by
    simpa only [rawBody, bodyCodeBound] using
      compactBinaryNatStatusValidBoundedRawTerminal_code_length_le_fixed
        tokenTable width tokenCount start finish bitBound htokenTableSize
        hwidthSize htokenCountSize hstartSize hfinishSize
  have hcontext : FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
      (valuationContext rawBody.freeVariables statusFixedZeroValuation) <= 0 := by
    rw [show rawBody.freeVariables = ∅ by
      simpa only [rawBody] using
        compactBinaryNatStatusValidBoundedRawTerminal_freeVariables_eq_empty
          tokenTable width tokenCount start finish]
    simp [valuationContext,
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum]
  let sourceFormula :=
    FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.explicitBoundedWitnessFormula
      (shortBinaryNumeralTerm valueBound) 4 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    0 valueBound bodyCodeBound rawBody values
      (compactBinaryNatStatusValidBoundedValues_le data) hbody hcontext
      terminalResource terminalProof hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity04
      0 valueBound bodyCodeBound rawBody values
      (compactBinaryNatStatusValidBoundedValues_le data) hbody hcontext
      terminalResource terminalProof hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
        tokenCount start finish valueBound :=
    (compactBinaryNatStatusValidBoundedClosedFormula_alignment tokenTable width
      tokenCount start finish valueBound).symm
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  have hcompiled : rawProof.payloadLength <=
      explicitBoundedWitnessDirectPublicPayloadEnvelope 4 0 valueBound
        bodyCodeBound terminalResource := by
    apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
      hcoordinates.1
    exact hcoordinates.2
  have henvelope := explicitBoundedWitnessDirectPublicPayloadEnvelope_four_mono
    0 terminalResource hvalueBound (Nat.le_refl bodyCodeBound)
  exact hcompiled.trans (by
    simpa only [compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial,
      terminalResource, bodyCodeBound] using henvelope)

noncomputable def
    compactBinaryNatStatusValidBoundedUniformDirectFixedBoundOfGraph
    (tokenTable width tokenCount start finish valueBound numericBound bitBound :
      Nat)
    (hgraph : CompactBinaryNatStatusValidBounded tokenTable width tokenCount
      start finish valueBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstartValue : start <= numericBound)
    (hfinishValue : finish <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound statusFixedZeroValuation
      (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
        tokenCount start finish valueBound)
      (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
        numericBound bitBound) :=
  compactBinaryNatStatusValidBoundedUniformDirectFixedBoundOfCanonicalBundle
    tokenTable width tokenCount start finish valueBound numericBound bitBound
    (compactBinaryNatStatusValidBoundedCanonicalDataBundleOfGraph tokenTable
      width tokenCount start finish valueBound hgraph)
    hvalueBound hwidthValue htokenCount hstartValue hfinishValue hareaNumeric
    hareaBit htokenTableSize hnumericSize hbitPositive

noncomputable def
    compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound numericBound bitBound :
      Nat)
    (hgraph : CompactBinaryNatStatusValidBounded tokenTable width tokenCount
      start finish valueBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstartValue : start <= numericBound)
    (hfinishValue : finish <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
          tokenCount start finish valueBound).freeVariables valuation)
      (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
        tokenCount start finish valueBound) := by
  let direct :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedBoundOfGraph tokenTable
      width tokenCount start finish valueBound numericBound bitBound hgraph
      hvalueBound hwidthValue htokenCount hstartValue hfinishValue hareaNumeric
      hareaBit htokenTableSize hnumericSize hbitPositive
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
            tokenCount start finish valueBound).freeVariables
          statusFixedZeroValuation =
        valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
            tokenCount start finish valueBound).freeVariables valuation := by
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext direct.proof

theorem
    compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount start finish valueBound numericBound bitBound :
      Nat)
    (hgraph : CompactBinaryNatStatusValidBounded tokenTable width tokenCount
      start finish valueBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstartValue : start <= numericBound)
    (hfinishValue : finish <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph
      valuation tokenTable width tokenCount start finish valueBound
      numericBound bitBound hgraph hvalueBound hwidthValue htokenCount
      hstartValue hfinishValue hareaNumeric hareaBit htokenTableSize
      hnumericSize hbitPositive).payloadLength <=
      compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
        numericBound bitBound := by
  let direct :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedBoundOfGraph tokenTable
      width tokenCount start finish valueBound numericBound bitBound hgraph
      hvalueBound hwidthValue htokenCount hstartValue hfinishValue hareaNumeric
      hareaBit htokenTableSize hnumericSize hbitPositive
  have hcontext :
      valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
            tokenCount start finish valueBound).freeVariables
          statusFixedZeroValuation =
        valuationContext
          (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
            tokenCount start finish valueBound).freeVariables valuation := by
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  change (CertifiedPAContextProof.castContext hcontext direct.proof).payloadLength
    <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact direct.payloadLength_le

#print axioms
  compactBinaryNatStatusValidBoundedUniformDirectFixedTerminalBoundOfCanonicalBundle
#print axioms
  compactBinaryNatStatusValidBoundedUniformDirectFixedBoundOfGraph
#print axioms
  compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph

end FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectFixedBounds
