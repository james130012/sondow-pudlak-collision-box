import integration.FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds
import integration.FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Fixed polynomial bounds for additive product splits

The two strict inequalities and the final non-strict inequality are charged to
one short-numeral bit-width coordinate.  The two conjunctions then use one
closed-context syntax coordinate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveProductSplitFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds
open FoundationCompactNumericListedDirectAdditiveTypeLayouts

private abbrev productZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate.zeroValuation

def productSplitAtomicTermCodePolynomial (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound

def productSplitAtomicFormulaCodePolynomial (bitBound : Nat) : Nat :=
  orderAtomicFormulaCodeEnvelope
    (productSplitAtomicTermCodePolynomial bitBound)

def productSplitAtomicFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (productSplitAtomicTermCodePolynomial bitBound)

def productSplitLeSyntaxPolynomial (bitBound : Nat) : Nat :=
  2 * productSplitAtomicFormulaCodePolynomial bitBound +
    4 * (binaryNatCode 5).length + 16

def productSplitLeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (productSplitLeSyntaxPolynomial bitBound)
    (productSplitAtomicFixedPayloadPolynomial bitBound)

def productSplitAssemblySyntaxPolynomial (bitBound : Nat) : Nat :=
  2 * productSplitAtomicFixedPayloadPolynomial bitBound +
    productSplitLeFixedPayloadPolynomial bitBound +
    4 * (binaryNatCode 4).length + 1

def productSplitFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  let syntaxResource := productSplitAssemblySyntaxPolynomial bitBound
  let atomicResource := productSplitAtomicFixedPayloadPolynomial bitBound
  let leResource := productSplitLeFixedPayloadPolynomial bitBound
  let tailResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicResource leResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource atomicResource
    tailResource

private theorem shortNumeralRelation_freeVariables_eq_empty
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : Nat) :
    (LO.FirstOrder.Semiformula.rel relationSymbol
      ![shortBinaryNumeralTerm left,
        shortBinaryNumeralTerm right]).freeVariables = ∅ := by
  ext candidate
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  simp [shortBinaryNumeralTerm_freeVariables_eq_empty]

private theorem shortNumeralRelation_code_length_le_fixed
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel relationSymbol
        ![shortBinaryNumeralTerm left,
          shortBinaryNumeralTerm right])).length <=
      productSplitAtomicFormulaCodePolynomial bitBound := by
  let termCode := productSplitAtomicTermCodePolynomial bitBound
  have hleftCode : (binaryTermCode (shortBinaryNumeralTerm left)).length <=
      termCode := by
    exact binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hrightCode : (binaryTermCode (shortBinaryNumeralTerm right)).length <=
      termCode := by
    exact binaryNumeralTerm_code_length_le_envelope right bitBound hright
  unfold productSplitAtomicFormulaCodePolynomial
    productSplitAtomicTermCodePolynomial
  exact binaryRelationFormula_code_le_orderAtomic relationSymbol
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
    (binaryNumeralTermCodeEnvelope bitBound) hleftCode hrightCode

theorem closedShortLtStructuralPayloadPolynomial_le_fixed
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    closedShortLtStructuralPayloadPolynomial left right <=
      productSplitAtomicFixedPayloadPolynomial bitBound := by
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
  have hfirstCode : (binaryTermCode (args 0)).length <=
      productSplitAtomicTermCodePolynomial bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hsecondCode : (binaryTermCode (args 1)).length <=
      productSplitAtomicTermCodePolynomial bitBound := by
    exact binaryNumeralTerm_code_length_le_envelope right bitBound hright
  unfold closedShortLtStructuralPayloadPolynomial
    productSplitAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadPolynomial_le_fixed
    productZeroValuation Language.ORing.Rel.lt args 0
      (productSplitAtomicTermCodePolynomial bitBound) hfirst hsecond
      (by rfl) hfirstCode hsecondCode

theorem closedShortLeStructuralPayloadPolynomial_le_fixed
    (left right bitBound : Nat)
    (hleft : Nat.size left <= bitBound)
    (hright : Nat.size right <= bitBound) :
    closedShortLeStructuralPayloadPolynomial left right <=
      productSplitLeFixedPayloadPolynomial bitBound := by
  let args : Fin 2 -> ValuationTerm :=
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right]
  let equalityFormula : ValuationFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula : ValuationFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let termCode := productSplitAtomicTermCodePolynomial bitBound
  let atomicCode := productSplitAtomicFormulaCodePolynomial bitBound
  let atomicResource := productSplitAtomicFixedPayloadPolynomial bitBound
  let syntaxResource := productSplitLeSyntaxPolynomial bitBound
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm left).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm right).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hfirstCode : (binaryTermCode (args 0)).length <= termCode :=
    binaryNumeralTerm_code_length_le_envelope left bitBound hleft
  have hsecondCode : (binaryTermCode (args 1)).length <= termCode :=
    binaryNumeralTerm_code_length_le_envelope right bitBound hright
  have hequalityResource :
      compilePositiveRelationPayloadPolynomial productZeroValuation
          Language.Eq.eq args <= atomicResource := by
    exact compilePositiveRelationPayloadPolynomial_le_fixed
      productZeroValuation Language.Eq.eq args 0 termCode hfirst hsecond
      (by rfl) hfirstCode hsecondCode
  have hstrictResource :
      compilePositiveRelationPayloadPolynomial productZeroValuation
          Language.ORing.Rel.lt args <= atomicResource := by
    exact compilePositiveRelationPayloadPolynomial_le_fixed
      productZeroValuation Language.ORing.Rel.lt args 0 termCode hfirst
      hsecond (by rfl) hfirstCode hsecondCode
  have hequalityCode : (binaryFormulaCode equalityFormula).length <=
      atomicCode := by
    simpa only [equalityFormula, args] using
      shortNumeralRelation_code_length_le_fixed Language.Eq.eq left right
        bitBound hleft hright
  have hstrictCode : (binaryFormulaCode strictFormula).length <=
      atomicCode := by
    simpa only [strictFormula, args] using
      shortNumeralRelation_code_length_le_fixed Language.ORing.Rel.lt left right
        bitBound hleft hright
  have htargetCode : (binaryFormulaCode targetFormula).length <=
      syntaxResource := by
    dsimp only [targetFormula]
    simp only [binaryFormulaCode, List.length_append]
    unfold syntaxResource productSplitLeSyntaxPolynomial
    omega
  have hequalitySyntax : (binaryFormulaCode equalityFormula).length <=
      syntaxResource := hequalityCode.trans (by
    unfold syntaxResource productSplitLeSyntaxPolynomial
    omega)
  have hstrictSyntax : (binaryFormulaCode strictFormula).length <=
      syntaxResource := hstrictCode.trans (by
    unfold syntaxResource productSplitLeSyntaxPolynomial
    omega)
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    have hequalityClosed : equalityFormula.freeVariables = ∅ := by
      simpa only [equalityFormula, args] using
        shortNumeralRelation_freeVariables_eq_empty Language.Eq.eq left right
    have hstrictClosed : strictFormula.freeVariables = ∅ := by
      simpa only [strictFormula, args] using
        shortNumeralRelation_freeVariables_eq_empty Language.ORing.Rel.lt left right
    dsimp only [targetFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hequalityClosed,
      hstrictClosed]
    simp
  have hcontext : formulaCodeSum
      (valuationContext targetFormula.freeVariables productZeroValuation) <=
        syntaxResource := by
    rw [htargetClosed]
    simp [valuationContext, formulaCodeSum]
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource productSplitLeSyntaxPolynomial
    omega
  by_cases heq : left = right
  · unfold closedShortLeStructuralPayloadPolynomial
    rw [if_pos heq]
    change transparentHybridDisjunctionLeftPayloadEnvelope
        productZeroValuation equalityFormula strictFormula
        (compilePositiveRelationPayloadPolynomial productZeroValuation
          Language.Eq.eq args) <= _
    have hraw :=
      transparentHybridDisjunctionLeftPayloadEnvelope_le_general
        productZeroValuation equalityFormula strictFormula
        (compilePositiveRelationPayloadPolynomial productZeroValuation
          Language.Eq.eq args) syntaxResource hpositive hcontext
        hequalitySyntax hstrictSyntax htargetCode
    apply hraw.trans
    unfold productSplitLeFixedPayloadPolynomial
      hybridDisjunctionGeneralPayloadEnvelope
    dsimp only [syntaxResource, atomicResource]
    omega
  · unfold closedShortLeStructuralPayloadPolynomial
    rw [if_neg heq]
    change transparentHybridDisjunctionRightPayloadEnvelope
        productZeroValuation equalityFormula strictFormula
        (compilePositiveRelationPayloadPolynomial productZeroValuation
          Language.ORing.Rel.lt args) <= _
    have hraw :=
      transparentHybridDisjunctionRightPayloadEnvelope_le_general
        productZeroValuation equalityFormula strictFormula
        (compilePositiveRelationPayloadPolynomial productZeroValuation
          Language.ORing.Rel.lt args) syntaxResource hpositive hcontext
        hequalitySyntax hstrictSyntax htargetCode
    apply hraw.trans
    unfold productSplitLeFixedPayloadPolynomial
      hybridDisjunctionGeneralPayloadEnvelope
    dsimp only [syntaxResource, atomicResource]
    omega

theorem compactAdditiveProductSplitStructuralPayloadPolynomial_le_fixed
    (tokenCount start middle finish bitBound : Nat)
    (hgraph : CompactAdditiveProductSplit tokenCount start middle finish)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hstart : Nat.size start <= bitBound)
    (hmiddle : Nat.size middle <= bitBound)
    (hfinish : Nat.size finish <= bitBound) :
    compactAdditiveProductSplitStructuralPayloadPolynomial tokenCount start
        middle finish <=
      productSplitFixedPayloadPolynomial bitBound := by
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
  let firstResource := closedShortLtStructuralPayloadPolynomial start middle
  let secondResource := closedShortLtStructuralPayloadPolynomial middle finish
  let lastResource := closedShortLeStructuralPayloadPolynomial finish
    tokenCount
  let atomicFixed := productSplitAtomicFixedPayloadPolynomial bitBound
  let leFixed := productSplitLeFixedPayloadPolynomial bitBound
  let syntaxResource := productSplitAssemblySyntaxPolynomial bitBound
  let tailFixed := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    atomicFixed leFixed
  have hfirstResource : firstResource <= atomicFixed :=
    closedShortLtStructuralPayloadPolynomial_le_fixed start middle bitBound
      hstart hmiddle
  have hsecondResource : secondResource <= atomicFixed :=
    closedShortLtStructuralPayloadPolynomial_le_fixed middle finish bitBound
      hmiddle hfinish
  have hlastResource : lastResource <= leFixed :=
    closedShortLeStructuralPayloadPolynomial_le_fixed finish tokenCount
      bitBound hfinish htokenCount
  let firstCertificate := closedLtCertificate start middle hgraph.1
  let secondCertificate := closedLtCertificate middle finish hgraph.2.1
  let lastCertificate := closedLeCertificate finish tokenCount hgraph.2.2
  have hfirstCompile : firstCertificate.compile.payloadLength <= atomicFixed :=
    (compile_payloadLength_le_structuralPayloadBound firstCertificate).trans
      ((closedLtCertificate_structuralPayloadBound_le_public start middle
        hgraph.1).trans hfirstResource)
  have hsecondCompile : secondCertificate.compile.payloadLength <=
      atomicFixed :=
    (compile_payloadLength_le_structuralPayloadBound secondCertificate).trans
      ((closedLtCertificate_structuralPayloadBound_le_public middle finish
        hgraph.2.1).trans hsecondResource)
  have hlastCompile : lastCertificate.compile.payloadLength <= leFixed :=
    (compile_payloadLength_le_structuralPayloadBound lastCertificate).trans
      ((closedLeCertificate_structuralPayloadBound_le_public finish tokenCount
        hgraph.2.2).trans hlastResource)
  have hfirstCode : (binaryFormulaCode firstFormula).length <= atomicFixed := by
    exact
      (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        firstCertificate.compile).trans hfirstCompile
  have hsecondCode : (binaryFormulaCode secondFormula).length <=
      atomicFixed := by
    exact
      (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        secondCertificate.compile).trans hsecondCompile
  have hlastCode : (binaryFormulaCode lastFormula).length <= leFixed := by
    exact
      (FoundationCompactCertifiedContextProofConclusionCodeBounds.CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        lastCertificate.compile).trans hlastCompile
  have htailCode : (binaryFormulaCode tailFormula).length <=
      atomicFixed + leFixed + (binaryNatCode 4).length := by
    dsimp only [tailFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have houterCode : (binaryFormulaCode (firstFormula ⋏ tailFormula)).length <=
      2 * atomicFixed + leFixed + 2 * (binaryNatCode 4).length := by
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hfirstClosed : firstFormula.freeVariables = ∅ := by
    dsimp only [firstFormula]
    rw [LO.FirstOrder.Semiformula.Operator.lt_def]
    exact shortNumeralRelation_freeVariables_eq_empty
      Language.ORing.Rel.lt start middle
  have hsecondClosed : secondFormula.freeVariables = ∅ := by
    dsimp only [secondFormula]
    rw [LO.FirstOrder.Semiformula.Operator.lt_def]
    exact shortNumeralRelation_freeVariables_eq_empty
      Language.ORing.Rel.lt middle finish
  have hlastClosed : lastFormula.freeVariables = ∅ := by
    dsimp only [lastFormula]
    rw [LO.FirstOrder.Semiformula.Operator.le_def]
    ext candidate
    simp [LO.FirstOrder.Semiformula.freeVariables_or,
      LO.FirstOrder.Semiformula.freeVariables_rel,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
  have htailClosed : tailFormula.freeVariables = ∅ := by
    dsimp only [tailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hsecondClosed,
      hlastClosed]
    simp
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource productSplitAssemblySyntaxPolynomial
    omega
  have hfirstSyntax : (binaryFormulaCode firstFormula).length <=
      syntaxResource := hfirstCode.trans (by
    unfold syntaxResource productSplitAssemblySyntaxPolynomial
    dsimp only [atomicFixed, leFixed]
    omega)
  have hsecondSyntax : (binaryFormulaCode secondFormula).length <=
      syntaxResource := hsecondCode.trans (by
    unfold syntaxResource productSplitAssemblySyntaxPolynomial
    dsimp only [atomicFixed, leFixed]
    omega)
  have hlastSyntax : (binaryFormulaCode lastFormula).length <=
      syntaxResource := hlastCode.trans (by
    unfold syntaxResource productSplitAssemblySyntaxPolynomial
    dsimp only [atomicFixed, leFixed]
    omega)
  have htailSyntax : (binaryFormulaCode tailFormula).length <=
      syntaxResource := htailCode.trans (by
    unfold syntaxResource productSplitAssemblySyntaxPolynomial
    dsimp only [atomicFixed, leFixed]
    omega)
  have houterSyntax :
      (binaryFormulaCode (firstFormula ⋏ tailFormula)).length <=
        syntaxResource := houterCode.trans (by
    unfold syntaxResource productSplitAssemblySyntaxPolynomial
    dsimp only [atomicFixed, leFixed]
    omega)
  have htailMono := transparentHybridConjunctionPayloadEnvelope_mono
    productZeroValuation secondFormula lastFormula hsecondResource
      hlastResource
  have htailGeneral :=
    FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds.transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      productZeroValuation secondFormula lastFormula atomicFixed leFixed
      syntaxResource hpositive hsecondClosed hlastClosed hsecondSyntax
      hlastSyntax htailSyntax
  have htail :
      transparentHybridConjunctionPayloadEnvelope productZeroValuation
          secondFormula lastFormula secondResource lastResource <= tailFixed :=
    htailMono.trans htailGeneral
  have houterMono := transparentHybridConjunctionPayloadEnvelope_mono
    productZeroValuation firstFormula tailFormula hfirstResource htail
  have houterGeneral :=
    FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds.transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      productZeroValuation firstFormula tailFormula atomicFixed tailFixed
      syntaxResource hpositive hfirstClosed htailClosed hfirstSyntax
      htailSyntax houterSyntax
  unfold compactAdditiveProductSplitStructuralPayloadPolynomial
    productSplitFixedPayloadPolynomial
  dsimp only [firstFormula, secondFormula, lastFormula, tailFormula,
    firstResource, secondResource, lastResource, atomicFixed, leFixed,
    syntaxResource, tailFixed] at houterMono houterGeneral ⊢
  exact houterMono.trans houterGeneral

theorem
    compactAdditiveProductSplitExplicitHybridCertificate_payloadLength_le_fixed
    (tokenCount start middle finish bitBound : Nat)
    (hgraph : CompactAdditiveProductSplit tokenCount start middle finish)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hstart : Nat.size start <= bitBound)
    (hmiddle : Nat.size middle <= bitBound)
    (hfinish : Nat.size finish <= bitBound) :
    (compactAdditiveProductSplitExplicitHybridCertificateOfGraph tokenCount
      start middle finish hgraph).compile.payloadLength <=
      productSplitFixedPayloadPolynomial bitBound :=
  (compile_payloadLength_le_structuralPayloadBound
    (compactAdditiveProductSplitExplicitHybridCertificateOfGraph tokenCount
      start middle finish hgraph)).trans
    ((compactAdditiveProductSplitExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenCount start middle finish hgraph).trans
      (compactAdditiveProductSplitStructuralPayloadPolynomial_le_fixed
        tokenCount start middle finish bitBound hgraph htokenCount hstart
        hmiddle hfinish))

#print axioms closedShortLeStructuralPayloadPolynomial_le_fixed
#print axioms
  compactAdditiveProductSplitExplicitHybridCertificate_payloadLength_le_fixed

end FoundationCompactNumericListedDirectAdditiveProductSplitFixedPolynomialBounds
