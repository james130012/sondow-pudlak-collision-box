import integration.FoundationCompactNumericListedDirectParserSyntaxTermGraphFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
import integration.FoundationCompactListedProofHonestWeight

/-! # Fully fixed selected Term graph endpoint inside SyntaxStep -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxStepTermGraphFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
open FoundationCompactListedProofHonestWeight
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermGraphFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds

private abbrev stepZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate stepZeroValuation formula

def syntaxStepTermSelectedPayloadEnvelope
    (a b c d e f : ValuationFormula) (resource : Nat) : Nat :=
  let inner3 :=
    transparentHybridDisjunctionLeftPayloadEnvelope stepZeroValuation d
      (e ⋎ f) resource
  let inner2 :=
    transparentHybridDisjunctionRightPayloadEnvelope stepZeroValuation c
      (d ⋎ (e ⋎ f)) inner3
  let inner1 :=
    transparentHybridDisjunctionRightPayloadEnvelope stepZeroValuation b
      (c ⋎ (d ⋎ (e ⋎ f))) inner2
  transparentHybridDisjunctionRightPayloadEnvelope stepZeroValuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) inner1

theorem termSelectedPayloadBound_le
    {a b c d e f : ValuationFormula}
    (selected : HybridCertificate d) (resource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (.disjunctionRight (left := a)
          (.disjunctionRight (left := b)
            (.disjunctionRight (left := c)
              (.disjunctionLeft (right := e ⋎ f) selected)))) <=
      syntaxStepTermSelectedPayloadEnvelope a b c d e f resource := by
  let inner3 : HybridCertificate (d ⋎ (e ⋎ f)) :=
    .disjunctionLeft selected
  have hinner3 :=
    transparentHybridDisjunctionLeftPayloadBound_le
      (right := e ⋎ f) selected resource hselected
  let inner2 : HybridCertificate (c ⋎ (d ⋎ (e ⋎ f))) :=
    .disjunctionRight inner3
  have hinner2 :=
    transparentHybridDisjunctionRightPayloadBound_le (left := c) inner3 _
      hinner3
  let inner1 : HybridCertificate (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) :=
    .disjunctionRight inner2
  have hinner1 :=
    transparentHybridDisjunctionRightPayloadBound_le (left := b) inner2 _
      hinner2
  exact
    transparentHybridDisjunctionRightPayloadBound_le (left := a) inner1 _
      hinner1

noncomputable def compactUnifiedParserSyntaxStepCertificateFromTermGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next witness.slot0 witness.term) :
    HybridCertificate
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness) :=
  .disjunctionRight
    (.disjunctionRight
      (.disjunctionRight
        (.disjunctionLeft
          (syntaxTermFullyFixedGraphCertificate tokenTable width tokenCount
            current next witness.slot0 witness.term hgraph))))

theorem
    compactUnifiedParserSyntaxStepCertificateFromTermGraph_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next witness.slot0 witness.term)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hbinderSize : Nat.size witness.slot0 <= bitBound)
    (hwitness :
      CompactUnifiedParserSyntaxTermWitnessCoordinateSizeBound witness.term
        bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxStepCertificateFromTermGraph tokenTable width
          tokenCount current next witness hgraph) <=
      syntaxStepTermSelectedPayloadEnvelope
        (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
          current next witness.done)
        (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
          current next witness.empty)
        (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width
          tokenCount current next witness.slot0 witness.slot1 witness.repeat)
        (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
          current next witness.slot0 witness.term)
        (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width
          tokenCount current next witness.slot0 witness.formula)
        (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width
          tokenCount current next witness.invalid)
        (syntaxTermGraphFullyFixedPayloadPolynomial tokenCount numericBound
          bitBound) := by
  let selected :=
    syntaxTermFullyFixedGraphCertificate tokenTable width tokenCount current next
      witness.slot0 witness.term hgraph
  have hselected :=
    syntaxTermFullyFixedGraphCertificate_structuralPayloadBound_le tokenTable
      width tokenCount current next witness.slot0 numericBound bitBound
      witness.term hgraph hwidth htokenCount hcurrentValue hnextValue
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      hbinderSize hwitness hnumericSize hbitPositive
  have hpath :=
    termSelectedPayloadBound_le
      (a := compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
        current next witness.done)
      (b := compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
        current next witness.empty)
      (c := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width
        tokenCount current next witness.slot0 witness.slot1 witness.repeat)
      (d := compactUnifiedParserSyntaxTermClosedFormula tokenTable width
        tokenCount current next witness.slot0 witness.term)
      (e := compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width
        tokenCount current next witness.slot0 witness.formula)
      (f := compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width
        tokenCount current next witness.invalid)
      selected
      (syntaxTermGraphFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound)
      hselected
  unfold compactUnifiedParserSyntaxStepCertificateFromTermGraph
  exact hpath

theorem
    compactUnifiedParserSyntaxStepCertificateFromTermGraph_structuralPayloadBound_le_closedFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next witness.slot0 witness.term)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (hbinderSize : Nat.size witness.slot0 <= bitBound)
    (hwitness :
      CompactUnifiedParserSyntaxTermWitnessCoordinateSizeBound witness.term
        bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hstepSize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
          tokenCount current next witness coordinate) <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxStepCertificateFromTermGraph tokenTable width
          tokenCount current next witness hgraph) <=
      sixRightDisjunctionPathThreePayloadEnvelope
        (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
        (syntaxTermGraphFullyFixedPayloadPolynomial tokenCount numericBound
          bitBound) := by
  let selected :=
    syntaxTermFullyFixedGraphCertificate tokenTable width tokenCount current next
      witness.slot0 witness.term hgraph
  have hselected :=
    syntaxTermFullyFixedGraphCertificate_structuralPayloadBound_le tokenTable
      width tokenCount current next witness.slot0 numericBound bitBound
      witness.term hgraph hwidth htokenCount hcurrentValue hnextValue
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      hbinderSize hwitness hnumericSize hbitPositive
  have hclosed :=
    compactUnifiedParserSyntaxStepExplicitFormula_freeVariables_eq_empty
      tokenTable width tokenCount current next witness
  have hcode :=
    compactUnifiedParserSyntaxStepExplicitFormula_code_length_le_fixed tokenTable
      width tokenCount current next witness bitBound hstepSize
  have hpositive :
      1 <= compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound :=
    (one_le_binaryFormulaCode_length
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)).trans hcode
  have hpath :=
    sixRightDisjunctionPathThreePayloadBound_le_closedGeneral
      (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount current
        next witness.done)
      (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount current
        next witness.empty)
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.slot1 witness.repeat)
      (compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.term)
      (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.formula)
      (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width tokenCount
        current next witness.invalid)
      selected
      (syntaxTermGraphFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound)
      (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
      hselected hpositive hclosed hcode
  unfold compactUnifiedParserSyntaxStepCertificateFromTermGraph
  exact hpath

end FoundationCompactNumericListedDirectParserSyntaxStepTermGraphFixedBounds
