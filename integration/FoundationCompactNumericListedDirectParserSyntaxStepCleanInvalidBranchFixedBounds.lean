import integration.FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
import integration.FoundationCompactListedProofHonestWeight

/-! # Fixed selected-invalid path inside a clean syntax step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepCleanInvalidBranchFixedBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidFullyFixedBounds
open FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
open FoundationCompactListedProofHonestWeight

private abbrev stepZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate stepZeroValuation formula

def syntaxStepCleanInvalidSelectedPayloadEnvelope
    (a b c d e f : ValuationFormula) (resource : Nat) : Nat :=
  let inner4 :=
    transparentHybridDisjunctionRightPayloadEnvelope stepZeroValuation e f
      resource
  let inner3 :=
    transparentHybridDisjunctionRightPayloadEnvelope stepZeroValuation d
      (e ⋎ f) inner4
  let inner2 :=
    transparentHybridDisjunctionRightPayloadEnvelope stepZeroValuation c
      (d ⋎ (e ⋎ f)) inner3
  let inner1 :=
    transparentHybridDisjunctionRightPayloadEnvelope stepZeroValuation b
      (c ⋎ (d ⋎ (e ⋎ f))) inner2
  transparentHybridDisjunctionRightPayloadEnvelope stepZeroValuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) inner1

private theorem invalidSelectedPayloadBound_le
    {a b c d e f : ValuationFormula}
    (selected : HybridCertificate f) (resource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (.disjunctionRight (left := a)
          (.disjunctionRight (left := b)
            (.disjunctionRight (left := c)
              (.disjunctionRight (left := d)
                (.disjunctionRight (left := e) selected))))) <=
      syntaxStepCleanInvalidSelectedPayloadEnvelope a b c d e f resource := by
  let inner4 : HybridCertificate (e ⋎ f) := .disjunctionRight selected
  have hinner4 :=
    transparentHybridDisjunctionRightPayloadBound_le (left := e) selected _
      hselected
  let inner3 : HybridCertificate (d ⋎ (e ⋎ f)) := .disjunctionRight inner4
  have hinner3 :=
    transparentHybridDisjunctionRightPayloadBound_le (left := d) inner4 _
      hinner4
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

theorem
    compactUnifiedParserSyntaxStepCleanHybridCertificateFromInvalidData_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
      current next witness.invalid)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.invalid.tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxStepCleanHybridCertificateFromData tokenTable
          width tokenCount current next witness (.invalid hgraph)) <=
      syntaxStepCleanInvalidSelectedPayloadEnvelope
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
        (syntaxInvalidFullyFixedPayloadPolynomial tokenCount numericBound
          bitBound) := by
  let selected :=
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current next witness.invalid hgraph
  let a := compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
    current next witness.done
  let b := compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
    current next witness.empty
  let c := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width
    tokenCount current next witness.slot0 witness.slot1 witness.repeat
  let d := compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
    current next witness.slot0 witness.term
  let e := compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width
    tokenCount current next witness.slot0 witness.formula
  let f := compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width
    tokenCount current next witness.invalid
  have hselected :=
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.invalid numericBound
      bitBound hgraph hwidth hwidthBit htokenCount hcurrentValue hnextValue
      htokenTableSize hcurrentSize hnextSize htailBoundarySize hnumericSize
      hbitPositive
  have hpath := invalidSelectedPayloadBound_le
    (a := a) (b := b) (c := c) (d := d) (e := e) (f := f) selected
    (syntaxInvalidFullyFixedPayloadPolynomial tokenCount numericBound bitBound)
    hselected
  simpa only [compactUnifiedParserSyntaxStepCleanHybridCertificateFromData,
    compactUnifiedParserSyntaxStepExplicitFormula, selected, a, b, c, d, e,
    f, id_eq] using hpath

#print axioms
  compactUnifiedParserSyntaxStepCleanHybridCertificateFromInvalidData_structuralPayloadBound_le_fixed

theorem
    compactUnifiedParserSyntaxStepCleanHybridCertificateFromInvalidData_structuralPayloadBound_le_closedFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
      current next witness.invalid)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.invalid.tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hstepSize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
          tokenCount current next witness coordinate) <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxStepCleanHybridCertificateFromData tokenTable
          width tokenCount current next witness (.invalid hgraph)) <=
      sixRightDisjunctionPathFivePayloadEnvelope
        (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
        (syntaxInvalidFullyFixedPayloadPolynomial tokenCount numericBound
          bitBound) := by
  let selected :=
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current next witness.invalid hgraph
  have hselected :=
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.invalid numericBound
      bitBound hgraph hwidth hwidthBit htokenCount hcurrentValue hnextValue
      htokenTableSize hcurrentSize hnextSize htailBoundarySize hnumericSize
      hbitPositive
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
    sixRightDisjunctionPathFivePayloadBound_le_closedGeneral
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
      (syntaxInvalidFullyFixedPayloadPolynomial tokenCount numericBound bitBound)
      (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
      hselected hpositive hclosed hcode
  unfold compactUnifiedParserSyntaxStepCleanHybridCertificateFromData
  exact hpath

end FoundationCompactNumericListedDirectParserSyntaxStepCleanInvalidBranchFixedBounds
