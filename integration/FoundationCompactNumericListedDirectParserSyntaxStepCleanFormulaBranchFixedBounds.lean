import integration.FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds
import integration.FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
import integration.FoundationCompactListedProofHonestWeight

/-!
# Fixed selected-formula path inside a clean syntax step

The selected formula certificate already has a fixed polynomial bound.  This
module pays the five real disjunction constructors that embed it into the
original six-way syntax-step formula.  The other five selected paths remain
separate obligations.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepCleanFormulaBranchFixedBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphPartsClosedGeneralBounds
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
open FoundationCompactListedProofHonestWeight

private abbrev stepZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate stepZeroValuation formula

def syntaxStepCleanFormulaSelectedPayloadEnvelope
    (a b c d e f : ValuationFormula) (resource : Nat) : Nat :=
  let inner4 :=
    transparentHybridDisjunctionLeftPayloadEnvelope stepZeroValuation e f
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

private theorem formulaSelectedPayloadBound_le
    {a b c d e f : ValuationFormula}
    (selected : HybridCertificate e) (resource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (.disjunctionRight (left := a)
          (.disjunctionRight (left := b)
            (.disjunctionRight (left := c)
              (.disjunctionRight (left := d)
                (.disjunctionLeft (right := f) selected))))) <=
      syntaxStepCleanFormulaSelectedPayloadEnvelope a b c d e f resource := by
  let inner4 : HybridCertificate (e ⋎ f) := .disjunctionLeft selected
  have hinner4 :=
    transparentHybridDisjunctionLeftPayloadBound_le (right := f) selected
      resource hselected
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
    compactUnifiedParserSyntaxStepCleanHybridCertificateFromFormulaData_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next witness.slot0 witness.formula)
    (hwidth : width <= numericBound)
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
    (htailBoundarySize : Nat.size witness.formula.tailBoundary <= bitBound)
    (hbinderAritySize : Nat.size witness.slot0 <= bitBound)
    (hrelationAritySize :
      Nat.size witness.formula.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.formula.relationCode <= bitBound)
    (htagSize : Nat.size witness.formula.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxStepCleanHybridCertificateFromData tokenTable
          width tokenCount current next witness
          (.formula hgraph)) <=
      syntaxStepCleanFormulaSelectedPayloadEnvelope
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
        (cleanParserSyntaxFormulaPartsPayloadPolynomial tokenCount numericBound
          bitBound) := by
  let selected :=
    compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph tokenTable
      width tokenCount current next witness.slot0 witness.formula hgraph
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
    compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.slot0 numericBound
      bitBound witness.formula hgraph hwidth htokenCount hcurrentValue
      hnextValue htokenTableSize hcurrentSize hnextSize htailBoundarySize
      hbinderAritySize hrelationAritySize hrelationCodeSize htagSize
      hnumericSize hbitPositive
  have hpath := formulaSelectedPayloadBound_le
    (a := a) (b := b) (c := c) (d := d) (e := e) (f := f) selected
    (cleanParserSyntaxFormulaPartsPayloadPolynomial tokenCount numericBound
      bitBound) hselected
  simpa only [
    compactUnifiedParserSyntaxStepCleanHybridCertificateFromData,
    compactUnifiedParserSyntaxStepExplicitFormula, selected, a, b, c, d, e,
    f, id_eq] using hpath

#print axioms
  compactUnifiedParserSyntaxStepCleanHybridCertificateFromFormulaData_structuralPayloadBound_le_fixed

theorem
    compactUnifiedParserSyntaxStepCleanHybridCertificateFromFormulaData_structuralPayloadBound_le_closedFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next witness.slot0 witness.formula)
    (hwidth : width <= numericBound)
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
    (htailBoundarySize : Nat.size witness.formula.tailBoundary <= bitBound)
    (hbinderAritySize : Nat.size witness.slot0 <= bitBound)
    (hrelationAritySize :
      Nat.size witness.formula.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.formula.relationCode <= bitBound)
    (htagSize : Nat.size witness.formula.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hstepSize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxStepFormulaEnvironment tokenTable width
          tokenCount current next witness coordinate) <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxStepCleanHybridCertificateFromData tokenTable
          width tokenCount current next witness (.formula hgraph)) <=
      sixRightDisjunctionPathFourPayloadEnvelope
        (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
        (cleanParserSyntaxFormulaPartsPayloadPolynomial tokenCount numericBound
          bitBound) := by
  let selected :=
    compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph tokenTable
      width tokenCount current next witness.slot0 witness.formula hgraph
  have hselected :=
    compactUnifiedParserSyntaxFormulaCleanHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.slot0 numericBound
      bitBound witness.formula hgraph hwidth htokenCount hcurrentValue
      hnextValue htokenTableSize hcurrentSize hnextSize htailBoundarySize
      hbinderAritySize hrelationAritySize hrelationCodeSize htagSize
      hnumericSize hbitPositive
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
    sixRightDisjunctionPathFourPayloadBound_le_closedGeneral
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
      (cleanParserSyntaxFormulaPartsPayloadPolynomial tokenCount numericBound
        bitBound)
      (compactUnifiedParserSyntaxStepFormulaSyntaxFixedPolynomial bitBound)
      hselected hpositive hclosed hcode
  unfold compactUnifiedParserSyntaxStepCleanHybridCertificateFromData
  exact hpath

end FoundationCompactNumericListedDirectParserSyntaxStepCleanFormulaBranchFixedBounds
