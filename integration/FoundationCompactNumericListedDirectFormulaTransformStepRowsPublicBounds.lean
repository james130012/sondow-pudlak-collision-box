import integration.FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserDonePublicBounds
import integration.FoundationCompactNumericListedDirectParserEmptyPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds
import integration.FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGraphPublicFiniteBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resources for one formula-transform step

The six checked semantic branches are charged by their concrete parser and
output-row certificates. No structural resource is supplied by the caller.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDonePublicBounds
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormula
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxInvalidFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds

abbrev stepRowsZeroValuation : Nat -> Nat :=
  compactFormulaTransformStepRowsZeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate stepRowsZeroValuation formula

def fourWayPath0PayloadEnvelope
    (a b c d : ValuationFormula) (resource : Nat) : Nat :=
  transparentHybridDisjunctionLeftPayloadEnvelope stepRowsZeroValuation a
    (b ⋎ (c ⋎ d)) resource

def fourWayPath1PayloadEnvelope
    (a b c d : ValuationFormula) (resource : Nat) : Nat :=
  let inner := transparentHybridDisjunctionLeftPayloadEnvelope
    stepRowsZeroValuation b (c ⋎ d) resource
  transparentHybridDisjunctionRightPayloadEnvelope stepRowsZeroValuation a
    (b ⋎ (c ⋎ d)) inner

def fourWayPath2PayloadEnvelope
    (a b c d : ValuationFormula) (resource : Nat) : Nat :=
  let inner2 := transparentHybridDisjunctionLeftPayloadEnvelope
    stepRowsZeroValuation c d resource
  let inner1 := transparentHybridDisjunctionRightPayloadEnvelope
    stepRowsZeroValuation b (c ⋎ d) inner2
  transparentHybridDisjunctionRightPayloadEnvelope stepRowsZeroValuation a
    (b ⋎ (c ⋎ d)) inner1

def fourWayPath3PayloadEnvelope
    (a b c d : ValuationFormula) (resource : Nat) : Nat :=
  let inner2 := transparentHybridDisjunctionRightPayloadEnvelope
    stepRowsZeroValuation c d resource
  let inner1 := transparentHybridDisjunctionRightPayloadEnvelope
    stepRowsZeroValuation b (c ⋎ d) inner2
  transparentHybridDisjunctionRightPayloadEnvelope stepRowsZeroValuation a
    (b ⋎ (c ⋎ d)) inner1

private theorem fourWayPath0PayloadBound_le
    {a b c d : ValuationFormula}
    (certificate : HybridCertificate a) (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := b ⋎ (c ⋎ d)) certificate) <=
      fourWayPath0PayloadEnvelope a b c d resource := by
  exact transparentHybridDisjunctionLeftPayloadBound_le
    (right := b ⋎ (c ⋎ d)) certificate resource hcertificate

private theorem fourWayPath1PayloadBound_le
    {a b c d : ValuationFormula}
    (certificate : HybridCertificate b) (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := a)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := c ⋎ d) certificate)) <=
      fourWayPath1PayloadEnvelope a b c d resource := by
  let inner := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := c ⋎ d) certificate
  have hinner := transparentHybridDisjunctionLeftPayloadBound_le
    (right := c ⋎ d) certificate resource hcertificate
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := a) inner _ hinner
  simpa only [fourWayPath1PayloadEnvelope, inner] using houter

private theorem fourWayPath2PayloadBound_le
    {a b c d : ValuationFormula}
    (certificate : HybridCertificate c) (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := a)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := b)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right := d) certificate))) <=
      fourWayPath2PayloadEnvelope a b c d resource := by
  let inner2 := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := d) certificate
  have hinner2 := transparentHybridDisjunctionLeftPayloadBound_le
    (right := d) certificate resource hcertificate
  let inner1 := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := b) inner2
  have hinner1 := transparentHybridDisjunctionRightPayloadBound_le
    (left := b) inner2 _ hinner2
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := a) inner1 _ hinner1
  simpa only [fourWayPath2PayloadEnvelope, inner2, inner1] using houter

private theorem fourWayPath3PayloadBound_le
    {a b c d : ValuationFormula}
    (certificate : HybridCertificate d) (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := a)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := b)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := c) certificate))) <=
      fourWayPath3PayloadEnvelope a b c d resource := by
  let inner2 := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := c) certificate
  have hinner2 := transparentHybridDisjunctionRightPayloadBound_le
    (left := c) certificate resource hcertificate
  let inner1 := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := b) inner2
  have hinner1 := transparentHybridDisjunctionRightPayloadBound_le
    (left := b) inner2 _ hinner2
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := a) inner1 _ hinner1
  simpa only [fourWayPath3PayloadEnvelope, inner2, inner1] using houter

def threeWayPath0PayloadEnvelope
    (a b c : ValuationFormula) (resource : Nat) : Nat :=
  transparentHybridDisjunctionLeftPayloadEnvelope stepRowsZeroValuation a
    (b ⋎ c) resource

def threeWayPath1PayloadEnvelope
    (a b c : ValuationFormula) (resource : Nat) : Nat :=
  let inner := transparentHybridDisjunctionLeftPayloadEnvelope
    stepRowsZeroValuation b c resource
  transparentHybridDisjunctionRightPayloadEnvelope stepRowsZeroValuation a
    (b ⋎ c) inner

def threeWayPath2PayloadEnvelope
    (a b c : ValuationFormula) (resource : Nat) : Nat :=
  let inner := transparentHybridDisjunctionRightPayloadEnvelope
    stepRowsZeroValuation b c resource
  transparentHybridDisjunctionRightPayloadEnvelope stepRowsZeroValuation a
    (b ⋎ c) inner

private theorem threeWayPath0PayloadBound_le
    {a b c : ValuationFormula}
    (certificate : HybridCertificate a) (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := b ⋎ c) certificate) <=
      threeWayPath0PayloadEnvelope a b c resource := by
  exact transparentHybridDisjunctionLeftPayloadBound_le
    (right := b ⋎ c) certificate resource hcertificate

private theorem threeWayPath1PayloadBound_le
    {a b c : ValuationFormula}
    (certificate : HybridCertificate b) (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := a)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := c) certificate)) <=
      threeWayPath1PayloadEnvelope a b c resource := by
  let inner := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := c) certificate
  have hinner := transparentHybridDisjunctionLeftPayloadBound_le
    (right := c) certificate resource hcertificate
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := a) inner _ hinner
  simpa only [threeWayPath1PayloadEnvelope, inner] using houter

private theorem threeWayPath2PayloadBound_le
    {a b c : ValuationFormula}
    (certificate : HybridCertificate c) (resource : Nat)
    (hcertificate : hybridFormulaStructuralPayloadBound certificate <=
      resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := a)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := b) certificate)) <=
      threeWayPath2PayloadEnvelope a b c resource := by
  let inner := CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (left := b) certificate
  have hinner := transparentHybridDisjunctionRightPayloadBound_le
    (left := b) certificate resource hcertificate
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := a) inner _ hinner
  simpa only [threeWayPath2PayloadEnvelope, inner] using houter

noncomputable def compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (data : CompactFormulaTransformStepRowsCheckedBranchData tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount) : Nat := by
  let doneFormula := compactUnifiedParserDoneClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.done
  let emptyFormula := compactUnifiedParserEmptyClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.empty
  let repeatFormula := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.slot1 stepWitness.repeat
  let invalidFormula := compactUnifiedParserSyntaxInvalidClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.invalid
  let quietParserFormula := doneFormula ⋎
    (emptyFormula ⋎ (repeatFormula ⋎ invalidFormula))
  let sameFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.outputBoundary current.outputCount next.outputBoundary
    next.outputCount
  let quietFormula := quietParserFormula ⋏ sameFormula
  let termParserFormula := compactUnifiedParserSyntaxTermClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.term
  let termOutputFormula := compactFormulaTransformTermOutputRowsClosedFormula
    tokenTable width tokenCount current next mode stepWitness.slot0
    stepWitness.term.tag stepWitness.term.argument consumedCount witnessStart
    witnessFinish witnessCount
  let termFormula := termParserFormula ⋏ termOutputFormula
  let formulaParserFormula := compactUnifiedParserSyntaxFormulaClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.formula
  let formulaOutputFormula :=
    compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
      tokenCount current next mode stepWitness.formula.tag consumedCount
      mappedHead
  let formulaFormula := formulaParserFormula ⋏ formulaOutputFormula
  cases data with
  | quietDone hparser hrows =>
      let parserResource := fourWayPath0PayloadEnvelope doneFormula emptyFormula
        repeatFormula invalidFormula
        (compactUnifiedParserDonePublicFinitePayloadEnvelope tokenTable width
          tokenCount current.parser next.parser stepWitness.done)
      let quietResource := transparentHybridConjunctionPayloadEnvelope
        stepRowsZeroValuation quietParserFormula sameFormula parserResource
        (compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope tokenTable width
          tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount)
      exact threeWayPath0PayloadEnvelope quietFormula termFormula formulaFormula
        quietResource
  | quietEmpty hparser hrows =>
      let parserResource := fourWayPath1PayloadEnvelope doneFormula emptyFormula
        repeatFormula invalidFormula
        (compactUnifiedParserEmptyPublicFinitePayloadEnvelope tokenTable width
          tokenCount current.parser next.parser stepWitness.empty)
      let quietResource := transparentHybridConjunctionPayloadEnvelope
        stepRowsZeroValuation quietParserFormula sameFormula parserResource
        (compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope tokenTable width
          tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount)
      exact threeWayPath0PayloadEnvelope quietFormula termFormula formulaFormula
        quietResource
  | quietRepeat hparser hrows =>
      let parserResource := fourWayPath2PayloadEnvelope doneFormula emptyFormula
        repeatFormula invalidFormula
        (compactUnifiedParserSyntaxRepeatPublicFinitePayloadEnvelope tokenTable
          width tokenCount current.parser next.parser stepWitness.slot0
          stepWitness.slot1 stepWitness.repeat)
      let quietResource := transparentHybridConjunctionPayloadEnvelope
        stepRowsZeroValuation quietParserFormula sameFormula parserResource
        (compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope tokenTable width
          tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount)
      exact threeWayPath0PayloadEnvelope quietFormula termFormula formulaFormula
        quietResource
  | quietInvalid hparser hrows =>
      let parserResource := fourWayPath3PayloadEnvelope doneFormula emptyFormula
        repeatFormula invalidFormula
        (compactUnifiedParserSyntaxInvalidPublicFinitePayloadEnvelope tokenTable
          width tokenCount current.parser next.parser stepWitness.invalid)
      let quietResource := transparentHybridConjunctionPayloadEnvelope
        stepRowsZeroValuation quietParserFormula sameFormula parserResource
        (compactAdditiveNatListSameRowsPublicFinitePayloadEnvelope tokenTable width
          tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount)
      exact threeWayPath0PayloadEnvelope quietFormula termFormula formulaFormula
        quietResource
  | term hparser hrows =>
      let termResource := transparentHybridConjunctionPayloadEnvelope
        stepRowsZeroValuation termParserFormula termOutputFormula
        (compactUnifiedParserSyntaxTermPublicFinitePayloadEnvelope tokenTable width
          tokenCount current.parser next.parser stepWitness.slot0
          stepWitness.term)
        (compactFormulaTransformTermOutputRowsPublicFinitePayloadEnvelope tokenTable
          width tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
          stepWitness.term.argument consumedCount witnessStart witnessFinish
          witnessCount)
      exact threeWayPath1PayloadEnvelope quietFormula termFormula formulaFormula
        termResource
  | formula hparser hrows =>
      let formulaResource := transparentHybridConjunctionPayloadEnvelope
        stepRowsZeroValuation formulaParserFormula formulaOutputFormula
        (compactUnifiedParserSyntaxFormulaPublicFinitePayloadEnvelope tokenTable
          width tokenCount current.parser next.parser stepWitness.slot0
          stepWitness.formula)
        (compactFormulaTransformFormulaOutputRowsPublicFinitePayloadEnvelope
          tokenTable width tokenCount current next mode stepWitness.formula.tag
          consumedCount mappedHead)
      exact threeWayPath2PayloadEnvelope quietFormula termFormula formulaFormula
        formulaResource

theorem
    compactFormulaTransformStepRowsQuietDoneBranch_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hparser : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current.parser next.parser stepWitness.done)
    (hrows : CompactFormulaTransformOutputSameRows tokenTable width tokenCount
      current next) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStepRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount
          (.quietDone hparser hrows)) <=
      compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData tokenTable
        width tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount (.quietDone hparser hrows) := by
  let doneFormula := compactUnifiedParserDoneClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.done
  let emptyFormula := compactUnifiedParserEmptyClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.empty
  let repeatFormula := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.slot1 stepWitness.repeat
  let invalidFormula := compactUnifiedParserSyntaxInvalidClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.invalid
  let quietParserFormula := doneFormula ⋎
    (emptyFormula ⋎ (repeatFormula ⋎ invalidFormula))
  let sameFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.outputBoundary current.outputCount next.outputBoundary
    next.outputCount
  let quietFormula := quietParserFormula ⋏ sameFormula
  let termParserFormula := compactUnifiedParserSyntaxTermClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.term
  let termOutputFormula := compactFormulaTransformTermOutputRowsClosedFormula
    tokenTable width tokenCount current next mode stepWitness.slot0
    stepWitness.term.tag stepWitness.term.argument consumedCount witnessStart
    witnessFinish witnessCount
  let termFormula := termParserFormula ⋏ termOutputFormula
  let formulaParserFormula := compactUnifiedParserSyntaxFormulaClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.formula
  let formulaOutputFormula :=
    compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
      tokenCount current next mode stepWitness.formula.tag consumedCount
      mappedHead
  let formulaFormula := formulaParserFormula ⋏ formulaOutputFormula
  let parserCertificate :=
    compactUnifiedParserDoneExplicitHybridCertificateOfGraph tokenTable width
      tokenCount current.parser next.parser stepWitness.done hparser
  let rowsCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  have hparserResource :=
    compactUnifiedParserDoneExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount current.parser next.parser stepWitness.done
      hparser
  have hrowsResource :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount current.outputBoundary current.outputCount
      next.outputBoundary next.outputCount hrows
  let parserPath :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := emptyFormula ⋎ (repeatFormula ⋎ invalidFormula))
      parserCertificate
  have hparserPath := fourWayPath0PayloadBound_le
    (b := emptyFormula) (c := repeatFormula) (d := invalidFormula)
    parserCertificate _ hparserResource
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    parserPath rowsCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le parserPath
    rowsCertificate _ _ hparserPath hrowsResource
  have houter := threeWayPath0PayloadBound_le
    (b := termFormula) (c := formulaFormula) selected _ hselected
  unfold compactFormulaTransformStepRowsExplicitHybridCertificateFromData
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := termFormula ⋎ formulaFormula) selected) <= _
  unfold compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData
  dsimp only [doneFormula, emptyFormula, repeatFormula, invalidFormula,
    quietParserFormula, sameFormula, quietFormula, termParserFormula,
    termOutputFormula, termFormula, formulaParserFormula, formulaOutputFormula,
    formulaFormula, parserCertificate, rowsCertificate, parserPath, selected]
  exact houter

theorem
    compactFormulaTransformStepRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (data : CompactFormulaTransformStepRowsCheckedBranchData tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStepRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount data) <=
      compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData tokenTable
        width tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount data := by
  let doneFormula := compactUnifiedParserDoneClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.done
  let emptyFormula := compactUnifiedParserEmptyClosedFormula tokenTable width
    tokenCount current.parser next.parser stepWitness.empty
  let repeatFormula := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.slot1 stepWitness.repeat
  let invalidFormula := compactUnifiedParserSyntaxInvalidClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.invalid
  let quietParserFormula := doneFormula ⋎
    (emptyFormula ⋎ (repeatFormula ⋎ invalidFormula))
  let sameFormula := compactAdditiveNatListSameRowsClosedFormula tokenTable width
    tokenCount current.outputBoundary current.outputCount next.outputBoundary
    next.outputCount
  let quietFormula := quietParserFormula ⋏ sameFormula
  let termParserFormula := compactUnifiedParserSyntaxTermClosedFormula tokenTable
    width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.term
  let termOutputFormula := compactFormulaTransformTermOutputRowsClosedFormula
    tokenTable width tokenCount current next mode stepWitness.slot0
    stepWitness.term.tag stepWitness.term.argument consumedCount witnessStart
    witnessFinish witnessCount
  let termFormula := termParserFormula ⋏ termOutputFormula
  let formulaParserFormula := compactUnifiedParserSyntaxFormulaClosedFormula
    tokenTable width tokenCount current.parser next.parser stepWitness.slot0
    stepWitness.formula
  let formulaOutputFormula :=
    compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
      tokenCount current next mode stepWitness.formula.tag consumedCount
      mappedHead
  let formulaFormula := formulaParserFormula ⋏ formulaOutputFormula
  cases data with
  | quietDone hparser hrows =>
      exact
        compactFormulaTransformStepRowsQuietDoneBranch_structuralPayloadBound_le_transparent
          tokenTable width tokenCount current next mode stepWitness
          consumedCount mappedHead witnessStart witnessFinish witnessCount
          hparser hrows
  | quietEmpty hparser hrows =>
      let parserCertificate :=
        compactUnifiedParserEmptyExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current.parser next.parser stepWitness.empty hparser
      let rowsCertificate :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hrows
      have hparserResource :=
        compactUnifiedParserEmptyExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current.parser next.parser
          stepWitness.empty hparser
      have hrowsResource :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hrows
      let parserPath :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := doneFormula)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := repeatFormula ⋎ invalidFormula) parserCertificate)
      have hparserPath := fourWayPath1PayloadBound_le
        (a := doneFormula) (c := repeatFormula) (d := invalidFormula)
        parserCertificate _ hparserResource
      let selected :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction parserPath
          rowsCertificate
      have hselected := transparentHybridConjunctionPayloadBound_le parserPath
        rowsCertificate _ _ hparserPath hrowsResource
      have houter := threeWayPath0PayloadBound_le
        (b := termFormula) (c := formulaFormula) selected _ hselected
      unfold compactFormulaTransformStepRowsExplicitHybridCertificateFromData
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := termFormula ⋎ formulaFormula) selected) <= _
      unfold compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData
      dsimp only [doneFormula, emptyFormula, repeatFormula, invalidFormula,
        quietParserFormula, sameFormula, quietFormula, termParserFormula,
        termOutputFormula, termFormula, formulaParserFormula,
        formulaOutputFormula, formulaFormula, parserCertificate,
        rowsCertificate, parserPath, selected]
      exact houter
  | quietRepeat hparser hrows =>
      let parserCertificate :=
        compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parser next.parser
          stepWitness.slot0 stepWitness.slot1 stepWitness.repeat hparser
      let rowsCertificate :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hrows
      have hparserResource :=
        compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current.parser next.parser
          stepWitness.slot0 stepWitness.slot1 stepWitness.repeat hparser
      have hrowsResource :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hrows
      let parserPath :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := doneFormula)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := emptyFormula)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right := invalidFormula) parserCertificate))
      have hparserPath := fourWayPath2PayloadBound_le
        (a := doneFormula) (b := emptyFormula) (d := invalidFormula)
        parserCertificate _ hparserResource
      let selected :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction parserPath
          rowsCertificate
      have hselected := transparentHybridConjunctionPayloadBound_le parserPath
        rowsCertificate _ _ hparserPath hrowsResource
      have houter := threeWayPath0PayloadBound_le
        (b := termFormula) (c := formulaFormula) selected _ hselected
      unfold compactFormulaTransformStepRowsExplicitHybridCertificateFromData
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := termFormula ⋎ formulaFormula) selected) <= _
      unfold compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData
      dsimp only [doneFormula, emptyFormula, repeatFormula, invalidFormula,
        quietParserFormula, sameFormula, quietFormula, termParserFormula,
        termOutputFormula, termFormula, formulaParserFormula,
        formulaOutputFormula, formulaFormula, parserCertificate,
        rowsCertificate, parserPath, selected]
      exact houter
  | quietInvalid hparser hrows =>
      let parserCertificate :=
        compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parser next.parser
          stepWitness.invalid hparser
      let rowsCertificate :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hrows
      have hparserResource :=
        compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current.parser next.parser
          stepWitness.invalid hparser
      have hrowsResource :=
        compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current.outputBoundary current.outputCount
          next.outputBoundary next.outputCount hrows
      let parserPath :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := doneFormula)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := emptyFormula)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := repeatFormula) parserCertificate))
      have hparserPath := fourWayPath3PayloadBound_le
        (a := doneFormula) (b := emptyFormula) (c := repeatFormula)
        parserCertificate _ hparserResource
      let selected :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction parserPath
          rowsCertificate
      have hselected := transparentHybridConjunctionPayloadBound_le parserPath
        rowsCertificate _ _ hparserPath hrowsResource
      have houter := threeWayPath0PayloadBound_le
        (b := termFormula) (c := formulaFormula) selected _ hselected
      unfold compactFormulaTransformStepRowsExplicitHybridCertificateFromData
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := termFormula ⋎ formulaFormula) selected) <= _
      unfold compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData
      dsimp only [doneFormula, emptyFormula, repeatFormula, invalidFormula,
        quietParserFormula, sameFormula, quietFormula, termParserFormula,
        termOutputFormula, termFormula, formulaParserFormula,
        formulaOutputFormula, formulaFormula, parserCertificate,
        rowsCertificate, parserPath, selected]
      exact houter
  | term hparser hrows =>
      let parserCertificate :=
        compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current.parser next.parser stepWitness.slot0
          stepWitness.term hparser
      let rowsCertificate :=
        compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next mode stepWitness.slot0
          stepWitness.term.tag stepWitness.term.argument consumedCount
          witnessStart witnessFinish witnessCount hrows
      have hparserResource :=
        compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current.parser next.parser
          stepWitness.slot0 stepWitness.term hparser
      have hrowsResource :=
        compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current next mode stepWitness.slot0
          stepWitness.term.tag stepWitness.term.argument consumedCount
          witnessStart witnessFinish witnessCount hrows
      let selected :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          parserCertificate rowsCertificate
      have hselected := transparentHybridConjunctionPayloadBound_le
        parserCertificate rowsCertificate _ _ hparserResource hrowsResource
      have houter := threeWayPath1PayloadBound_le
        (a := quietFormula) (c := formulaFormula) selected _ hselected
      unfold compactFormulaTransformStepRowsExplicitHybridCertificateFromData
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := quietFormula)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right := formulaFormula) selected)) <= _
      unfold compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData
      dsimp only [doneFormula, emptyFormula, repeatFormula, invalidFormula,
        quietParserFormula, sameFormula, quietFormula, termParserFormula,
        termOutputFormula, termFormula, formulaParserFormula,
        formulaOutputFormula, formulaFormula, parserCertificate,
        rowsCertificate, selected]
      exact houter
  | formula hparser hrows =>
      let parserCertificate :=
        compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.parser next.parser
          stepWitness.slot0 stepWitness.formula hparser
      let rowsCertificate :=
        compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next mode stepWitness.formula.tag
          consumedCount mappedHead hrows
      have hparserResource :=
        compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current.parser next.parser
          stepWitness.slot0 stepWitness.formula hparser
      have hrowsResource :=
        compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current next mode stepWitness.formula.tag
          consumedCount mappedHead hrows
      let selected :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          parserCertificate rowsCertificate
      have hselected := transparentHybridConjunctionPayloadBound_le
        parserCertificate rowsCertificate _ _ hparserResource hrowsResource
      have houter := threeWayPath2PayloadBound_le
        (a := quietFormula) (b := termFormula) selected _ hselected
      unfold compactFormulaTransformStepRowsExplicitHybridCertificateFromData
      change hybridFormulaStructuralPayloadBound
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := quietFormula)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := termFormula) selected)) <= _
      unfold compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData
      dsimp only [doneFormula, emptyFormula, repeatFormula, invalidFormula,
        quietParserFormula, sameFormula, quietFormula, termParserFormula,
        termOutputFormula, termFormula, formulaParserFormula,
        formulaOutputFormula, formulaFormula, parserCertificate,
        rowsCertificate, selected]
      exact houter

noncomputable def compactFormulaTransformStepRowsGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) : Nat :=
  compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData tokenTable width
    tokenCount current next mode stepWitness consumedCount mappedHead
    witnessStart witnessFinish witnessCount
    (compactFormulaTransformStepRowsCheckedBranchDataOfGraph tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount hgraph)

theorem
    compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next mode stepWitness consumedCount
          mappedHead witnessStart witnessFinish witnessCount hgraph) <=
      compactFormulaTransformStepRowsGraphPayloadEnvelope tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount hgraph := by
  let data := compactFormulaTransformStepRowsCheckedBranchDataOfGraph tokenTable
    width tokenCount current next mode stepWitness consumedCount mappedHead
    witnessStart witnessFinish witnessCount hgraph
  have hbranch :=
    compactFormulaTransformStepRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next mode stepWitness consumedCount
      mappedHead witnessStart witnessFinish witnessCount data
  unfold compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  unfold compactFormulaTransformStepRowsGraphPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
      (compactFormulaTransformStepRowsExplicitHybridCertificateFromData
        tokenTable width tokenCount current next mode stepWitness consumedCount
        mappedHead witnessStart witnessFinish witnessCount data) <=
    compactFormulaTransformStepRowsBranchPayloadEnvelopeFromData tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount data
  exact hbranch

#print axioms
  compactFormulaTransformStepRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_transparent
#print axioms
  compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent

end FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicBounds
