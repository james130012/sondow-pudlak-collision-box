import integration.FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserDonePublicBounds
import integration.FoundationCompactNumericListedDirectParserEmptyPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for a complete syntax-parser step

The six checked semantic branches are charged independently and then lifted
through the original right-associated disjunction tree.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepPublicBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDonePublicBounds
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds

private abbrev stepZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

private abbrev HybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

private def sixWayDisjunctionPath0PayloadEnvelope
    (valuation : Nat -> Nat) (a b c d e f : ValuationFormula)
    (resource : Nat) : Nat :=
  transparentHybridDisjunctionLeftPayloadEnvelope valuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) resource

private def sixWayDisjunctionPath1PayloadEnvelope
    (valuation : Nat -> Nat) (a b c d e f : ValuationFormula)
    (resource : Nat) : Nat :=
  let inner := transparentHybridDisjunctionLeftPayloadEnvelope valuation b
    (c ⋎ (d ⋎ (e ⋎ f))) resource
  transparentHybridDisjunctionRightPayloadEnvelope valuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) inner

private def sixWayDisjunctionPath2PayloadEnvelope
    (valuation : Nat -> Nat) (a b c d e f : ValuationFormula)
    (resource : Nat) : Nat :=
  let inner2 := transparentHybridDisjunctionLeftPayloadEnvelope valuation c
    (d ⋎ (e ⋎ f)) resource
  let inner1 := transparentHybridDisjunctionRightPayloadEnvelope valuation b
    (c ⋎ (d ⋎ (e ⋎ f))) inner2
  transparentHybridDisjunctionRightPayloadEnvelope valuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) inner1

private def sixWayDisjunctionPath3PayloadEnvelope
    (valuation : Nat -> Nat) (a b c d e f : ValuationFormula)
    (resource : Nat) : Nat :=
  let inner3 := transparentHybridDisjunctionLeftPayloadEnvelope valuation d
    (e ⋎ f) resource
  let inner2 := transparentHybridDisjunctionRightPayloadEnvelope valuation c
    (d ⋎ (e ⋎ f)) inner3
  let inner1 := transparentHybridDisjunctionRightPayloadEnvelope valuation b
    (c ⋎ (d ⋎ (e ⋎ f))) inner2
  transparentHybridDisjunctionRightPayloadEnvelope valuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) inner1

private def sixWayDisjunctionPath4PayloadEnvelope
    (valuation : Nat -> Nat) (a b c d e f : ValuationFormula)
    (resource : Nat) : Nat :=
  let inner4 := transparentHybridDisjunctionLeftPayloadEnvelope valuation e f
    resource
  let inner3 := transparentHybridDisjunctionRightPayloadEnvelope valuation d
    (e ⋎ f) inner4
  let inner2 := transparentHybridDisjunctionRightPayloadEnvelope valuation c
    (d ⋎ (e ⋎ f)) inner3
  let inner1 := transparentHybridDisjunctionRightPayloadEnvelope valuation b
    (c ⋎ (d ⋎ (e ⋎ f))) inner2
  transparentHybridDisjunctionRightPayloadEnvelope valuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) inner1

private def sixWayDisjunctionPath5PayloadEnvelope
    (valuation : Nat -> Nat) (a b c d e f : ValuationFormula)
    (resource : Nat) : Nat :=
  let inner4 := transparentHybridDisjunctionRightPayloadEnvelope valuation e f
    resource
  let inner3 := transparentHybridDisjunctionRightPayloadEnvelope valuation d
    (e ⋎ f) inner4
  let inner2 := transparentHybridDisjunctionRightPayloadEnvelope valuation c
    (d ⋎ (e ⋎ f)) inner3
  let inner1 := transparentHybridDisjunctionRightPayloadEnvelope valuation b
    (c ⋎ (d ⋎ (e ⋎ f))) inner2
  transparentHybridDisjunctionRightPayloadEnvelope valuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) inner1

private theorem sixWayDisjunctionPath0PayloadBound_le
    {valuation : Nat -> Nat} {a b c d e f : ValuationFormula}
    (selected : HybridCertificate valuation a) (resource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) selected) <=
      sixWayDisjunctionPath0PayloadEnvelope valuation a b c d e f resource := by
  exact transparentHybridDisjunctionLeftPayloadBound_le selected resource
    hselected

private theorem sixWayDisjunctionPath1PayloadBound_le
    {valuation : Nat -> Nat} {a b c d e f : ValuationFormula}
    (selected : HybridCertificate valuation b) (resource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := a)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := c ⋎ (d ⋎ (e ⋎ f))) selected)) <=
      sixWayDisjunctionPath1PayloadEnvelope valuation a b c d e f resource := by
  let inner : HybridCertificate valuation (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft selected
  have hinner := transparentHybridDisjunctionLeftPayloadBound_le
    (right := c ⋎ (d ⋎ (e ⋎ f))) selected resource hselected
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := a) inner _ hinner
  exact houter

private theorem sixWayDisjunctionPath2PayloadBound_le
    {valuation : Nat -> Nat} {a b c d e f : ValuationFormula}
    (selected : HybridCertificate valuation c) (resource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := a)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := b)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right := d ⋎ (e ⋎ f)) selected))) <=
      sixWayDisjunctionPath2PayloadEnvelope valuation a b c d e f resource := by
  let inner2 : HybridCertificate valuation (c ⋎ (d ⋎ (e ⋎ f))) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft selected
  have hinner2 := transparentHybridDisjunctionLeftPayloadBound_le
    (right := d ⋎ (e ⋎ f)) selected resource hselected
  let inner1 : HybridCertificate valuation
      (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight inner2
  have hinner1 := transparentHybridDisjunctionRightPayloadBound_le
    (left := b) inner2 _ hinner2
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := a) inner1 _ hinner1
  exact houter

private theorem sixWayDisjunctionPath3PayloadBound_le
    {valuation : Nat -> Nat} {a b c d e f : ValuationFormula}
    (selected : HybridCertificate valuation d) (resource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := a)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := b)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := c)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right := e ⋎ f) selected)))) <=
      sixWayDisjunctionPath3PayloadEnvelope valuation a b c d e f resource := by
  let inner3 : HybridCertificate valuation (d ⋎ (e ⋎ f)) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft selected
  have hinner3 := transparentHybridDisjunctionLeftPayloadBound_le
    (right := e ⋎ f) selected resource hselected
  let inner2 : HybridCertificate valuation (c ⋎ (d ⋎ (e ⋎ f))) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight inner3
  have hinner2 := transparentHybridDisjunctionRightPayloadBound_le
    (left := c) inner3 _ hinner3
  let inner1 : HybridCertificate valuation
      (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight inner2
  have hinner1 := transparentHybridDisjunctionRightPayloadBound_le
    (left := b) inner2 _ hinner2
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := a) inner1 _ hinner1
  exact houter

private theorem sixWayDisjunctionPath4PayloadBound_le
    {valuation : Nat -> Nat} {a b c d e f : ValuationFormula}
    (selected : HybridCertificate valuation e) (resource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := a)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := b)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := c)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := d)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  (right := f) selected))))) <=
      sixWayDisjunctionPath4PayloadEnvelope valuation a b c d e f resource := by
  let inner4 : HybridCertificate valuation (e ⋎ f) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft selected
  have hinner4 := transparentHybridDisjunctionLeftPayloadBound_le
    (right := f) selected resource hselected
  let inner3 : HybridCertificate valuation (d ⋎ (e ⋎ f)) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight inner4
  have hinner3 := transparentHybridDisjunctionRightPayloadBound_le
    (left := d) inner4 _ hinner4
  let inner2 : HybridCertificate valuation (c ⋎ (d ⋎ (e ⋎ f))) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight inner3
  have hinner2 := transparentHybridDisjunctionRightPayloadBound_le
    (left := c) inner3 _ hinner3
  let inner1 : HybridCertificate valuation
      (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight inner2
  have hinner1 := transparentHybridDisjunctionRightPayloadBound_le
    (left := b) inner2 _ hinner2
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := a) inner1 _ hinner1
  exact houter

private theorem sixWayDisjunctionPath5PayloadBound_le
    {valuation : Nat -> Nat} {a b c d e f : ValuationFormula}
    (selected : HybridCertificate valuation f) (resource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := a)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := b)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := c)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := d)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (left := e) selected))))) <=
      sixWayDisjunctionPath5PayloadEnvelope valuation a b c d e f resource := by
  let inner4 : HybridCertificate valuation (e ⋎ f) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight selected
  have hinner4 := transparentHybridDisjunctionRightPayloadBound_le
    (left := e) selected resource hselected
  let inner3 : HybridCertificate valuation (d ⋎ (e ⋎ f)) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight inner4
  have hinner3 := transparentHybridDisjunctionRightPayloadBound_le
    (left := d) inner4 _ hinner4
  let inner2 : HybridCertificate valuation (c ⋎ (d ⋎ (e ⋎ f))) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight inner3
  have hinner2 := transparentHybridDisjunctionRightPayloadBound_le
    (left := c) inner3 _ hinner3
  let inner1 : HybridCertificate valuation
      (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight inner2
  have hinner1 := transparentHybridDisjunctionRightPayloadBound_le
    (left := b) inner2 _ hinner2
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := a) inner1 _ hinner1
  exact houter

noncomputable def compactUnifiedParserSyntaxStepBranchPayloadEnvelopeFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (data : CompactUnifiedParserSyntaxStepCheckedBranchData tokenTable width
      tokenCount current next witness) : Nat := by
  let doneFormula := compactUnifiedParserDoneClosedFormula tokenTable width
    tokenCount current next witness.done
  let emptyFormula := compactUnifiedParserEmptyClosedFormula tokenTable width
    tokenCount current next witness.empty
  let repeatFormula := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable
    width tokenCount current next witness.slot0 witness.slot1 witness.repeat
  let termFormula := compactUnifiedParserSyntaxTermClosedFormula tokenTable
    width tokenCount current next witness.slot0 witness.term
  let formulaFormula := compactUnifiedParserSyntaxFormulaClosedFormula tokenTable
    width tokenCount current next witness.slot0 witness.formula
  let invalidFormula := compactUnifiedParserSyntaxInvalidClosedFormula
    tokenTable width tokenCount current next witness.invalid
  cases data with
  | done hgraph =>
      exact sixWayDisjunctionPath0PayloadEnvelope stepZeroValuation doneFormula
        emptyFormula repeatFormula termFormula formulaFormula invalidFormula
        (compactUnifiedParserDonePublicFinitePayloadEnvelope tokenTable width
          tokenCount current next witness.done)
  | empty hgraph =>
      exact sixWayDisjunctionPath1PayloadEnvelope stepZeroValuation doneFormula
        emptyFormula repeatFormula termFormula formulaFormula invalidFormula
        (compactUnifiedParserEmptyPublicFinitePayloadEnvelope tokenTable width
          tokenCount current next witness.empty)
  | repeatBranch hgraph =>
      exact sixWayDisjunctionPath2PayloadEnvelope stepZeroValuation doneFormula
        emptyFormula repeatFormula termFormula formulaFormula invalidFormula
        (compactUnifiedParserSyntaxRepeatPublicFinitePayloadEnvelope tokenTable
          width tokenCount current next witness.slot0 witness.slot1
          witness.repeat)
  | term hgraph =>
      exact sixWayDisjunctionPath3PayloadEnvelope stepZeroValuation doneFormula
        emptyFormula repeatFormula termFormula formulaFormula invalidFormula
        (compactUnifiedParserSyntaxTermGraphPayloadEnvelope tokenTable width
          tokenCount current next witness.slot0 witness.term hgraph)
  | formula hgraph =>
      exact sixWayDisjunctionPath4PayloadEnvelope stepZeroValuation doneFormula
        emptyFormula repeatFormula termFormula formulaFormula invalidFormula
        (compactUnifiedParserSyntaxFormulaGraphPayloadEnvelope tokenTable width
          tokenCount current next witness.slot0 witness.formula hgraph)
  | invalid hgraph =>
      exact sixWayDisjunctionPath5PayloadEnvelope stepZeroValuation doneFormula
        emptyFormula repeatFormula termFormula formulaFormula invalidFormula
        (compactUnifiedParserSyntaxInvalidPublicFinitePayloadEnvelope tokenTable
          width tokenCount current next witness.invalid)

theorem
    compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (data : CompactUnifiedParserSyntaxStepCheckedBranchData tokenTable width
      tokenCount current next witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData
          tokenTable width tokenCount current next witness data) <=
      compactUnifiedParserSyntaxStepBranchPayloadEnvelopeFromData tokenTable
        width tokenCount current next witness data := by
  let doneFormula := compactUnifiedParserDoneClosedFormula tokenTable width
    tokenCount current next witness.done
  let emptyFormula := compactUnifiedParserEmptyClosedFormula tokenTable width
    tokenCount current next witness.empty
  let repeatFormula := compactUnifiedParserSyntaxRepeatClosedFormula tokenTable
    width tokenCount current next witness.slot0 witness.slot1 witness.repeat
  let termFormula := compactUnifiedParserSyntaxTermClosedFormula tokenTable
    width tokenCount current next witness.slot0 witness.term
  let formulaFormula := compactUnifiedParserSyntaxFormulaClosedFormula tokenTable
    width tokenCount current next witness.slot0 witness.formula
  let invalidFormula := compactUnifiedParserSyntaxInvalidClosedFormula
    tokenTable width tokenCount current next witness.invalid
  cases data with
  | done hgraph =>
      have hselected :=
        compactUnifiedParserDoneExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current next witness.done hgraph
      have hpath := sixWayDisjunctionPath0PayloadBound_le
        (valuation := stepZeroValuation)
        (a := doneFormula) (b := emptyFormula) (c := repeatFormula)
        (d := termFormula) (e := formulaFormula) (f := invalidFormula)
        (compactUnifiedParserDoneExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current next witness.done hgraph) _ hselected
      simpa only [compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData,
        compactUnifiedParserSyntaxStepBranchPayloadEnvelopeFromData,
        compactUnifiedParserSyntaxStepExplicitFormula,
        hybridFormulaStructuralPayloadBound, id_eq, doneFormula,
        emptyFormula, repeatFormula, termFormula, formulaFormula,
        invalidFormula] using hpath
  | empty hgraph =>
      have hselected :=
        compactUnifiedParserEmptyExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current next witness.empty hgraph
      have hpath := sixWayDisjunctionPath1PayloadBound_le
        (valuation := stepZeroValuation)
        (a := doneFormula) (b := emptyFormula) (c := repeatFormula)
        (d := termFormula) (e := formulaFormula) (f := invalidFormula)
        (compactUnifiedParserEmptyExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current next witness.empty hgraph) _ hselected
      simpa only [compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData,
        compactUnifiedParserSyntaxStepBranchPayloadEnvelopeFromData,
        compactUnifiedParserSyntaxStepExplicitFormula,
        hybridFormulaStructuralPayloadBound, id_eq, doneFormula,
        emptyFormula, repeatFormula, termFormula, formulaFormula,
        invalidFormula] using hpath
  | repeatBranch hgraph =>
      have hselected :=
        compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current next witness.slot0 witness.slot1
          witness.repeat hgraph
      have hpath := sixWayDisjunctionPath2PayloadBound_le
        (valuation := stepZeroValuation)
        (a := doneFormula) (b := emptyFormula) (c := repeatFormula)
        (d := termFormula) (e := formulaFormula) (f := invalidFormula)
        (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.slot0 witness.slot1
          witness.repeat hgraph) _ hselected
      simpa only [compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData,
        compactUnifiedParserSyntaxStepBranchPayloadEnvelopeFromData,
        compactUnifiedParserSyntaxStepExplicitFormula,
        hybridFormulaStructuralPayloadBound, id_eq, doneFormula,
        emptyFormula, repeatFormula, termFormula, formulaFormula,
        invalidFormula] using hpath
  | term hgraph =>
      have hselected :=
        compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
          tokenTable width tokenCount current next witness.slot0 witness.term
          hgraph
      have hpath := sixWayDisjunctionPath3PayloadBound_le
        (valuation := stepZeroValuation)
        (a := doneFormula) (b := emptyFormula) (c := repeatFormula)
        (d := termFormula) (e := formulaFormula) (f := invalidFormula)
        (compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph tokenTable
          width tokenCount current next witness.slot0 witness.term hgraph) _
        hselected
      simpa only [compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData,
        compactUnifiedParserSyntaxStepBranchPayloadEnvelopeFromData,
        compactUnifiedParserSyntaxStepExplicitFormula,
        hybridFormulaStructuralPayloadBound, id_eq, doneFormula,
        emptyFormula, repeatFormula, termFormula, formulaFormula,
        invalidFormula] using hpath
  | formula hgraph =>
      have hselected :=
        compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
          tokenTable width tokenCount current next witness.slot0 witness.formula
          hgraph
      have hpath := sixWayDisjunctionPath4PayloadBound_le
        (valuation := stepZeroValuation)
        (a := doneFormula) (b := emptyFormula) (c := repeatFormula)
        (d := termFormula) (e := formulaFormula) (f := invalidFormula)
        (compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.slot0 witness.formula
          hgraph) _ hselected
      simpa only [compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData,
        compactUnifiedParserSyntaxStepBranchPayloadEnvelopeFromData,
        compactUnifiedParserSyntaxStepExplicitFormula,
        hybridFormulaStructuralPayloadBound, id_eq, doneFormula,
        emptyFormula, repeatFormula, termFormula, formulaFormula,
        invalidFormula] using hpath
  | invalid hgraph =>
      have hselected :=
        compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount current next witness.invalid hgraph
      have hpath := sixWayDisjunctionPath5PayloadBound_le
        (valuation := stepZeroValuation)
        (a := doneFormula) (b := emptyFormula) (c := repeatFormula)
        (d := termFormula) (e := formulaFormula) (f := invalidFormula)
        (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.invalid hgraph) _
        hselected
      simpa only [compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData,
        compactUnifiedParserSyntaxStepBranchPayloadEnvelopeFromData,
        compactUnifiedParserSyntaxStepExplicitFormula,
        hybridFormulaStructuralPayloadBound, id_eq, doneFormula,
        emptyFormula, repeatFormula, termFormula, formulaFormula,
        invalidFormula] using hpath

noncomputable def compactUnifiedParserSyntaxStepGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxStepRows tokenTable width tokenCount
      current next witness) : Nat :=
  compactUnifiedParserSyntaxStepBranchPayloadEnvelopeFromData tokenTable width
    tokenCount current next witness
    (compactUnifiedParserSyntaxStepCheckedBranchDataOfGraph tokenTable width
      tokenCount current next witness hgraph)

theorem
    compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxStepRows tokenTable width tokenCount
      current next witness) :
    @hybridFormulaStructuralPayloadBound stepZeroValuation
        (compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount
          current next witness)
        (compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness hgraph) <=
      compactUnifiedParserSyntaxStepGraphPayloadEnvelope tokenTable width
        tokenCount current next witness hgraph := by
  let data := compactUnifiedParserSyntaxStepCheckedBranchDataOfGraph tokenTable
    width tokenCount current next witness hgraph
  have hbranch :=
    compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness data
  unfold compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  unfold compactUnifiedParserSyntaxStepGraphPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
      (compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData
        tokenTable width tokenCount current next witness data) <=
    compactUnifiedParserSyntaxStepBranchPayloadEnvelopeFromData tokenTable width
      tokenCount current next witness data
  exact hbranch

#print axioms
  compactUnifiedParserSyntaxStepExplicitHybridCertificateFromData_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxStepExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectParserSyntaxStepPublicBounds
