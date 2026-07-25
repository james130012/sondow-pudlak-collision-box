import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatFullSelectedFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-! # Selected Repeat path inside the six-way syntax step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxStepRepeatSelectedBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate

private abbrev stepZeroValuation : Nat -> Nat :=
  compactUnifiedParserSyntaxStepZeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate stepZeroValuation formula

def syntaxStepRepeatSelectedPayloadEnvelope
    (a b c d e f : ValuationFormula) (resource : Nat) : Nat :=
  let inner2 :=
    transparentHybridDisjunctionLeftPayloadEnvelope stepZeroValuation c
      (d ⋎ (e ⋎ f)) resource
  let inner1 :=
    transparentHybridDisjunctionRightPayloadEnvelope stepZeroValuation b
      (c ⋎ (d ⋎ (e ⋎ f))) inner2
  transparentHybridDisjunctionRightPayloadEnvelope stepZeroValuation a
    (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) inner1

theorem repeatSelectedPayloadBound_le
    {a b c d e f : ValuationFormula}
    (selected : HybridCertificate c) (resource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (.disjunctionRight (left := a)
          (.disjunctionRight (left := b)
            (.disjunctionLeft (right := d ⋎ (e ⋎ f)) selected))) <=
      syntaxStepRepeatSelectedPayloadEnvelope a b c d e f resource := by
  let inner2 : HybridCertificate (c ⋎ (d ⋎ (e ⋎ f))) :=
    .disjunctionLeft selected
  have hinner2 :=
    transparentHybridDisjunctionLeftPayloadBound_le
      (right := d ⋎ (e ⋎ f)) selected resource hselected
  let inner1 : HybridCertificate (b ⋎ (c ⋎ (d ⋎ (e ⋎ f)))) :=
    .disjunctionRight inner2
  have hinner1 :=
    transparentHybridDisjunctionRightPayloadBound_le (left := b) inner2 _
      hinner2
  exact
    transparentHybridDisjunctionRightPayloadBound_le (left := a) inner1 _
      hinner1

noncomputable def compactUnifiedParserSyntaxStepCertificateFromRepeatCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (selected : HybridCertificate
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.slot1 witness.repeat)) :
    HybridCertificate
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness) :=
  .disjunctionRight (.disjunctionRight (.disjunctionLeft selected))

theorem
    compactUnifiedParserSyntaxStepCertificateFromRepeatCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (selected : HybridCertificate
      (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
        current next witness.slot0 witness.slot1 witness.repeat))
    (resource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= resource) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxStepCertificateFromRepeatCertificate
          tokenTable width tokenCount current next witness selected) <=
      syntaxStepRepeatSelectedPayloadEnvelope
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
        resource := by
  unfold compactUnifiedParserSyntaxStepCertificateFromRepeatCertificate
  exact repeatSelectedPayloadBound_le selected resource hselected

#print axioms repeatSelectedPayloadBound_le
#print axioms
  compactUnifiedParserSyntaxStepCertificateFromRepeatCertificate_structuralPayloadBound_le

end FoundationCompactNumericListedDirectParserSyntaxStepRepeatSelectedBounds
