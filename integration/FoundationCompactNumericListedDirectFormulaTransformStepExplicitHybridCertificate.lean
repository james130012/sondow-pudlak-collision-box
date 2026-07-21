import integration.FoundationCompactNumericListedDirectFormulaTransformStepFormula
import integration.FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for one formula-transform step

The original thirty-eight-coordinate formula is assembled from the four quiet
parser branches and the checked term/formula output-row branches.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

def compactFormulaTransformStepRowsClosedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFormulaTransformStepRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm current.start,
      shortBinaryNumeralTerm current.finish,
      shortBinaryNumeralTerm current.parserFinish,
      shortBinaryNumeralTerm current.parserTokensFinish,
      shortBinaryNumeralTerm current.parserTasksFinish,
      shortBinaryNumeralTerm current.parserTokensBoundary,
      shortBinaryNumeralTerm current.parserTokensCount,
      shortBinaryNumeralTerm current.parserTasksBoundary,
      shortBinaryNumeralTerm current.parserTasksCount,
      shortBinaryNumeralTerm current.outputBoundary,
      shortBinaryNumeralTerm current.outputCount,
      shortBinaryNumeralTerm next.start,
      shortBinaryNumeralTerm next.finish,
      shortBinaryNumeralTerm next.parserFinish,
      shortBinaryNumeralTerm next.parserTokensFinish,
      shortBinaryNumeralTerm next.parserTasksFinish,
      shortBinaryNumeralTerm next.parserTokensBoundary,
      shortBinaryNumeralTerm next.parserTokensCount,
      shortBinaryNumeralTerm next.parserTasksBoundary,
      shortBinaryNumeralTerm next.parserTasksCount,
      shortBinaryNumeralTerm next.outputBoundary,
      shortBinaryNumeralTerm next.outputCount,
      shortBinaryNumeralTerm mode,
      shortBinaryNumeralTerm stepWitness.slot0,
      shortBinaryNumeralTerm stepWitness.slot1,
      shortBinaryNumeralTerm stepWitness.slot2,
      shortBinaryNumeralTerm stepWitness.slot3,
      shortBinaryNumeralTerm stepWitness.slot4,
      shortBinaryNumeralTerm stepWitness.slot5,
      shortBinaryNumeralTerm stepWitness.slot6,
      shortBinaryNumeralTerm consumedCount,
      shortBinaryNumeralTerm mappedHead,
      shortBinaryNumeralTerm witnessStart,
      shortBinaryNumeralTerm witnessFinish,
      shortBinaryNumeralTerm witnessCount]

def compactFormulaTransformStepRowsExplicitFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    ValuationFormula :=
  ((compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.done ⋎
      (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
          current.parser next.parser stepWitness.empty ⋎
        (compactUnifiedParserSyntaxRepeatClosedFormula tokenTable width tokenCount
            current.parser next.parser stepWitness.slot0 stepWitness.slot1
              stepWitness.repeat ⋎
          compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width tokenCount
            current.parser next.parser stepWitness.invalid))) ⋏
    compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
      current.outputBoundary current.outputCount next.outputBoundary
        next.outputCount) ⋎
  ((compactUnifiedParserSyntaxTermClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.term ⋏
      compactFormulaTransformTermOutputRowsClosedFormula tokenTable width
        tokenCount current next mode stepWitness.slot0 stepWitness.term.tag
        stepWitness.term.argument consumedCount witnessStart witnessFinish
        witnessCount) ⋎
    (compactUnifiedParserSyntaxFormulaClosedFormula tokenTable width tokenCount
        current.parser next.parser stepWitness.slot0 stepWitness.formula ⋏
      compactFormulaTransformFormulaOutputRowsClosedFormula tokenTable width
        tokenCount current next mode stepWitness.formula.tag consumedCount
        mappedHead))

theorem compactFormulaTransformStepRowsClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat) :
    compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount =
      compactFormulaTransformStepRowsExplicitFormula tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount := by
  unfold compactFormulaTransformStepRowsClosedFormula
  unfold compactFormulaTransformStepRowsExplicitFormula
  unfold compactFormulaTransformStepRowsDef
  unfold compactUnifiedParserDoneClosedFormula
  unfold compactUnifiedParserEmptyClosedFormula
  unfold compactUnifiedParserSyntaxRepeatClosedFormula
  unfold compactUnifiedParserSyntaxTermClosedFormula
  unfold compactUnifiedParserSyntaxFormulaClosedFormula
  unfold compactUnifiedParserSyntaxInvalidClosedFormula
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactFormulaTransformTermOutputRowsClosedFormula
  unfold compactFormulaTransformFormulaOutputRowsClosedFormula
  simp [CompactFormulaTransformStateRowCoordinates.parser,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.empty,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.term,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.formula,
    CompactUnifiedParserSyntaxStepWitnessCoordinates.invalid,
    FoundationCompactNumericListedDirectParserDoneFormula.compactUnifiedParserDoneWitnessCoordinatesOf,
    FoundationCompactNumericListedDirectParserEmptyFormula.compactUnifiedParserEmptyWitnessCoordinatesOf,
    FoundationCompactNumericListedDirectParserSyntaxRepeatFormula.compactSyntaxRepeatTaskWitnessCoordinatesOf,
    FoundationCompactNumericListedDirectParserSyntaxTermFormula.compactSyntaxTermTaskWitnessCoordinatesOf,
    FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula.compactSyntaxFormulaTaskWitnessCoordinatesOf,
    FoundationCompactNumericListedDirectParserSyntaxInvalidFormula.compactSyntaxInvalidTaskWitnessCoordinatesOf,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    first
    | rfl
    | (congr 1
       apply arithmeticRewritingApp_congr
       apply Rew.ext
       · intro coordinate
         fin_cases coordinate <;>
           simp [compactFormulaTransformTermOutputRowsOuterTerms,
             Rew.comp_app, Rew.subst_bvar]
       · intro coordinate
         exact Empty.elim coordinate)

private theorem compactFormulaTransformStepRowsCertificate_nonempty
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) :
    Nonempty (HybridCertificate
      (compactFormulaTransformStepRowsExplicitFormula tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount)) := by
  rcases hgraph with hquiet | hterm | hformula
  · rcases hquiet with ⟨hparser, hrows⟩
    let rowsCertificate :=
      compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
        width tokenCount current.outputBoundary current.outputCount
        next.outputBoundary next.outputCount hrows
    rcases hparser with hdone | hempty | hrepeat | hinvalid
    · exact ⟨.disjunctionLeft (.conjunction
        (.disjunctionLeft
          (compactUnifiedParserDoneExplicitHybridCertificateOfGraph tokenTable
            width tokenCount current.parser next.parser stepWitness.done hdone))
        rowsCertificate)⟩
    · exact ⟨.disjunctionLeft (.conjunction
        (.disjunctionRight (.disjunctionLeft
          (compactUnifiedParserEmptyExplicitHybridCertificateOfGraph tokenTable
            width tokenCount current.parser next.parser stepWitness.empty hempty)))
        rowsCertificate)⟩
    · exact ⟨.disjunctionLeft (.conjunction
        (.disjunctionRight (.disjunctionRight (.disjunctionLeft
          (compactUnifiedParserSyntaxRepeatExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.parser next.parser
            stepWitness.slot0 stepWitness.slot1 stepWitness.repeat hrepeat))))
        rowsCertificate)⟩
    · exact ⟨.disjunctionLeft (.conjunction
        (.disjunctionRight (.disjunctionRight (.disjunctionRight
          (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.parser next.parser
            stepWitness.invalid hinvalid))))
        rowsCertificate)⟩
  · rcases hterm with ⟨hparser, hrows⟩
    exact ⟨.disjunctionRight (.disjunctionLeft (.conjunction
      (compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph tokenTable
        width tokenCount current.parser next.parser stepWitness.slot0
        stepWitness.term hparser)
      (compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next mode stepWitness.slot0
        stepWitness.term.tag stepWitness.term.argument consumedCount
        witnessStart witnessFinish witnessCount hrows)))⟩
  · rcases hformula with ⟨hparser, hrows⟩
    exact ⟨.disjunctionRight (.disjunctionRight (.conjunction
      (compactUnifiedParserSyntaxFormulaExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.parser next.parser stepWitness.slot0
        stepWitness.formula hparser)
      (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next mode stepWitness.formula.tag
        consumedCount mappedHead hrows)))⟩

noncomputable def compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) :
    HybridCertificate
      (compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount) :=
  .cast
    (compactFormulaTransformStepRowsClosedFormula_alignment tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount).symm
    (Classical.choice
      (compactFormulaTransformStepRowsCertificate_nonempty tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount hgraph))

noncomputable def compileCompactFormulaTransformStepRowsExplicitHybridContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
          current next mode stepWitness consumedCount mappedHead witnessStart
          witnessFinish witnessCount).freeVariables zeroValuation)
      (compactFormulaTransformStepRowsClosedFormula tokenTable width tokenCount
        current next mode stepWitness consumedCount mappedHead witnessStart
        witnessFinish witnessCount) :=
  (compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph tokenTable
    width tokenCount current next mode stepWitness consumedCount mappedHead
    witnessStart witnessFinish witnessCount hgraph).compile

noncomputable def compactFormulaTransformStepRowsExplicitStructuralResource
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount hgraph)

theorem compileCompactFormulaTransformStepRowsExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode : Nat)
    (stepWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (consumedCount mappedHead witnessStart witnessFinish witnessCount : Nat)
    (hgraph : CompactFormulaTransformStepRows tokenTable width tokenCount
      current next mode stepWitness consumedCount mappedHead witnessStart
      witnessFinish witnessCount) :
    (compileCompactFormulaTransformStepRowsExplicitHybridContext tokenTable width
      tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount hgraph).payloadLength ≤
      compactFormulaTransformStepRowsExplicitStructuralResource tokenTable width
        tokenCount current next mode stepWitness consumedCount mappedHead
        witnessStart witnessFinish witnessCount hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current next mode stepWitness consumedCount mappedHead
      witnessStart witnessFinish witnessCount hgraph)

#print axioms compactFormulaTransformStepRowsClosedFormula_alignment
#print axioms compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph
#print axioms
  compileCompactFormulaTransformStepRowsExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
