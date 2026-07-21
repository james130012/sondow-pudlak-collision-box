import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicFiniteUniversalBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicFiniteUniversalBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for a binary syntax-formula transition

The five checked children of the explicit binary transition are charged
independently and then reassembled with the original conjunction tree.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsPublicBounds

private abbrev binaryZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate.zeroValuation

private abbrev binaryNativeNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate.nativeNumeralTerm
    value

private theorem binaryNativeNumeralTerm_freeVariables_eq_empty (value : Nat) :
    (binaryNativeNumeralTerm value).freeVariables = ∅ := by
  unfold binaryNativeNumeralTerm
  unfold
    FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate.nativeNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem binaryNativeNumeralTerm_value
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (binaryNativeNumeralTerm value) = value := by
  exact
    FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate.termValue_nativeNumeralTerm
      valuation value

noncomputable def
    compactUnifiedParserSyntaxFormulaBinaryGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokenDropFormula :=
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsClosedFormula
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1
  let taskDropFormula :=
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      tailBoundary tailCount 2
  let taskZeroFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount
      (binaryNativeNumeralTerm 0) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0)
  let taskOneFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount
      (binaryNativeNumeralTerm 1) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0)
  let taskPairResource := transparentHybridConjunctionPayloadEnvelope
    binaryZeroValuation taskZeroFormula taskOneFormula
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 0 1
      binderArity 0 (binaryNativeNumeralTerm 0) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0)
      hgraph.2.2.2.1)
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 1 1
      binderArity 0 (binaryNativeNumeralTerm 1) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0)
      hgraph.2.2.2.2)
  let taskDropTailResource := transparentHybridConjunctionPayloadEnvelope
    binaryZeroValuation taskDropFormula (taskZeroFormula ⋏ taskOneFormula)
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      tailBoundary tailCount 2 hgraph.2.2.1)
    taskPairResource
  let tokenDropTailResource := transparentHybridConjunctionPayloadEnvelope
    binaryZeroValuation tokenDropFormula
    (taskDropFormula ⋏ taskZeroFormula ⋏ taskOneFormula)
    (compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 hgraph.2.1)
    taskDropTailResource
  transparentHybridConjunctionPayloadEnvelope binaryZeroValuation
    runningFormula
    (tokenDropFormula ⋏ taskDropFormula ⋏ taskZeroFormula ⋏ taskOneFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish next.finish)
    tokenDropTailResource

def compactUnifiedParserSyntaxFormulaBinaryPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount next.tasksFinish next.finish
  let tokenDropFormula :=
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsClosedFormula
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1
  let taskDropFormula :=
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      tailBoundary tailCount 2
  let taskZeroFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount
      (binaryNativeNumeralTerm 0) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0)
  let taskOneFormula :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable width
      tokenCount next.tasksBoundary next.tasksCount
      (binaryNativeNumeralTerm 1) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0)
  let taskPairResource := transparentHybridConjunctionPayloadEnvelope
    binaryZeroValuation taskZeroFormula taskOneFormula
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPublicFinitePayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 0 1
      binderArity 0 (binaryNativeNumeralTerm 0) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0))
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPublicFinitePayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 1 1
      binderArity 0 (binaryNativeNumeralTerm 1) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0))
  let taskDropTailResource := transparentHybridConjunctionPayloadEnvelope
    binaryZeroValuation taskDropFormula (taskZeroFormula ⋏ taskOneFormula)
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFinitePayloadEnvelope
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      tailBoundary tailCount 2)
    taskPairResource
  let tokenDropTailResource := transparentHybridConjunctionPayloadEnvelope
    binaryZeroValuation tokenDropFormula
    (taskDropFormula ⋏ taskZeroFormula ⋏ taskOneFormula)
    (compactAdditiveNatListDropFixedNumeralRowsPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1)
    taskDropTailResource
  transparentHybridConjunctionPayloadEnvelope binaryZeroValuation
    runningFormula
    (tokenDropFormula ⋏ taskDropFormula ⋏ taskZeroFormula ⋏ taskOneFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount next.tasksFinish next.finish)
    tokenDropTailResource

theorem
    compactUnifiedParserSyntaxFormulaBinaryGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity) :
    compactUnifiedParserSyntaxFormulaBinaryGraphPayloadEnvelope tokenTable
        width tokenCount current next tailBoundary tailCount binderArity
        hgraph <=
      compactUnifiedParserSyntaxFormulaBinaryPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next tailBoundary tailCount
        binderArity := by
  unfold compactUnifiedParserSyntaxFormulaBinaryGraphPayloadEnvelope
    compactUnifiedParserSyntaxFormulaBinaryPublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      (compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount current.tokensBoundary
        current.tokensCount next.tokensBoundary next.tokensCount 1 hgraph.2.1)
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount next.tasksBoundary next.tasksCount
          tailBoundary tailCount 2 hgraph.2.2.1)
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount next.tasksBoundary next.tasksCount 0 1
            binderArity 0 (binaryNativeNumeralTerm 0)
            (binaryNativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
            (binaryNativeNumeralTerm 0) hgraph.2.2.2.1)
          (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount next.tasksBoundary next.tasksCount 1 1
            binderArity 0 (binaryNativeNumeralTerm 1)
            (binaryNativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
            (binaryNativeNumeralTerm 0) hgraph.2.2.2.2))))

theorem
    compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity hgraph) <=
      compactUnifiedParserSyntaxFormulaBinaryGraphPayloadEnvelope tokenTable
        width tokenCount current next tailBoundary tailCount binderArity
        hgraph := by
  rcases hgraph with ⟨hrunning, htokens, hdrop, htaskZero, htaskOne⟩
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  let tokenDropCertificate :=
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 htokens
  let taskDropCertificate :=
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      tailBoundary tailCount 2 hdrop
  let taskZeroCertificate :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 0 1
      binderArity 0 (binaryNativeNumeralTerm 0) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0)
      (binaryNativeNumeralTerm_value binaryZeroValuation 0)
      (binaryNativeNumeralTerm_value · 1)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (binaryNativeNumeralTerm_value · 0) htaskZero
  let taskOneCertificate :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 1 1
      binderArity 0 (binaryNativeNumeralTerm 1) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0)
      (binaryNativeNumeralTerm_value binaryZeroValuation 1)
      (binaryNativeNumeralTerm_value · 1)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (binaryNativeNumeralTerm_value · 0) htaskOne
  have hrunningResource :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount next.tasksFinish next.finish hrunning
  have htokensResource :=
    FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds.compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount 1 htokens
  have hdropResource :=
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds.compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount next.tasksBoundary next.tasksCount
      tailBoundary tailCount 2 hdrop
  have htaskZeroResource :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 0 1
      binderArity 0 (binaryNativeNumeralTerm 0) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0)
      (binaryNativeNumeralTerm_freeVariables_eq_empty 0)
      (binaryNativeNumeralTerm_freeVariables_eq_empty 1)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (binaryNativeNumeralTerm_freeVariables_eq_empty 0)
      (binaryNativeNumeralTerm_value binaryZeroValuation 0)
      (binaryNativeNumeralTerm_value · 1)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (binaryNativeNumeralTerm_value · 0) htaskZero
  have htaskOneResource :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount next.tasksBoundary next.tasksCount 1 1
      binderArity 0 (binaryNativeNumeralTerm 1) (binaryNativeNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (binaryNativeNumeralTerm 0)
      (binaryNativeNumeralTerm_freeVariables_eq_empty 1)
      (binaryNativeNumeralTerm_freeVariables_eq_empty 1)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (binaryNativeNumeralTerm_freeVariables_eq_empty 0)
      (binaryNativeNumeralTerm_value binaryZeroValuation 1)
      (binaryNativeNumeralTerm_value · 1)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (binaryNativeNumeralTerm_value · 0) htaskOne
  let taskPairCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      taskZeroCertificate taskOneCertificate
  have htaskPair := transparentHybridConjunctionPayloadBound_le
    taskZeroCertificate taskOneCertificate _ _ htaskZeroResource
    htaskOneResource
  let taskDropTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      taskDropCertificate taskPairCertificate
  have htaskDropTail := transparentHybridConjunctionPayloadBound_le
    taskDropCertificate taskPairCertificate _ _ hdropResource htaskPair
  let tokenDropTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      tokenDropCertificate taskDropTailCertificate
  have htokenDropTail := transparentHybridConjunctionPayloadBound_le
    tokenDropCertificate taskDropTailCertificate _ _ htokensResource
    htaskDropTail
  let partsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      runningCertificate tokenDropTailCertificate
  have hparts := transparentHybridConjunctionPayloadBound_le runningCertificate
    tokenDropTailCertificate _ _ hrunningResource htokenDropTail
  unfold
    compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  unfold compactUnifiedParserSyntaxFormulaBinaryGraphPayloadEnvelope
  change hybridFormulaStructuralPayloadBound partsCertificate <= _
  exact hparts

theorem
    compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat)
    (hgraph : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next tailBoundary tailCount
          binderArity hgraph) <=
      compactUnifiedParserSyntaxFormulaBinaryPublicFinitePayloadEnvelope
        tokenTable width tokenCount current next tailBoundary tailCount
        binderArity := by
  exact
    (compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next tailBoundary tailCount
      binderArity hgraph).trans
    (compactUnifiedParserSyntaxFormulaBinaryGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount current next tailBoundary tailCount
      binderArity hgraph)

#print axioms
  compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryPublicBounds
