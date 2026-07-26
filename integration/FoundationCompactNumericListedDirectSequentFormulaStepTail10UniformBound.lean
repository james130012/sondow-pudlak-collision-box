import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16UniformBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16AtValuationFullyFixedBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedLeaves
import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedResources

/-! # Row-independent open-index tail 10--21 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail10UniformBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedLeaves
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepTail16AtValuationFullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepTail16UniformBound
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound
open FoundationCompactNumericListedDirectSequentFormulaStepTail10FullyFixedResources

def compactSequentFormulaStepTail15UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail16UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail14UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail15UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail13UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail14UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail12UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail13UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail11UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail12UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail10UniformCodePolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound +
    compactSequentFormulaStepTail11UniformCodePolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound +
    (binaryNatCode 4).length

def compactSequentFormulaStepTail10UniformSyntaxPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  32 *
    (compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
        numericBound +
      compactSequentFormulaStepTail10UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound + 1)

def compactSequentFormulaStepTail15UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail16UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount valueBound)

def compactSequentFormulaStepTail14UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail15UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail13UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail14UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail12UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail13UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail11UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail12UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

def compactSequentFormulaStepTail10UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount numericBound bitBound
      valueBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (compactSequentFormulaStepTail10UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)
    (compactSequentFormulaStepOpenEntryFullyFixedPayload numericBound bitBound
      tokenCount valueBound)
    (compactSequentFormulaStepTail11UniformPayloadPolynomial tokenTable width
      tokenCount suffixCount valueCount numericBound bitBound valueBound)

noncomputable def compactSequentFormulaStepTail10UniformResultOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound)
    (hrowIndex : rowIndex <= numericBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hsuffixBoundary : Nat.size suffixBoundary <= bitBound)
    (hvalueBoundary : Nat.size valueBoundary <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    CompactSequentFormulaStepAtValuationFixedResult
      (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepTail10Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail10UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail10UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
  let valuation := extendValuation rowIndex zeroValuation
  let leaves := compactSequentFormulaStepOpenEntryFullyFixedLeavesOfData
    tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
    valueCount rowIndex valueBound numericBound bitBound data hrowIndex
    htokenCount hsuffixBoundary hvalueBoundary hvalueBound
  let closedResult := compactSequentFormulaStepTail16UniformResultOfData
    tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
    valueCount rowIndex valueBound data
  let closed : ClosedDirectFormulaBound
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount data.row)
      (compactSequentFormulaStepTail16UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound) := by
    rw [← compactSequentFormulaStepTail16Formula_eq_direct]
    exact closedResult.bound
  have hclosed :
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount data.row).freeVariables = ∅ := by
    rw [← compactSequentFormulaStepTail16Formula_eq_direct]
    exact compactSequentFormulaStepTail16Formula_freeVariables_eq_empty
      tokenTable width tokenCount suffixCount valueCount data.row
  have hcontext : (∅ : Finset ValuationFormula) =
      valuationContext
        (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
          tokenCount suffixCount valueCount data.row).freeVariables
        valuation := by
    rw [hclosed]
    simp [valuationContext]
  let tail16Proof := CertifiedPAContextProof.castContext hcontext closed.proof
  let tail16Bound : ExplicitDirectFormulaBound valuation
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount data.row)
      (compactSequentFormulaStepTail16UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound) :=
    { proof := tail16Proof
      payloadLength_le := by
        dsimp only [tail16Proof]
        rw [CertifiedPAContextProof.castContext_payloadLength]
        exact closed.payloadLength_le }
  let tail16 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount data.row)
      (compactSequentFormulaStepTail16UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound)
      (compactSequentFormulaStepTail16UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound) :=
    { bound := tail16Bound
      codeLength_le := by
        rw [← compactSequentFormulaStepTail16Formula_eq_direct]
        exact closedResult.codeLength_le
      freeVariables_subset := by rw [hclosed]; simp }
  let syntaxResource := compactSequentFormulaStepTail10UniformSyntaxPolynomial
    tokenTable width tokenCount suffixCount valueCount numericBound bitBound
    valueBound
  let entryResource := compactSequentFormulaStepOpenEntryFullyFixedPayload
    numericBound bitBound tokenCount valueBound
  have hvaluation : valuation 0 <= numericBound := by
    simpa only [valuation, extendValuation_zero] using hrowIndex
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepTail10UniformSyntaxPolynomial
    omega
  have hcontextEnvelope :
      FoundationCompactPAValuationTermCompilerPublicBounds.valuationContextFormulaCodeSumEnvelope
          1 numericBound (binaryTermCode (&0 : ValuationTerm)).length <=
        syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepTail10UniformSyntaxPolynomial
      compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
    omega
  have hentryCode {formula : ValuationFormula}
      (proof : ExplicitDirectFormulaBound valuation formula entryResource) :
      (binaryFormulaCode formula).length <= entryResource :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      proof.proof).trans proof.payloadLength_le
  have hindexVariables :
      (&0 : ValuationTerm).freeVariables ⊆ {0} := by simp
  have hsuccessorVariables :
      (compactSequentFormulaStepIndexSuccessorTermAtValuation
        (&0 : ValuationTerm)).freeVariables ⊆ {0} :=
    compactSequentFormulaStepIndexSuccessorTermAtValuation_freeVariables_subset_singleton
  have hsecondSuccessorVariables :
      (compactSequentFormulaStepIndexSecondSuccessorTermAtValuation
        (&0 : ValuationTerm)).freeVariables ⊆ {0} :=
    compactSequentFormulaStepIndexSecondSuccessorTermAtValuation_freeVariables_subset_singleton
  have hopenVariables (boundary index value : ValuationTerm)
      (hboundary : boundary.freeVariables = ∅)
      (hindex : index.freeVariables ⊆ {0})
      (hvalue : value.freeVariables = ∅) :
      (compactFixedWidthEntryAtValuationFormula boundary
        (shortBinaryNumeralTerm tokenCount) index value).freeVariables ⊆
          {0} :=
    compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ hboundary (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hindex hvalue
  have hcode15 : entryResource +
      compactSequentFormulaStepTail16UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount valueBound +
      (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepTail10UniformSyntaxPolynomial
      compactSequentFormulaStepTail10UniformCodePolynomial
      compactSequentFormulaStepTail11UniformCodePolynomial
      compactSequentFormulaStepTail12UniformCodePolynomial
      compactSequentFormulaStepTail13UniformCodePolynomial
      compactSequentFormulaStepTail14UniformCodePolynomial
      compactSequentFormulaStepTail15UniformCodePolynomial
    omega
  let tail15Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaves.valueFinish tail16 (hentryCode leaves.valueFinish)
    (hopenVariables _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hsuccessorVariables (shortBinaryNumeralTerm_freeVariables_eq_empty _))
    hvaluation hpositive hcontextEnvelope hcode15
  let tail15 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail15Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail15UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail15UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail15Formula,
      compactSequentFormulaStepTail15UniformPayloadPolynomial,
      compactSequentFormulaStepTail15UniformCodePolynomial, syntaxResource,
      entryResource] using tail15Raw
  have hcode14 : entryResource +
      compactSequentFormulaStepTail15UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound +
      (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepTail10UniformSyntaxPolynomial
      compactSequentFormulaStepTail10UniformCodePolynomial
      compactSequentFormulaStepTail11UniformCodePolynomial
      compactSequentFormulaStepTail12UniformCodePolynomial
      compactSequentFormulaStepTail13UniformCodePolynomial
      compactSequentFormulaStepTail14UniformCodePolynomial
    omega
  let tail14Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaves.valueStart tail15 (hentryCode leaves.valueStart)
    (hopenVariables _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hindexVariables (shortBinaryNumeralTerm_freeVariables_eq_empty _))
    hvaluation hpositive hcontextEnvelope hcode14
  let tail14 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail14Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail14UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail14UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail14Formula,
      compactSequentFormulaStepTail14UniformPayloadPolynomial,
      compactSequentFormulaStepTail14UniformCodePolynomial, syntaxResource,
      entryResource] using tail14Raw
  have hcode13 : entryResource +
      compactSequentFormulaStepTail14UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound +
      (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepTail10UniformSyntaxPolynomial
      compactSequentFormulaStepTail10UniformCodePolynomial
      compactSequentFormulaStepTail11UniformCodePolynomial
      compactSequentFormulaStepTail12UniformCodePolynomial
      compactSequentFormulaStepTail13UniformCodePolynomial
    omega
  let tail13Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaves.nextFinish tail14 (hentryCode leaves.nextFinish)
    (hopenVariables _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hsecondSuccessorVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty _))
    hvaluation hpositive hcontextEnvelope hcode13
  let tail13 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail13Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail13UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail13UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail13Formula,
      compactSequentFormulaStepTail13UniformPayloadPolynomial,
      compactSequentFormulaStepTail13UniformCodePolynomial, syntaxResource,
      entryResource] using tail13Raw
  have hcode12 : entryResource +
      compactSequentFormulaStepTail13UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound +
      (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepTail10UniformSyntaxPolynomial
      compactSequentFormulaStepTail10UniformCodePolynomial
      compactSequentFormulaStepTail11UniformCodePolynomial
      compactSequentFormulaStepTail12UniformCodePolynomial
    omega
  let tail12Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaves.nextStart tail13 (hentryCode leaves.nextStart)
    (hopenVariables _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hsuccessorVariables (shortBinaryNumeralTerm_freeVariables_eq_empty _))
    hvaluation hpositive hcontextEnvelope hcode12
  let tail12 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail12Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail12UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail12UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail12Formula,
      compactSequentFormulaStepTail12UniformPayloadPolynomial,
      compactSequentFormulaStepTail12UniformCodePolynomial, syntaxResource,
      entryResource] using tail12Raw
  have hcode11 : entryResource +
      compactSequentFormulaStepTail12UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound +
      (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepTail10UniformSyntaxPolynomial
      compactSequentFormulaStepTail10UniformCodePolynomial
      compactSequentFormulaStepTail11UniformCodePolynomial
    omega
  let tail11Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaves.currentFinish tail12 (hentryCode leaves.currentFinish)
    (hopenVariables _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hsuccessorVariables (shortBinaryNumeralTerm_freeVariables_eq_empty _))
    hvaluation hpositive hcontextEnvelope hcode11
  let tail11 : CompactSequentFormulaStepAtValuationFixedResult valuation
      (compactSequentFormulaStepTail11Formula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail11UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail11UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
    simpa only [compactSequentFormulaStepTail11Formula,
      compactSequentFormulaStepTail11UniformPayloadPolynomial,
      compactSequentFormulaStepTail11UniformCodePolynomial, syntaxResource,
      entryResource] using tail11Raw
  have hcode10 : entryResource +
      compactSequentFormulaStepTail11UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound +
      (binaryNatCode 4).length <= syntaxResource := by
    unfold syntaxResource compactSequentFormulaStepTail10UniformSyntaxPolynomial
      compactSequentFormulaStepTail10UniformCodePolynomial
    omega
  let tail10Raw := compactSequentFormulaStepAtValuationFixedConjunctionResult
    leaves.currentStart tail11 (hentryCode leaves.currentStart)
    (hopenVariables _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      hindexVariables (shortBinaryNumeralTerm_freeVariables_eq_empty _))
    hvaluation hpositive hcontextEnvelope hcode10
  simpa only [compactSequentFormulaStepTail10Formula,
    compactSequentFormulaStepTail10UniformPayloadPolynomial,
    compactSequentFormulaStepTail10UniformCodePolynomial, syntaxResource,
    entryResource] using tail10Raw

noncomputable def
    compactSequentFormulaStepDirectTail10AtValuationIndexUniformResultOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound)
    (hrowIndex : rowIndex <= numericBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hsuffixBoundary : Nat.size suffixBoundary <= bitBound)
    (hvalueBoundary : Nat.size valueBoundary <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    CompactSequentFormulaStepAtValuationFixedResult
      (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepDirectTail10AtValuationIndex tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount data.row)
      (compactSequentFormulaStepTail10UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound)
      (compactSequentFormulaStepTail10UniformCodePolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
  simpa only [compactSequentFormulaStepTail10Formula_eq_direct] using
    compactSequentFormulaStepTail10UniformResultOfData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound numericBound bitBound data hrowIndex htokenCount
      hsuffixBoundary hvalueBoundary hvalueBound

#print axioms
  compactSequentFormulaStepDirectTail10AtValuationIndexUniformResultOfData

end FoundationCompactNumericListedDirectSequentFormulaStepTail10UniformBound
