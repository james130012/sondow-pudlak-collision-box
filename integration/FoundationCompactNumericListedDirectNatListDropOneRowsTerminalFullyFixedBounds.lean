import integration.FoundationCompactNumericListedDirectNatListDropOneRowsIndexSemanticFixedBounds
import integration.FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
import integration.FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
import integration.FoundationCompactPAHybridFiveConjunctionSingletonGeneralBounds

/-!
# Fully fixed payload for one drop-one natural-list row

The four fixed-width entry leaves use the native index terms
`1 + i`, `1 + i + 1`, `i`, and `i + 1`.  Their bounds come from the drop
graph count equation.  The fifth leaf is the checked atomic-row equality.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropOneRowsTerminalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
open FoundationCompactPAHybridFiveConjunctionSingletonGeneralBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
open FoundationCompactNumericListedDirectAtomicRowEqualityFixedPolynomialBounds
open FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsIndexTermsFixedBounds
open FoundationCompactNumericListedDirectNatListDropOneRowsIndexSemanticFixedBounds
open FoundationCompactNumericListedDirectNatListDropRows

def dropOneRowsEntryFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtTermCoordinate numericBound bitBound
        dropOneIndexTermCodeBound))

def dropOneRowsTerminalContextCodePolynomial (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length

def dropOneRowsTerminalAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let entryResource :=
    dropOneRowsEntryFixedPayloadPolynomial numericBound bitBound
  let rowResource :=
    compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
  dropOneRowsTerminalContextCodePolynomial numericBound +
    32 * (entryResource + rowResource +
      (binaryNatCode 4).length + 1) + 1

def dropOneRowsTerminalFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridFiveConjunctionGeneralPayloadEnvelope
    (dropOneRowsTerminalAssemblySyntaxPolynomial numericBound bitBound)
    (dropOneRowsEntryFixedPayloadPolynomial numericBound bitBound)
    (dropOneRowsEntryFixedPayloadPolynomial numericBound bitBound)
    (dropOneRowsEntryFixedPayloadPolynomial numericBound bitBound)
    (dropOneRowsEntryFixedPayloadPolynomial numericBound bitBound)
    (compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound)

private theorem atomicRowPayloadAndCode_le_dropOneFixed
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight
      numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceLeft : sourceLeft <= numericBound)
    (hsourceRight : sourceRight <= numericBound)
    (htargetLeft : targetLeft <= numericBound)
    (htargetRight : targetRight <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hrow : CompactAdditiveAtomicRowEq tokenTable width tokenCount
      sourceLeft sourceRight targetLeft targetRight) :
    let resource :=
      compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
    compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm sourceLeft)
        (shortBinaryNumeralTerm sourceRight)
        (shortBinaryNumeralTerm targetLeft)
        (shortBinaryNumeralTerm targetRight) <= resource ∧
      (binaryFormulaCode
        (compactAdditiveAtomicRowEqAtValuationFormula
          (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm sourceLeft)
          (shortBinaryNumeralTerm sourceRight)
          (shortBinaryNumeralTerm targetLeft)
          (shortBinaryNumeralTerm targetRight))).length <= resource := by
  let resource :=
    compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
  let certificate :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm sourceLeft)
      (shortBinaryNumeralTerm sourceRight)
      (shortBinaryNumeralTerm targetLeft)
      (shortBinaryNumeralTerm targetRight) (by
        simpa only [termValue_shortBinaryNumeralTerm] using hrow)
  have hresource :
      compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
          (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm sourceLeft)
          (shortBinaryNumeralTerm sourceRight)
          (shortBinaryNumeralTerm targetLeft)
          (shortBinaryNumeralTerm targetRight) <= resource := by
    dsimp only [resource]
    exact compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope_le_fixed
      valuation tokenTable width tokenCount sourceLeft sourceRight targetLeft
      targetRight numericBound bitBound hwidth htokenCount hsourceLeft
      hsourceRight htargetLeft htargetRight htokenTableSize hnumericSize
  have hopen : hybridFormulaStructuralPayloadBound certificate <=
      compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm sourceLeft)
        (shortBinaryNumeralTerm sourceRight)
        (shortBinaryNumeralTerm targetLeft)
        (shortBinaryNumeralTerm targetRight) := by
    dsimp only [certificate]
    exact
      compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_of_closed
        valuation (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm sourceLeft)
        (shortBinaryNumeralTerm sourceRight)
        (shortBinaryNumeralTerm targetLeft)
        (shortBinaryNumeralTerm targetRight)
        (shortBinaryNumeralTerm_freeVariables_eq_empty _)
        (shortBinaryNumeralTerm_freeVariables_eq_empty _)
        (shortBinaryNumeralTerm_freeVariables_eq_empty _)
        (shortBinaryNumeralTerm_freeVariables_eq_empty _) (by
          simpa only [termValue_shortBinaryNumeralTerm] using hrow)
  have hpayload : hybridFormulaStructuralPayloadBound certificate <= resource :=
    hopen.trans hresource
  have hcodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      certificate
  have hcode :
      (binaryFormulaCode
        (compactAdditiveAtomicRowEqAtValuationFormula
          (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm sourceLeft)
          (shortBinaryNumeralTerm sourceRight)
          (shortBinaryNumeralTerm targetLeft)
          (shortBinaryNumeralTerm targetRight))).length <= resource := by
    simpa only [certificate] using hcodeRaw.trans hpayload
  exact ⟨hresource, hcode⟩

private theorem dropOneAtomicRowFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft targetRight :
      Nat) :
    (compactAdditiveAtomicRowEqAtValuationFormula
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm sourceLeft)
      (shortBinaryNumeralTerm sourceRight)
      (shortBinaryNumeralTerm targetLeft)
      (shortBinaryNumeralTerm targetRight)).freeVariables = ∅ := by
  unfold compactAdditiveAtomicRowEqAtValuationFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem
    compactAdditiveNatListDropOneRowsTerminalStructuralPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1)
    (index : Fin targetCount)
    (data : CompactAdditiveNatListDropRowData tokenTable width tokenCount
      sourceBoundary targetBoundary 1 index)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary 1 index data <=
      dropOneRowsTerminalFullyFixedPayloadPolynomial numericBound bitBound := by
  let valuation := dropOneRowsValuation index
  let sourceIndexTerm := dropOneSourceIndexTerm
  let sourceNextTerm := dropOneSourceNextTerm
  let targetIndexTerm := dropOneTargetIndexTerm
  let targetNextTerm := dropOneTargetNextTerm
  let sourceLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary)
    (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
    (shortBinaryNumeralTerm data.sourceLeft)
  let sourceRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm sourceBoundary)
    (shortBinaryNumeralTerm tokenCount) sourceNextTerm
    (shortBinaryNumeralTerm data.sourceRight)
  let targetLeftFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) targetIndexTerm
    (shortBinaryNumeralTerm data.targetLeft)
  let targetRightFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm targetBoundary)
    (shortBinaryNumeralTerm tokenCount) targetNextTerm
    (shortBinaryNumeralTerm data.targetRight)
  let rowFormula := compactAdditiveAtomicRowEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm data.sourceLeft)
    (shortBinaryNumeralTerm data.sourceRight)
    (shortBinaryNumeralTerm data.targetLeft)
    (shortBinaryNumeralTerm data.targetRight)
  let entryResource :=
    dropOneRowsEntryFixedPayloadPolynomial numericBound bitBound
  let rowResource :=
    compactAdditiveAtomicRowEqFixedPayloadPolynomial numericBound bitBound
  let syntaxResource :=
    dropOneRowsTerminalAssemblySyntaxPolynomial numericBound bitBound
  have hindices := dropOneRowsIndexSemanticBounds_of_graph tokenTable width
    tokenCount sourceBoundary sourceCount targetBoundary targetCount
    numericBound bitBound hgraph index hsourceCount hnumericSize
  have hvaluation : valuation 0 <= numericBound := by
    change index.val <= numericBound
    exact hindices.targetIndexValue
  have hwidthSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hsourceLeft : data.sourceLeft <= numericBound :=
    data.sourceLeft_le.trans htokenCount
  have hsourceRight : data.sourceRight <= numericBound :=
    data.sourceRight_le.trans htokenCount
  have htargetLeft : data.targetLeft <= numericBound :=
    data.targetLeft_le.trans htokenCount
  have htargetRight : data.targetRight <= numericBound :=
    data.targetRight_le.trans htokenCount
  have hsourceLeftSize : Nat.size data.sourceLeft <= bitBound :=
    (Nat.size_le_size hsourceLeft).trans hnumericSize
  have hsourceRightSize : Nat.size data.sourceRight <= bitBound :=
    (Nat.size_le_size hsourceRight).trans hnumericSize
  have htargetLeftSize : Nat.size data.targetLeft <= bitBound :=
    (Nat.size_le_size htargetLeft).trans hnumericSize
  have htargetRightSize : Nat.size data.targetRight <= bitBound :=
    (Nat.size_le_size htargetRight).trans hnumericSize
  have hsourceLeftEntry :
      CompactFixedWidthEntry sourceBoundary tokenCount
        (termValue valuation sourceIndexTerm) data.sourceLeft := by
    rw [show sourceIndexTerm = dropOneSourceIndexTerm by rfl,
      termValue_dropOneSourceIndexTerm]
    exact data.sourceLeft_entry
  have hsourceRightEntry :
      CompactFixedWidthEntry sourceBoundary tokenCount
        (termValue valuation sourceNextTerm) data.sourceRight := by
    rw [show sourceNextTerm = dropOneSourceNextTerm by rfl,
      termValue_dropOneSourceNextTerm]
    exact data.sourceRight_entry
  have htargetLeftEntry :
      CompactFixedWidthEntry targetBoundary tokenCount
        (termValue valuation targetIndexTerm) data.targetLeft := by
    rw [show targetIndexTerm = dropOneTargetIndexTerm by rfl,
      termValue_dropOneTargetIndexTerm]
    exact data.targetLeft_entry
  have htargetRightEntry :
      CompactFixedWidthEntry targetBoundary tokenCount
        (termValue valuation targetNextTerm) data.targetRight := by
    rw [show targetNextTerm = dropOneTargetNextTerm by rfl,
      termValue_dropOneTargetNextTerm]
    exact data.targetRight_entry
  have hsourceLeftLeaf :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
      valuation sourceBoundary tokenCount data.sourceLeft sourceIndexTerm
      numericBound bitBound dropOneIndexTermCodeBound htokenCount
      hindices.sourceIndexValue hvaluation hsourceBoundarySize hwidthSize
      hindices.sourceIndexSize hsourceLeftSize
      dropOneSourceIndexTerm_code_length_le
      dropOneSourceIndexTerm_freeVariables_subset hsourceLeftEntry
  have hsourceRightLeaf :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
      valuation sourceBoundary tokenCount data.sourceRight sourceNextTerm
      numericBound bitBound dropOneIndexTermCodeBound htokenCount
      hindices.sourceNextValue hvaluation hsourceBoundarySize hwidthSize
      hindices.sourceNextSize hsourceRightSize
      dropOneSourceNextTerm_code_length_le
      dropOneSourceNextTerm_freeVariables_subset hsourceRightEntry
  have htargetLeftLeaf :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
      valuation targetBoundary tokenCount data.targetLeft targetIndexTerm
      numericBound bitBound dropOneIndexTermCodeBound htokenCount
      hindices.targetIndexValue hvaluation htargetBoundarySize hwidthSize
      hindices.targetIndexSize htargetLeftSize
      dropOneTargetIndexTerm_code_length_le
      dropOneTargetIndexTerm_freeVariables_subset htargetLeftEntry
  have htargetRightLeaf :=
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermPayloadAndCode_le_uniform
      valuation targetBoundary tokenCount data.targetRight targetNextTerm
      numericBound bitBound dropOneIndexTermCodeBound htokenCount
      hindices.targetNextValue hvaluation htargetBoundarySize hwidthSize
      hindices.targetNextSize htargetRightSize
      dropOneTargetNextTerm_code_length_le
      dropOneTargetNextTerm_freeVariables_subset htargetRightEntry
  have hrowLeaf := atomicRowPayloadAndCode_le_dropOneFixed valuation
    tokenTable width tokenCount data.sourceLeft data.sourceRight
    data.targetLeft data.targetRight numericBound bitBound hwidth htokenCount
    hsourceLeft hsourceRight htargetLeft htargetRight htokenTableSize
    hnumericSize data.row_eq
  have hsourceLeftResource :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
            (shortBinaryNumeralTerm data.sourceLeft) <= entryResource := by
    simpa only [entryResource, dropOneRowsEntryFixedPayloadPolynomial,
      sourceIndexTerm] using hsourceLeftLeaf.1
  have hsourceLeftCode :
      (binaryFormulaCode sourceLeftFormula).length <= entryResource := by
    simpa only [sourceLeftFormula, entryResource,
      dropOneRowsEntryFixedPayloadPolynomial, sourceIndexTerm] using
      hsourceLeftLeaf.2
  have hsourceRightResource :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount) sourceNextTerm
            (shortBinaryNumeralTerm data.sourceRight) <= entryResource := by
    simpa only [entryResource, dropOneRowsEntryFixedPayloadPolynomial,
      sourceNextTerm] using hsourceRightLeaf.1
  have hsourceRightCode :
      (binaryFormulaCode sourceRightFormula).length <= entryResource := by
    simpa only [sourceRightFormula, entryResource,
      dropOneRowsEntryFixedPayloadPolynomial, sourceNextTerm] using
      hsourceRightLeaf.2
  have htargetLeftResource :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount) targetIndexTerm
            (shortBinaryNumeralTerm data.targetLeft) <= entryResource := by
    simpa only [entryResource, dropOneRowsEntryFixedPayloadPolynomial,
      targetIndexTerm] using htargetLeftLeaf.1
  have htargetLeftCode :
      (binaryFormulaCode targetLeftFormula).length <= entryResource := by
    simpa only [targetLeftFormula, entryResource,
      dropOneRowsEntryFixedPayloadPolynomial, targetIndexTerm] using
      htargetLeftLeaf.2
  have htargetRightResource :
      compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
          valuation (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount) targetNextTerm
            (shortBinaryNumeralTerm data.targetRight) <= entryResource := by
    simpa only [entryResource, dropOneRowsEntryFixedPayloadPolynomial,
      targetNextTerm] using htargetRightLeaf.1
  have htargetRightCode :
      (binaryFormulaCode targetRightFormula).length <= entryResource := by
    simpa only [targetRightFormula, entryResource,
      dropOneRowsEntryFixedPayloadPolynomial, targetNextTerm] using
      htargetRightLeaf.2
  have hrowResource :
      compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
          (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount)
          (shortBinaryNumeralTerm data.sourceLeft)
          (shortBinaryNumeralTerm data.sourceRight)
          (shortBinaryNumeralTerm data.targetLeft)
          (shortBinaryNumeralTerm data.targetRight) <= rowResource := by
    simpa only [rowResource] using hrowLeaf.1
  have hrowCode :
      (binaryFormulaCode rowFormula).length <= rowResource := by
    simpa only [rowFormula, rowResource] using hrowLeaf.2
  have hsourceLeftVariables : sourceLeftFormula.freeVariables ⊆ {0} := by
    dsimp only [sourceLeftFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      dropOneSourceIndexTerm_freeVariables_subset
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hsourceRightVariables : sourceRightFormula.freeVariables ⊆ {0} := by
    dsimp only [sourceRightFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      dropOneSourceNextTerm_freeVariables_subset
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have htargetLeftVariables : targetLeftFormula.freeVariables ⊆ {0} := by
    dsimp only [targetLeftFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      dropOneTargetIndexTerm_freeVariables_subset
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have htargetRightVariables : targetRightFormula.freeVariables ⊆ {0} := by
    dsimp only [targetRightFormula]
    exact compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      _ _ _ _ (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      dropOneTargetNextTerm_freeVariables_subset
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
  have hrowVariables : rowFormula.freeVariables ⊆ {0} := by
    rw [show rowFormula.freeVariables = ∅ by
      dsimp only [rowFormula]
      exact dropOneAtomicRowFormula_freeVariables_eq_empty _ _ _ _ _ _ _]
    simp
  have htotalVariables :
      (sourceLeftFormula ⋏
        (sourceRightFormula ⋏
          (targetLeftFormula ⋏
            (targetRightFormula ⋏ rowFormula)))).freeVariables ⊆ {0} := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hsourceLeftVariables
      (Finset.union_subset hsourceRightVariables
        (Finset.union_subset htargetLeftVariables
          (Finset.union_subset htargetRightVariables hrowVariables)))
  have htail4CodeRaw :=
    binaryFormulaCode_and_length_le_local targetRightFormula rowFormula
  have htail3CodeRaw :=
    binaryFormulaCode_and_length_le_local targetLeftFormula
      (targetRightFormula ⋏ rowFormula)
  have htail2CodeRaw :=
    binaryFormulaCode_and_length_le_local sourceRightFormula
      (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula))
  have htotalCodeRaw :=
    binaryFormulaCode_and_length_le_local sourceLeftFormula
      (sourceRightFormula ⋏
        (targetLeftFormula ⋏ (targetRightFormula ⋏ rowFormula)))
  have htotalCode :
      (binaryFormulaCode
        (sourceLeftFormula ⋏
          (sourceRightFormula ⋏
            (targetLeftFormula ⋏
              (targetRightFormula ⋏ rowFormula))))).length <=
        syntaxResource := by
    simp only [syntaxResource, dropOneRowsTerminalAssemblySyntaxPolynomial]
    omega
  have hpositive : 1 <= syntaxResource := by
    simp only [syntaxResource, dropOneRowsTerminalAssemblySyntaxPolynomial]
    omega
  have hcontext :
      dropOneRowsTerminalContextCodePolynomial numericBound <=
        syntaxResource := by
    simp only [syntaxResource, dropOneRowsTerminalAssemblySyntaxPolynomial]
    omega
  have hgeneral :=
    transparentHybridFiveConjunctionPayloadEnvelope_le_singletonGeneral
      valuation sourceLeftFormula sourceRightFormula targetLeftFormula
      targetRightFormula rowFormula
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
          (shortBinaryNumeralTerm data.sourceLeft))
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount) sourceNextTerm
          (shortBinaryNumeralTerm data.sourceRight))
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) targetIndexTerm
          (shortBinaryNumeralTerm data.targetLeft))
      (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount) targetNextTerm
          (shortBinaryNumeralTerm data.targetRight))
      (compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm data.sourceLeft)
        (shortBinaryNumeralTerm data.sourceRight)
        (shortBinaryNumeralTerm data.targetLeft)
        (shortBinaryNumeralTerm data.targetRight))
      syntaxResource numericBound hpositive hvaluation htotalVariables
      htotalCode (by
        simpa only [dropOneRowsTerminalContextCodePolynomial] using hcontext)
  have hmono :
      hybridFiveConjunctionGeneralPayloadEnvelope syntaxResource
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm sourceBoundary)
              (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
              (shortBinaryNumeralTerm data.sourceLeft))
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm sourceBoundary)
              (shortBinaryNumeralTerm tokenCount) sourceNextTerm
              (shortBinaryNumeralTerm data.sourceRight))
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount) targetIndexTerm
              (shortBinaryNumeralTerm data.targetLeft))
          (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
            valuation (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount) targetNextTerm
              (shortBinaryNumeralTerm data.targetRight))
          (compactAdditiveAtomicRowEqAtValuationStructuralPayloadEnvelope
            valuation (shortBinaryNumeralTerm tokenTable)
              (shortBinaryNumeralTerm width)
              (shortBinaryNumeralTerm tokenCount)
              (shortBinaryNumeralTerm data.sourceLeft)
              (shortBinaryNumeralTerm data.sourceRight)
              (shortBinaryNumeralTerm data.targetLeft)
              (shortBinaryNumeralTerm data.targetRight)) <=
        dropOneRowsTerminalFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [syntaxResource, entryResource, rowResource]
    unfold dropOneRowsTerminalFullyFixedPayloadPolynomial
      hybridFiveConjunctionGeneralPayloadEnvelope
      hybridConjunctionGeneralPayloadEnvelope
    omega
  unfold
    compactAdditiveNatListDropFixedNumeralRowsTerminalStructuralPayloadEnvelope
  dsimp only [valuation, sourceIndexTerm, sourceNextTerm, targetIndexTerm,
    targetNextTerm, sourceLeftFormula, sourceRightFormula, targetLeftFormula,
    targetRightFormula, rowFormula]
  exact hgeneral.trans hmono

#print axioms atomicRowPayloadAndCode_le_dropOneFixed
#print axioms
  compactAdditiveNatListDropOneRowsTerminalStructuralPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListDropOneRowsTerminalFullyFixedBounds
