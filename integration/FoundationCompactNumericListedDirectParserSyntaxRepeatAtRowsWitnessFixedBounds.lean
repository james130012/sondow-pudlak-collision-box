import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsBodyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsInstalledWitnessCertificate
import integration.FoundationCompactNumericListedDirectBinaryWitnessInstallationCoreBounds

/-! # Fully fixed two-witness installation for exact Repeat task rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsWitnessFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedArity02Bounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryWitnessInstallationCoreBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsTerminalCoreCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsInstalledWitnessCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsBodyFixedBounds

private abbrev atRowsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate.zeroValuation

def repeatAtRowsWitnessPayloadEnvelope
    (terminalResource numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessHybridFullyFixedPayloadEnvelopeArity02 0 numericBound
    (repeatAtRowsFullFormulaCodeEnvelope bitBound) terminalResource

theorem repeatAtRowsInstalledWitness_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount boundaryTable count index kind binderArity
      repeatCount terminalResource numericBound bitBound : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hkindClosed : kindTerm.freeVariables = ∅)
    (hbinderClosed : binderArityTerm.freeVariables = ∅)
    (hrepeatClosed : repeatCountTerm.freeVariables = ∅)
    (hindexValue : termValue atRowsZeroValuation indexTerm = index)
    (hkindValue : forall valuation, termValue valuation kindTerm = kind)
    (hbinderValue :
      forall valuation, termValue valuation binderArityTerm = binderArity)
    (hrepeatValue :
      forall valuation, termValue valuation repeatCountTerm = repeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListAtRows tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount)
    (htokenCountValue : tokenCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexCode :
      (binaryTermCode indexTerm).length <= repeatAtRowsTermCodeEnvelope bitBound)
    (hkindCode :
      (binaryTermCode kindTerm).length <= repeatAtRowsTermCodeEnvelope bitBound)
    (hbinderCode :
      (binaryTermCode binderArityTerm).length <=
        repeatAtRowsTermCodeEnvelope bitBound)
    (hrepeatCode :
      (binaryTermCode repeatCountTerm).length <=
        repeatAtRowsTermCodeEnvelope bitBound)
    (hterminal :
      hybridFormulaStructuralPayloadBound
          (repeatAtRowsTerminalCertificateOfGraph tokenTable width tokenCount
            boundaryTable count index kind binderArity repeatCount indexTerm
            kindTerm binderArityTerm repeatCountTerm hindexValue hkindValue
            hbinderValue hrepeatValue hgraph) <= terminalResource) :
    hybridFormulaStructuralPayloadBound
        (repeatAtRowsInstalledWitnessCertificateOfGraph tokenTable width
          tokenCount boundaryTable count index kind binderArity repeatCount
          indexTerm kindTerm binderArityTerm repeatCountTerm hindexValue
          hkindValue hbinderValue hrepeatValue hgraph) <=
      repeatAtRowsWitnessPayloadEnvelope terminalResource numericBound
        bitBound := by
  let left := Classical.choose hgraph.2
  have hleftData := Classical.choose_spec hgraph.2
  let right := Classical.choose hleftData.2
  have hrightData := Classical.choose_spec hleftData.2
  let values : Fin 2 -> Nat := ![right, left]
  let body :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable width
      tokenCount boundaryTable indexTerm kindTerm binderArityTerm repeatCountTerm
  have hvalues : forall coordinate, values coordinate <= tokenCount := by
    intro coordinate
    fin_cases coordinate
    · exact hrightData.1
    · exact hleftData.1
  let terminal :=
    repeatAtRowsTerminalCertificateOfGraph tokenTable width tokenCount
      boundaryTable count index kind binderArity repeatCount indexTerm kindTerm
      binderArityTerm repeatCountTerm hindexValue hkindValue hbinderValue
      hrepeatValue hgraph
  have hfull :=
    repeatAtRowsFullFormula_code_length_le_fixed tokenTable width tokenCount
      boundaryTable count bitBound indexTerm kindTerm binderArityTerm
      repeatCountTerm htableSize hwidthSize htokenCountSize hboundarySize
      hcountSize hindexCode hkindCode hbinderCode hrepeatCode
  have hbody :
      (binaryFormulaCode body).length <=
        repeatAtRowsFullFormulaCodeEnvelope bitBound := by
    simpa only [body] using
      repeatAtRowsTerminalBody_code_length_le_fixed tokenTable width tokenCount
        boundaryTable count bitBound indexTerm kindTerm binderArityTerm
        repeatCountTerm hfull
  have hbodyClosed : body.freeVariables = ∅ := by
    simpa only [body] using
      repeatAtRowsTerminalBody_freeVariables_eq_empty tokenTable width tokenCount
        boundaryTable count indexTerm kindTerm binderArityTerm repeatCountTerm
        hindexClosed hkindClosed hbinderClosed hrepeatClosed
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables atRowsZeroValuation) <= 0 := by
    rw [hbodyClosed]
    simp [valuationContext, formulaCodeSum]
  have hinstalled :=
    installBinaryWitness_structuralPayloadBound_le_fullyFixed
      atRowsZeroValuation tokenCount numericBound
      (repeatAtRowsFullFormulaCodeEnvelope bitBound) terminalResource body values
      hvalues htokenCountValue hbody hcontext terminal hterminal
  change hybridFormulaStructuralPayloadBound
      (buildExplicitBoundedWitnessHybridCertificate tokenCount body values
        hvalues terminal) <= _
  simpa only [repeatAtRowsWitnessPayloadEnvelope] using hinstalled

#print axioms repeatAtRowsInstalledWitness_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsWitnessFixedBounds
