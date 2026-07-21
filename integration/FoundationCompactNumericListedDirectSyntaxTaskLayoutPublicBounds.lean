import integration.FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for one syntax-task layout

The three token cells are charged independently, combined transparently, and
installed below the two concrete bounded cursor witnesses.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskLayoutPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev layoutZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskLayoutExplicitHybridCertificate.zeroValuation

def compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelopeOfWitnesses
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (binderStart countStart : Nat) : Nat := by
  let tokenTableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let tokenCountTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm start
  let binderStartTerm := shortBinaryNumeralTerm binderStart
  let countStartTerm := shortBinaryNumeralTerm countStart
  let finishTerm := shortBinaryNumeralTerm finish
  let kindFormula := compactAdditiveTokenCellAtValuationFormula tokenTableTerm
    widthTerm tokenCountTerm startTerm kindTerm binderStartTerm
  let binderFormula := compactAdditiveTokenCellAtValuationFormula
    tokenTableTerm widthTerm tokenCountTerm binderStartTerm binderArityTerm
    countStartTerm
  let repeatFormula := compactAdditiveTokenCellAtValuationFormula
    tokenTableTerm widthTerm tokenCountTerm countStartTerm repeatCountTerm
    finishTerm
  let kindResource :=
    compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
      tokenTableTerm widthTerm tokenCountTerm startTerm kindTerm binderStartTerm
  let binderResource :=
    compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
      tokenTableTerm widthTerm tokenCountTerm binderStartTerm binderArityTerm
      countStartTerm
  let repeatResource :=
    compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
      tokenTableTerm widthTerm tokenCountTerm countStartTerm repeatCountTerm
      finishTerm
  let binderRepeatResource := transparentHybridConjunctionPayloadEnvelope
    layoutZeroValuation binderFormula repeatFormula binderResource
    repeatResource
  let terminalResource := transparentHybridConjunctionPayloadEnvelope
    layoutZeroValuation kindFormula (binderFormula ⋏ repeatFormula)
    kindResource binderRepeatResource
  let values : Fin 2 -> Nat := ![countStart, binderStart]
  exact explicitBoundedWitnessHybridStructuralPayloadEnvelope
    layoutZeroValuation tokenCount
    (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
      tokenCount start finish kindTerm binderArityTerm repeatCountTerm)
    values terminalResource

noncomputable def compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (kind, binderArity, repeatCount)) : Nat :=
  compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelopeOfWitnesses
    tokenTable width tokenCount start finish kind binderArity repeatCount
    kindTerm binderArityTerm repeatCountTerm (Classical.choose hlayout)
    (Classical.choose (Classical.choose_spec hlayout))

theorem
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout_structuralPayloadBound_le_public
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hkindClosed : kindTerm.freeVariables = ∅)
    (hbinderClosed : binderArityTerm.freeVariables = ∅)
    (hrepeatClosed : repeatCountTerm.freeVariables = ∅)
    (hkindValue : ∀ valuation, termValue valuation kindTerm = kind)
    (hbinderArityValue : ∀ valuation,
      termValue valuation binderArityTerm = binderArity)
    (hrepeatCountValue : ∀ valuation,
      termValue valuation repeatCountTerm = repeatCount)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (kind, binderArity, repeatCount)) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start finish kind binderArity repeatCount
          kindTerm binderArityTerm repeatCountTerm hkindValue
          hbinderArityValue hrepeatCountValue hlayout) ≤
      compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope tokenTable
        width tokenCount start finish kind binderArity repeatCount kindTerm
        binderArityTerm repeatCountTerm hlayout := by
  let binderStart := Classical.choose hlayout
  have hbinderData := Classical.choose_spec hlayout
  let countStart := Classical.choose hbinderData
  have hcells := Classical.choose_spec hbinderData
  have hkind := hcells.1
  have hbinder := hcells.2.1
  have hrepeat := hcells.2.2
  have hbinderStartLe : binderStart ≤ tokenCount := by
    have hstart := hkind.1
    have hnext := hkind.2.1
    omega
  have hcountStartLe : countStart ≤ tokenCount := by
    have hstart := hbinder.1
    have hnext := hbinder.2.1
    omega
  let tokenTableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let tokenCountTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm start
  let binderStartTerm := shortBinaryNumeralTerm binderStart
  let countStartTerm := shortBinaryNumeralTerm countStart
  let finishTerm := shortBinaryNumeralTerm finish
  let kindCertificate :
      CheckedHybridValuationBoundedFormulaCertificate layoutZeroValuation
        (compactAdditiveTokenCellAtValuationFormula tokenTableTerm widthTerm
          tokenCountTerm startTerm kindTerm binderStartTerm) :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      tokenTableTerm widthTerm tokenCountTerm startTerm kindTerm
      binderStartTerm (by
        simpa [binderStart, countStart, tokenTableTerm, widthTerm,
          tokenCountTerm, startTerm, binderStartTerm,
          termValue_shortBinaryNumeralTerm, hkindValue _] using hkind)
  let binderCertificate :
      CheckedHybridValuationBoundedFormulaCertificate layoutZeroValuation
        (compactAdditiveTokenCellAtValuationFormula tokenTableTerm widthTerm
          tokenCountTerm binderStartTerm binderArityTerm countStartTerm) :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      tokenTableTerm widthTerm tokenCountTerm binderStartTerm binderArityTerm
      countStartTerm (by
        simpa [binderStart, countStart, tokenTableTerm, widthTerm,
          tokenCountTerm, binderStartTerm, countStartTerm,
          termValue_shortBinaryNumeralTerm, hbinderArityValue _] using hbinder)
  let repeatCertificate :
      CheckedHybridValuationBoundedFormulaCertificate layoutZeroValuation
        (compactAdditiveTokenCellAtValuationFormula tokenTableTerm widthTerm
          tokenCountTerm countStartTerm repeatCountTerm finishTerm) :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      tokenTableTerm widthTerm tokenCountTerm countStartTerm repeatCountTerm
      finishTerm (by
        simpa [binderStart, countStart, tokenTableTerm, widthTerm,
          tokenCountTerm, countStartTerm, finishTerm,
          termValue_shortBinaryNumeralTerm, hrepeatCountValue _] using hrepeat)
  have htokenTable : tokenTableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidth : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty width
  have htokenCount : tokenCountTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hstart : startTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty start
  have hbinderStart : binderStartTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty binderStart
  have hcountStart : countStartTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty countStart
  have hfinish : finishTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty finish
  have hkindResource :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTableTerm widthTerm tokenCountTerm startTerm kindTerm
      binderStartTerm htokenTable hwidth htokenCount hstart hkindClosed
      hbinderStart (by
        simpa [binderStart, countStart, tokenTableTerm, widthTerm,
          tokenCountTerm, startTerm, binderStartTerm,
          termValue_shortBinaryNumeralTerm, hkindValue _] using hkind)
  have hbinderResource :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTableTerm widthTerm tokenCountTerm binderStartTerm binderArityTerm
      countStartTerm htokenTable hwidth htokenCount hbinderStart
      hbinderClosed hcountStart (by
        simpa [binderStart, countStart, tokenTableTerm, widthTerm,
          tokenCountTerm, binderStartTerm, countStartTerm,
          termValue_shortBinaryNumeralTerm, hbinderArityValue _] using hbinder)
  have hrepeatResource :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTableTerm widthTerm tokenCountTerm countStartTerm repeatCountTerm
      finishTerm htokenTable hwidth htokenCount hcountStart hrepeatClosed
      hfinish (by
        simpa [binderStart, countStart, tokenTableTerm, widthTerm,
          tokenCountTerm, countStartTerm, finishTerm,
          termValue_shortBinaryNumeralTerm, hrepeatCountValue _] using hrepeat)
  let binderRepeat :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      binderCertificate repeatCertificate
  have hbinderRepeat := transparentHybridConjunctionPayloadBound_le
    binderCertificate repeatCertificate _ _ hbinderResource hrepeatResource
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      kindCertificate binderRepeat
  have hterminalParts := transparentHybridConjunctionPayloadBound_le
    kindCertificate binderRepeat _ _ hkindResource hbinderRepeat
  let values : Fin 2 -> Nat := ![countStart, binderStart]
  have hvalueTerms :
      (fun coordinate : Fin 2 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm countStart,
          shortBinaryNumeralTerm binderStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminal :
      CheckedHybridValuationBoundedFormulaCertificate layoutZeroValuation
        ((compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable
          width tokenCount start finish kindTerm binderArityTerm
          repeatCountTerm) ⇜
            fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal_substitution_alignment
          tokenTable width tokenCount start finish binderStart countStart
          kindTerm binderArityTerm repeatCountTerm).symm) terminalParts
  have hterminal : hybridFormulaStructuralPayloadBound terminal ≤
      transparentHybridConjunctionPayloadEnvelope layoutZeroValuation
        (compactAdditiveTokenCellAtValuationFormula tokenTableTerm widthTerm
          tokenCountTerm startTerm kindTerm binderStartTerm)
        (compactAdditiveTokenCellAtValuationFormula tokenTableTerm widthTerm
            tokenCountTerm binderStartTerm binderArityTerm countStartTerm ⋏
          compactAdditiveTokenCellAtValuationFormula tokenTableTerm widthTerm
            tokenCountTerm countStartTerm repeatCountTerm finishTerm)
        (compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
          tokenTableTerm widthTerm tokenCountTerm startTerm kindTerm
          binderStartTerm)
        (transparentHybridConjunctionPayloadEnvelope layoutZeroValuation
          (compactAdditiveTokenCellAtValuationFormula tokenTableTerm widthTerm
            tokenCountTerm binderStartTerm binderArityTerm countStartTerm)
          (compactAdditiveTokenCellAtValuationFormula tokenTableTerm widthTerm
            tokenCountTerm countStartTerm repeatCountTerm finishTerm)
          (compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
            tokenTableTerm widthTerm tokenCountTerm binderStartTerm
            binderArityTerm countStartTerm)
          (compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
            tokenTableTerm widthTerm tokenCountTerm countStartTerm
            repeatCountTerm finishTerm)) := by
    simpa only [terminal, hybridFormulaStructuralPayloadBound,
      tokenTableTerm, widthTerm, tokenCountTerm, startTerm, binderStartTerm,
      countStartTerm, finishTerm, kindCertificate, binderCertificate,
      repeatCertificate, binderRepeat, terminalParts] using hterminalParts
  have hinstalled :=
    buildExplicitBoundedWitnessHybridCertificate_structuralPayloadBound_le_transparent
      tokenCount
      (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable width
        tokenCount start finish kindTerm binderArityTerm repeatCountTerm)
      values (by
        intro coordinate
        fin_cases coordinate
        · exact hcountStartLe
        · exact hbinderStartLe)
      terminal _ hterminal
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactSyntaxTaskDirectLayoutAtValuationTermsFormula_alignment
          tokenTable width tokenCount start finish kindTerm binderArityTerm
          repeatCountTerm).symm
        (buildExplicitBoundedWitnessHybridCertificate tokenCount
          (compactSyntaxTaskDirectLayoutAtValuationTermsTerminal tokenTable
            width tokenCount start finish kindTerm binderArityTerm
            repeatCountTerm) values _ terminal)) ≤ _
  unfold compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope
    compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelopeOfWitnesses
  simpa only [hybridFormulaStructuralPayloadBound, binderStart, countStart,
    tokenTableTerm, widthTerm, tokenCountTerm, startTerm, binderStartTerm,
    countStartTerm, finishTerm, kindCertificate, binderCertificate,
    repeatCertificate, binderRepeat, terminalParts, values, terminal] using
    hinstalled

private theorem layoutValue_le_finiteSum
    (bound value : Nat) (resource : Nat -> Nat) (hvalue : value <= bound) :
    resource value <= (Finset.range (bound + 1)).sum resource := by
  exact Finset.single_le_sum
    (fun candidate _ => Nat.zero_le (resource candidate))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hvalue))

def compactSyntaxTaskDirectLayoutAtValuationTermsPublicFinitePayloadEnvelope
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm) : Nat :=
  (Finset.range (tokenCount + 1)).sum fun binderStart =>
    (Finset.range (tokenCount + 1)).sum fun countStart =>
      compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelopeOfWitnesses
        tokenTable width tokenCount start finish kind binderArity repeatCount
        kindTerm binderArityTerm repeatCountTerm binderStart countStart

theorem
    compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (kind, binderArity, repeatCount)) :
    compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope tokenTable
        width tokenCount start finish kind binderArity repeatCount kindTerm
        binderArityTerm repeatCountTerm hlayout <=
      compactSyntaxTaskDirectLayoutAtValuationTermsPublicFinitePayloadEnvelope
        tokenTable width tokenCount start finish kind binderArity repeatCount
        kindTerm binderArityTerm repeatCountTerm := by
  let binderStart := Classical.choose hlayout
  have hbinderData := Classical.choose_spec hlayout
  let countStart := Classical.choose hbinderData
  have hcells := Classical.choose_spec hbinderData
  have hkind := hcells.1
  have hbinder := hcells.2.1
  have hbinderStartLe : binderStart <= tokenCount := by
    have hstart := hkind.1
    have hnext := hkind.2.1
    omega
  have hcountStartLe : countStart <= tokenCount := by
    have hstart := hbinder.1
    have hnext := hbinder.2.1
    omega
  let resource :=
    compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelopeOfWitnesses
      tokenTable width tokenCount start finish kind binderArity repeatCount
      kindTerm binderArityTerm repeatCountTerm
  have hcount := layoutValue_le_finiteSum tokenCount countStart
    (resource binderStart) hcountStartLe
  have hbinderBound := layoutValue_le_finiteSum tokenCount binderStart
    (fun candidate =>
      (Finset.range (tokenCount + 1)).sum (resource candidate))
    hbinderStartLe
  unfold compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope
    compactSyntaxTaskDirectLayoutAtValuationTermsPublicFinitePayloadEnvelope
  dsimp only [binderStart, countStart, resource] at hcount hbinderBound ⊢
  exact hcount.trans hbinderBound

theorem
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount start finish
      kind binderArity repeatCount : Nat)
    (kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hkindClosed : kindTerm.freeVariables = ∅)
    (hbinderClosed : binderArityTerm.freeVariables = ∅)
    (hrepeatClosed : repeatCountTerm.freeVariables = ∅)
    (hkindValue : ∀ valuation, termValue valuation kindTerm = kind)
    (hbinderArityValue : ∀ valuation,
      termValue valuation binderArityTerm = binderArity)
    (hrepeatCountValue : ∀ valuation,
      termValue valuation repeatCountTerm = repeatCount)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (kind, binderArity, repeatCount)) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start finish kind binderArity repeatCount
          kindTerm binderArityTerm repeatCountTerm hkindValue
          hbinderArityValue hrepeatCountValue hlayout) <=
      compactSyntaxTaskDirectLayoutAtValuationTermsPublicFinitePayloadEnvelope
        tokenTable width tokenCount start finish kind binderArity repeatCount
        kindTerm binderArityTerm repeatCountTerm := by
  exact
    (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout_structuralPayloadBound_le_public
      tokenTable width tokenCount start finish kind binderArity repeatCount
      kindTerm binderArityTerm repeatCountTerm hkindClosed hbinderClosed
      hrepeatClosed hkindValue hbinderArityValue hrepeatCountValue
      hlayout).trans
    (compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount start finish kind binderArity repeatCount
      kindTerm binderArityTerm repeatCountTerm hlayout)

theorem
    compactSyntaxTaskDirectLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_public
    (tokenTable width tokenCount start finish kind binderArity repeatCount : Nat)
    (hlayout : CompactSyntaxTaskDirectLayout tokenTable width tokenCount
      start finish (kind, binderArity, repeatCount)) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTaskDirectLayoutExplicitHybridCertificateOfLayout
          tokenTable width tokenCount start finish kind binderArity
          repeatCount hlayout) ≤
      compactSyntaxTaskDirectLayoutAtValuationTermsPayloadEnvelope tokenTable
        width tokenCount start finish kind binderArity repeatCount
        (shortBinaryNumeralTerm kind) (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm repeatCount) hlayout := by
  have hkindValue : ∀ valuation,
      termValue valuation (shortBinaryNumeralTerm kind) = kind := by
    intro valuation
    simp [termValue_shortBinaryNumeralTerm]
  have hbinderValue : ∀ valuation,
      termValue valuation (shortBinaryNumeralTerm binderArity) =
        binderArity := by
    intro valuation
    simp [termValue_shortBinaryNumeralTerm]
  have hrepeatValue : ∀ valuation,
      termValue valuation (shortBinaryNumeralTerm repeatCount) =
        repeatCount := by
    intro valuation
    simp [termValue_shortBinaryNumeralTerm]
  change hybridFormulaStructuralPayloadBound
      (compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout
        tokenTable width tokenCount start finish kind binderArity repeatCount
        (shortBinaryNumeralTerm kind) (shortBinaryNumeralTerm binderArity)
        (shortBinaryNumeralTerm repeatCount) hkindValue hbinderValue
        hrepeatValue hlayout) ≤ _
  exact
    compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout_structuralPayloadBound_le_public
      tokenTable width tokenCount start finish kind binderArity repeatCount
      (shortBinaryNumeralTerm kind) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm repeatCount)
      (shortBinaryNumeralTerm_freeVariables_eq_empty kind)
      (shortBinaryNumeralTerm_freeVariables_eq_empty binderArity)
      (shortBinaryNumeralTerm_freeVariables_eq_empty repeatCount)
      hkindValue hbinderValue hrepeatValue hlayout

#print axioms
  compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout_structuralPayloadBound_le_public
#print axioms
  compactSyntaxTaskDirectLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_public
#print axioms
  compactSyntaxTaskDirectLayoutAtValuationTermsExplicitHybridCertificateOfLayout_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectSyntaxTaskLayoutPublicBounds
