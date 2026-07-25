import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds

/-!
# Complete fixed bound for the open-index term-bounded universal shell

This layer connects the scalarized finite branches and shifted bound equality
to every local constructor emitted by the contextual term-bounded universal
compiler.  The resulting endpoint depends only on the common open-index scale.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 250000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexContextualBranchesFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactSyntaxTransformationCodeBounds

def fixedWidthOpenIndexUniversalFullyFixedPayloadPolynomial
    (scale : Nat) : Nat :=
  let termBound := fixedWidthOpenIndexUniversalShellTermPolynomial scale
  let formulaBound := fixedWidthOpenIndexUniversalShellFormulaPolynomial scale
  let localBound := fixedWidthOpenIndexUniversalShellLocalPayloadPolynomial scale
  fixedWidthOpenIndexContextualBranchesFixedPayloadPolynomial scale +
    compileShiftedBoundEqualityFixedPayloadPolynomial scale +
    2 * paPrimitiveCostEnvelope termBound +
    arbitraryContextRelationTransportLocalEnvelope formulaBound termBound +
    12 * localBound

private theorem formulaCodeBound_weaken_openIndexUniversalShell
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {small large : Nat}
    (hGamma : FormulaCodeBound Gamma small)
    (hbound : small <= large) :
    FormulaCodeBound Gamma large := by
  intro formula hformula
  exact (hGamma formula hformula).trans hbound

theorem fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial_le_fullyFixed
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (htable : tableTerm.freeVariables = ∅)
    (hwidth : widthTerm.freeVariables = ∅)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hvalue : valueTerm.freeVariables = ∅) :
    fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial valuation
        tableTerm widthTerm indexTerm valueTerm <=
      fixedWidthOpenIndexUniversalFullyFixedPayloadPolynomial scale := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let boundTerm := Rew.bShift widthTerm
  let outerFormula := ∀⁰ termBoundedUniversalBody boundTerm body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables valuation
  let shiftedGamma := Gamma.image Rewriting.shift
  let bound := termValue valuation widthTerm
  let originalBound := freedTermBoundFormula boundTerm
  let canonicalBound := finiteBoundFormula bound
  let targetFormula := Rewriting.free body
  let originalContext := insert (∼originalBound) shiftedGamma
  let canonicalImplication := canonicalBound 🡒 targetFormula
  let freeBoundTerm := Rew.free boundTerm
  let canonicalTerm := iteratedSuccessorTerm 0 bound
  let forwardEquality :=
    (“!!canonicalTerm = !!freeBoundTerm” :
      LO.FirstOrder.ArithmeticProposition)
  let backwardEquality :=
    (“!!freeBoundTerm = !!canonicalTerm” :
      LO.FirstOrder.ArithmeticProposition)
  let subjectTerm := (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
  let subjectEquality :=
    (“!!subjectTerm = !!subjectTerm” :
      LO.FirstOrder.ArithmeticProposition)
  let symmetryImplication := forwardEquality 🡒 backwardEquality
  let originalCanonicalImplication := originalBound 🡒 canonicalBound
  let originalTargetImplication := originalBound 🡒 targetFormula
  let universalBody := termBoundedUniversalBody boundTerm body
  let boundEqualityResource :=
    compileShiftedBoundEqualityPayloadPublicPolynomial valuation outerVariables
      widthTerm
  let branchResource :=
    fixedWidthOpenIndexContextualBranchesEqualityExposedPayloadPolynomial
      valuation tableTerm widthTerm indexTerm valueTerm
  let termBound := fixedWidthOpenIndexUniversalShellTermPolynomial scale
  let rawFormulaBound :=
    fixedWidthOpenIndexUniversalShellRawFormulaPolynomial scale
  let sourceFormulaBound :=
    fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial scale
  let formulaBound := fixedWidthOpenIndexUniversalShellFormulaPolynomial scale
  let localBound := fixedWidthOpenIndexUniversalShellLocalPayloadPolynomial scale
  let transportLocal := arbitraryContextRelationTransportLocalEnvelope
    formulaBound termBound
  have houter : outerVariables ⊆ {0} := by
    dsimp only [outerVariables, outerFormula, boundTerm, body]
    exact
      fixedWidthUniversalOuterFormula_freeVariables_subset_singleton_of_openIndex
        tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have houterCard : outerVariables.card <= 1 :=
    (Finset.card_le_card houter).trans (by simp)
  have hGammaCard : Gamma.card <= 1 := by
    have hraw : Gamma.card <= outerVariables.card := by
      dsimp only [Gamma]
      unfold valuationContext
      exact Finset.card_image_le
    exact hraw.trans houterCard
  have hshiftedCard : shiftedGamma.card <= 1 := by
    exact Finset.card_image_le.trans hGammaCard
  have hzero : valuation 0 <= scale := by
    have hraw : valuation 0 <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
        fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hscale
  have hbound : bound <= scale := by
    have hraw : bound <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      dsimp only [bound]
      unfold fixedWidthOpenIndexAtomicCoordinateScale
        fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hscale
  have hwidthCode : (binaryTermCode widthTerm).length <= scale := by
    have hraw : (binaryTermCode widthTerm).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
      omega
    exact hraw.trans hscale
  let contextBase := valuationContextFormulaCodeSumEnvelope 1 scale
    (binaryTermCode (&0 : ValuationTerm)).length
  have hGammaSum : formulaCodeSum Gamma <= contextBase := by
    have hvalues : forall candidate, candidate ∈ outerVariables ->
        valuation candidate <= scale := by
      intro candidate hcandidate
      have hsingle := houter hcandidate
      simp only [Finset.mem_singleton] at hsingle
      subst candidate
      exact hzero
    have hvariables : forall candidate, candidate ∈ outerVariables ->
        (binaryTermCode (&candidate : ValuationTerm)).length <=
          (binaryTermCode (&0 : ValuationTerm)).length := by
      intro candidate hcandidate
      have hsingle := houter hcandidate
      simp only [Finset.mem_singleton] at hsingle
      subst candidate
      exact le_rfl
    dsimp only [Gamma, contextBase]
    exact valuationContext_formulaCodeSum_le_uniform outerVariables valuation 1
      scale (binaryTermCode (&0 : ValuationTerm)).length houterCard hvalues
        hvariables
  have hcontextBaseUniversal : contextBase <=
      fixedWidthOpenIndexUniversalContextCodePolynomial scale := by
    dsimp only [contextBase]
    unfold fixedWidthOpenIndexUniversalContextCodePolynomial
    omega
  have hcontextUniversalRaw :
      fixedWidthOpenIndexUniversalContextCodePolynomial scale <=
        rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
      fixedWidthOpenIndexUniversalClosedFormulaPolynomial
      fixedWidthOpenIndexUniversalFormulaPolynomial
    dsimp only
    omega
  have hrawSource : rawFormulaBound <= sourceFormulaBound := by
    dsimp only [rawFormulaBound, sourceFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial
    omega
  have hcontextBaseSource : contextBase <= sourceFormulaBound := by
    exact hcontextBaseUniversal.trans
      (hcontextUniversalRaw.trans hrawSource)
  have hGammaSource : FormulaCodeBound Gamma sourceFormulaBound := by
    intro formula hformula
    have hmember :=
      FoundationCompactPAValuationTermCompilerPublicBounds.formulaCode_le_formulaCodeSum
        hformula
    exact hmember.trans (hGammaSum.trans hcontextBaseSource)
  have hsourceFormula : sourceFormulaBound <= formulaBound := by
    dsimp only [sourceFormulaBound, formulaBound]
    unfold fixedWidthOpenIndexUniversalShellFormulaPolynomial
    omega
  have hGammaFormula : FormulaCodeBound Gamma formulaBound :=
    formulaCodeBound_weaken_openIndexUniversalShell hGammaSource hsourceFormula
  have hshiftedSum := fixedWidthOpenIndexOuterContextFormulaCodeSum_le_fixed
    valuation tableTerm widthTerm indexTerm valueTerm scale hscale htable hwidth
      hindex hvalue
  have hcontextShiftedSource :
      fixedWidthOpenIndexUniversalContextCodePolynomial scale <=
        sourceFormulaBound := by
    exact hcontextUniversalRaw.trans hrawSource
  have hshiftedSource : FormulaCodeBound shiftedGamma sourceFormulaBound := by
    intro formula hformula
    have hmember :=
      formulaCode_le_contextualHybridUniversalFormulaCodeSum hformula
    exact hmember.trans (hshiftedSum.trans hcontextShiftedSource)
  have hshiftedFormula : FormulaCodeBound shiftedGamma formulaBound :=
    formulaCodeBound_weaken_openIndexUniversalShell hshiftedSource
      hsourceFormula
  have hboundTermShift := binaryTermCode_bShift_length_le_add_symbols widthTerm
  have hwidthSymbols := termSymbolCount_le_binaryTermCode_length widthTerm
  have hboundTermRaw : (binaryTermCode boundTerm).length <=
      3 * (binaryTermCode widthTerm).length := by
    dsimp only [boundTerm]
    omega
  have hboundTerm : (binaryTermCode boundTerm).length <= termBound := by
    dsimp only [boundTerm, termBound]
    unfold fixedWidthOpenIndexUniversalShellTermPolynomial
    omega
  have hfreeBoundRaw := binaryTermCode_free_length_le boundTerm
  have hfreeBound : (binaryTermCode freeBoundTerm).length <= termBound := by
    dsimp only [freeBoundTerm, termBound]
    unfold fixedWidthOpenIndexUniversalShellTermPolynomial
      shiftedBoundFixedTermCodePolynomial
    omega
  have hcanonicalTermRaw :=
    iteratedSuccessorTerm_code_length_le_polynomial 0 bound
  have hcanonicalTermMono := iteratedSuccessorTermCodePolynomial_mono 0 hbound
  have hcanonicalTerm : (binaryTermCode canonicalTerm).length <= termBound := by
    dsimp only [canonicalTerm, termBound]
    unfold fixedWidthOpenIndexUniversalShellTermPolynomial
      shiftedBoundFixedTermCodePolynomial
    omega
  have hsubjectTerm : (binaryTermCode subjectTerm).length <= termBound := by
    dsimp only [subjectTerm, termBound]
    unfold fixedWidthOpenIndexUniversalShellTermPolynomial
    omega
  have hbodyRaw := fixedWidthBitBody_code_le_fixed valuation tableTerm widthTerm
    indexTerm valueTerm scale hscale
  have hbodyFixed : (binaryFormulaCode body).length <=
      fixedWidthOpenIndexUniversalBodyCodePolynomial scale := by
    simpa only [body] using hbodyRaw
  have hbody : (binaryFormulaCode body).length <= rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have htargetFree := binaryFormulaCode_free_length_le body
  have htargetTight : (binaryFormulaCode targetFormula).length <=
      2 * (binaryFormulaCode body).length := by
    simpa only [targetFormula] using htargetFree
  have htarget : (binaryFormulaCode targetFormula).length <= rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
      fixedWidthOpenIndexUniversalClosedFormulaPolynomial
      fixedWidthOpenIndexUniversalFormulaPolynomial
      fixedWidthOpenIndexUniversalSyntaxPolynomial
    dsimp only
    omega
  have horiginalBoundRaw := finiteCaseLessThanFormula_code_length_le
    subjectTerm freeBoundTerm
  have horiginalBoundTight : (binaryFormulaCode originalBound).length <=
      (binaryTermCode subjectTerm).length +
        (binaryTermCode freeBoundTerm).length +
          finiteCaseLessThanFormulaCodeOverhead := by
    simpa only [originalBound, freedTermBoundFormula, subjectTerm,
      freeBoundTerm] using horiginalBoundRaw
  have horiginalBound : (binaryFormulaCode originalBound).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hsyntaxBound : bound <=
      fixedWidthOpenIndexUniversalSyntaxPolynomial scale := by
    unfold fixedWidthOpenIndexUniversalSyntaxPolynomial
    omega
  have hcanonicalBoundRaw := finiteBoundFormula_code_le_boundedUniversal bound
    (fixedWidthOpenIndexUniversalSyntaxPolynomial scale) hsyntaxBound
  have hcanonicalBoundTight : (binaryFormulaCode canonicalBound).length <=
      boundedUniversalClosedFormulaEnvelope
        (fixedWidthOpenIndexUniversalSyntaxPolynomial scale) := by
    simpa only [canonicalBound] using hcanonicalBoundRaw
  have hcanonicalBound : (binaryFormulaCode canonicalBound).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
      fixedWidthOpenIndexUniversalClosedFormulaPolynomial
      fixedWidthOpenIndexUniversalFormulaPolynomial
    dsimp only
    omega
  have hforwardEqualityRaw := equalityFormula_code_length_le_paEnvelope
    canonicalTerm freeBoundTerm termBound hcanonicalTerm hfreeBound
  have hforwardEqualityTight :
      (binaryFormulaCode forwardEquality).length <=
        paFormulaCodeEnvelope termBound := by
    simpa only [forwardEquality] using hforwardEqualityRaw
  dsimp only [termBound] at hforwardEqualityTight
  have hforwardEquality : (binaryFormulaCode forwardEquality).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hbackwardEqualityRaw := equalityFormula_code_length_le_paEnvelope
    freeBoundTerm canonicalTerm termBound hfreeBound hcanonicalTerm
  have hbackwardEqualityTight :
      (binaryFormulaCode backwardEquality).length <=
        paFormulaCodeEnvelope termBound := by
    simpa only [backwardEquality] using hbackwardEqualityRaw
  dsimp only [termBound] at hbackwardEqualityTight
  have hbackwardEquality : (binaryFormulaCode backwardEquality).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hsubjectEqualityRaw := equalityFormula_code_length_le_paEnvelope
    subjectTerm subjectTerm termBound hsubjectTerm hsubjectTerm
  have hsubjectEqualityTight :
      (binaryFormulaCode subjectEquality).length <=
        paFormulaCodeEnvelope termBound := by
    simpa only [subjectEquality] using hsubjectEqualityRaw
  dsimp only [termBound] at hsubjectEqualityTight
  have hsubjectEquality : (binaryFormulaCode subjectEquality).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hcoreSource := fun {formula : LO.FirstOrder.ArithmeticProposition}
      (hformula : (binaryFormulaCode formula).length <= rawFormulaBound) =>
    hformula.trans hrawSource
  have himplication := fun
      (left right : LO.FirstOrder.ArithmeticProposition)
      (hleft : (binaryFormulaCode left).length <= rawFormulaBound)
      (hright : (binaryFormulaCode right).length <= rawFormulaBound) => by
    have hraw := binaryFormulaCode_implication_length_le left right
    have htag : (binaryNatCode 5).length <= 64 := by decide
    have : (binaryFormulaCode (left 🡒 right)).length <= sourceFormulaBound := by
      dsimp only [sourceFormulaBound]
      unfold fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial
      omega
    exact this
  have hcanonicalImplication :
      (binaryFormulaCode canonicalImplication).length <= sourceFormulaBound := by
    dsimp only [canonicalImplication]
    exact himplication canonicalBound targetFormula hcanonicalBound htarget
  have hsymmetryImplication :
      (binaryFormulaCode symmetryImplication).length <= sourceFormulaBound := by
    dsimp only [symmetryImplication]
    exact himplication forwardEquality backwardEquality hforwardEquality
      hbackwardEquality
  have horiginalCanonicalImplication :
      (binaryFormulaCode originalCanonicalImplication).length <=
        sourceFormulaBound := by
    dsimp only [originalCanonicalImplication]
    exact himplication originalBound canonicalBound horiginalBound
      hcanonicalBound
  have horiginalTargetImplication :
      (binaryFormulaCode originalTargetImplication).length <=
        sourceFormulaBound := by
    dsimp only [originalTargetImplication]
    exact himplication originalBound targetFormula horiginalBound htarget
  have hnegated := fun (formula : LO.FirstOrder.ArithmeticProposition)
      (hformula : (binaryFormulaCode formula).length <= sourceFormulaBound) => by
    have hraw := binaryFormulaCode_neg_length_le formula
    have : (binaryFormulaCode (∼formula)).length <= formulaBound := by
      dsimp only [formulaBound]
      unfold fixedWidthOpenIndexUniversalShellFormulaPolynomial
      omega
    exact this
  have hnegatedOriginalBound := hnegated originalBound
    (hcoreSource horiginalBound)
  have hnegatedCanonicalBound := hnegated canonicalBound
    (hcoreSource hcanonicalBound)
  have hnegatedTarget := hnegated targetFormula (hcoreSource htarget)
  have hnegatedBackward := hnegated backwardEquality
    (hcoreSource hbackwardEquality)
  have hnegatedSymmetryImplication := hnegated symmetryImplication
    hsymmetryImplication
  have hnegatedOriginalCanonicalImplication :=
    hnegated originalCanonicalImplication horiginalCanonicalImplication
  have hnegatedCanonicalImplication :=
    hnegated canonicalImplication hcanonicalImplication
  have htermBoundFormulaRaw := finiteCaseLessThanFormula_code_length_le
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) boundTerm
  have htermBoundFormulaTight :
      (binaryFormulaCode (termBoundFormula boundTerm)).length <=
        (binaryTermCode
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length +
          (binaryTermCode boundTerm).length +
            finiteCaseLessThanFormulaCodeOverhead := by
    simpa only [termBoundFormula] using htermBoundFormulaRaw
  have htermBoundFormula :
      (binaryFormulaCode (termBoundFormula boundTerm)).length <=
        rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
    have hzeroTerm :
        (binaryTermCode (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
          termBound := by
      have hzeroCode :
          (binaryTermCode
              (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
            (binaryTermCode (&0 : ValuationTerm)).length := by decide
      dsimp only [termBound]
      unfold fixedWidthOpenIndexUniversalShellTermPolynomial
      omega
    dsimp only
    omega
  have huniversalBodyRaw := binarySemiformulaCode_implication_length_le
    (termBoundFormula boundTerm) body
  have huniversalBodyTight : (binaryFormulaCode universalBody).length <=
      2 * (binaryFormulaCode (termBoundFormula boundTerm)).length +
        (binaryFormulaCode body).length + (binaryNatCode 5).length := by
    simpa only [universalBody, termBoundedUniversalBody] using
      huniversalBodyRaw
  have htagFive : (binaryNatCode 5).length <= 64 := by decide
  have huniversalBody : (binaryFormulaCode universalBody).length <=
      sourceFormulaBound := by
    dsimp only [sourceFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial
    omega
  have huniversalFormulaRaw := binaryFormulaCode_all_length_le universalBody
  have huniversalFormula :
      (binaryFormulaCode
        (∀⁰ universalBody : LO.FirstOrder.ArithmeticProposition)).length <=
          sourceFormulaBound := by
    dsimp only [sourceFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial
    omega
  have hfreeUniversalBodyRaw := binaryFormulaCode_free_length_le universalBody
  have hfreeUniversalBody :
      (binaryFormulaCode (Rewriting.free universalBody)).length <=
        formulaBound := by
    dsimp only [formulaBound]
    unfold fixedWidthOpenIndexUniversalShellFormulaPolynomial
    omega
  have hformulaPositive : sourceFormulaBound <= formulaBound := hsourceFormula
  have horiginalBoundFormula := (hcoreSource horiginalBound).trans
    hformulaPositive
  have hcanonicalBoundFormula := (hcoreSource hcanonicalBound).trans
    hformulaPositive
  have htargetFormula := (hcoreSource htarget).trans hformulaPositive
  have hforwardEqualityFormula := (hcoreSource hforwardEquality).trans
    hformulaPositive
  have hbackwardEqualityFormula := (hcoreSource hbackwardEquality).trans
    hformulaPositive
  have hsubjectEqualityFormula := (hcoreSource hsubjectEquality).trans
    hformulaPositive
  have hcanonicalImplicationFormula := hcanonicalImplication.trans
    hformulaPositive
  have hsymmetryImplicationFormula := hsymmetryImplication.trans
    hformulaPositive
  have horiginalCanonicalImplicationFormula :=
    horiginalCanonicalImplication.trans hformulaPositive
  have horiginalTargetImplicationFormula :=
    horiginalTargetImplication.trans hformulaPositive
  have horiginalContextBound : FormulaCodeBound originalContext formulaBound := by
    dsimp only [originalContext]
    exact hshiftedFormula.insert hnegatedOriginalBound
  have horiginalContextCard : originalContext.card <= 4 := by
    have hstep := Finset.card_insert_le (∼originalBound) shiftedGamma
    dsimp only [originalContext]
    omega
  have hboundEquality : boundEqualityResource <=
      compileShiftedBoundEqualityFixedPayloadPolynomial scale := by
    dsimp only [boundEqualityResource]
    exact compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
      valuation outerVariables widthTerm _ _ scale rfl rfl hwidth houter hzero
        hbound hwidthCode
  have hbranches : branchResource <=
      fixedWidthOpenIndexContextualBranchesFixedPayloadPolynomial scale := by
    dsimp only [branchResource]
    exact fixedWidthContextualBranchesEqualityExposedPayloadPolynomial_le_fixed
      valuation tableTerm widthTerm indexTerm valueTerm scale hscale htable hwidth
        hindex hvalue
  have hcanonicalDischarge :=
    contextualDischargeFullAssemblyCost_le_openIndexUniversalShell shiftedGamma
      canonicalBound targetFormula formulaBound (by omega) hshiftedFormula
      htargetFormula hcanonicalImplicationFormula hnegatedCanonicalBound
  have hcanonicalInsertBound : FormulaCodeBound
      (insert canonicalImplication originalContext) formulaBound :=
    horiginalContextBound.insert hcanonicalImplicationFormula
  have hcanonicalInsertCard :
      (insert canonicalImplication originalContext).card <= 8 := by
    have hstep := Finset.card_insert_le canonicalImplication originalContext
    omega
  have hweakCanonical := weakeningFullAssemblyCost_le_small
    (insert canonicalImplication originalContext) formulaBound
      hcanonicalInsertCard hcanonicalInsertBound
  have horiginalAssumption := assumptionFullPayloadCost_le_small originalContext
    originalBound formulaBound horiginalContextCard horiginalContextBound
      horiginalBoundFormula
  have hsymmetry := equalitySymmetryImplication_payloadLength_le_primitive
    canonicalTerm freeBoundTerm termBound hcanonicalTerm hfreeBound
  have hsymmetryInsertBound : FormulaCodeBound
      (insert symmetryImplication shiftedGamma) formulaBound :=
    hshiftedFormula.insert hsymmetryImplicationFormula
  have hsymmetryInsertCard :
      (insert symmetryImplication shiftedGamma).card <= 8 := by
    have hstep := Finset.card_insert_le symmetryImplication shiftedGamma
    omega
  have hweakSymmetry := weakeningFullAssemblyCost_le_small
    (insert symmetryImplication shiftedGamma) formulaBound hsymmetryInsertCard
      hsymmetryInsertBound
  have hmpSymmetry := contextualModusPonensFullAssemblyCost_le_small shiftedGamma
    forwardEquality backwardEquality formulaBound (by omega) hshiftedFormula
      hforwardEqualityFormula hbackwardEqualityFormula
      hsymmetryImplicationFormula hnegatedSymmetryImplication hnegatedBackward
  have hbackwardInsertBound : FormulaCodeBound
      (insert backwardEquality originalContext) formulaBound :=
    horiginalContextBound.insert hbackwardEqualityFormula
  have hbackwardInsertCard :
      (insert backwardEquality originalContext).card <= 8 := by
    have hstep := Finset.card_insert_le backwardEquality originalContext
    omega
  have hweakBackward := weakeningFullAssemblyCost_le_small
    (insert backwardEquality originalContext) formulaBound hbackwardInsertCard
      hbackwardInsertBound
  have hreflexivity := proveEqualityReflexivityAtTerm_payloadLength_le_primitive
    subjectTerm termBound hsubjectTerm
  have hsubjectInsertBound : FormulaCodeBound
      (insert subjectEquality originalContext) formulaBound :=
    horiginalContextBound.insert hsubjectEqualityFormula
  have hsubjectInsertCard :
      (insert subjectEquality originalContext).card <= 8 := by
    have hstep := Finset.card_insert_le subjectEquality originalContext
    omega
  have hweakSubject := weakeningFullAssemblyCost_le_small
    (insert subjectEquality originalContext) formulaBound hsubjectInsertCard
      hsubjectInsertBound
  let backwardResource :=
    (equalitySymmetryImplication canonicalTerm freeBoundTerm).payloadLength +
      weakeningFullAssemblyCost (insert symmetryImplication shiftedGamma) +
      boundEqualityResource +
      contextualModusPonensFullAssemblyCost shiftedGamma forwardEquality
        backwardEquality
  let backwardUnderOriginalResource := backwardResource +
    weakeningFullAssemblyCost (insert backwardEquality originalContext)
  let subjectResource :=
    (proveEqualityReflexivityAtTerm subjectTerm).payloadLength +
      weakeningFullAssemblyCost (insert subjectEquality originalContext)
  have htransport :=
    relationTransportImplicationStructuralPayloadBound_le_arbitraryContext
      originalContext Language.ORing.Rel.lt subjectTerm freeBoundTerm
      subjectTerm canonicalTerm subjectResource backwardUnderOriginalResource
      formulaBound termBound horiginalContextCard horiginalContextBound
      hsubjectTerm hfreeBound hsubjectTerm hcanonicalTerm
  have hmpOriginalCanonical :=
    contextualModusPonensFullAssemblyCost_le_small originalContext
      originalBound canonicalBound formulaBound horiginalContextCard
      horiginalContextBound horiginalBoundFormula hcanonicalBoundFormula
      horiginalCanonicalImplicationFormula
      hnegatedOriginalCanonicalImplication hnegatedCanonicalBound
  have hmpCanonicalTarget :=
    contextualModusPonensFullAssemblyCost_le_small originalContext
      canonicalBound targetFormula formulaBound horiginalContextCard
      horiginalContextBound hcanonicalBoundFormula htargetFormula
      hcanonicalImplicationFormula hnegatedCanonicalImplication hnegatedTarget
  have horiginalDischarge :=
    contextualDischargeFullAssemblyCost_le_openIndexUniversalShell shiftedGamma
      originalBound targetFormula formulaBound (by omega) hshiftedFormula
      htargetFormula horiginalTargetImplicationFormula hnegatedOriginalBound
  have hshiftSource : 2 * sourceFormulaBound <= formulaBound := by
    dsimp only [formulaBound]
    unfold fixedWidthOpenIndexUniversalShellFormulaPolynomial
    omega
  have huniversalIntroduction :=
    contextualUniversalIntroductionFullAssemblyCost_le_openIndexUniversalShell
      Gamma universalBody sourceFormulaBound formulaBound (by omega)
      hGammaSource (huniversalBody.trans hformulaPositive) hfreeUniversalBody
      huniversalFormula hshiftSource
  have hlocalBound : localBound =
      smallContextAssemblyEnvelope formulaBound := by
    dsimp only [localBound, formulaBound]
    rfl
  simp only [shiftedGamma, canonicalBound, targetFormula] at hcanonicalDischarge
  simp only [canonicalImplication, canonicalBound, targetFormula,
    originalContext, originalBound, shiftedGamma] at hweakCanonical
  simp only [originalContext, originalBound, shiftedGamma] at horiginalAssumption
  simp only [canonicalTerm, freeBoundTerm] at hsymmetry
  simp only [symmetryImplication, forwardEquality, backwardEquality,
    shiftedGamma, canonicalTerm, freeBoundTerm] at hweakSymmetry
  simp only [shiftedGamma, forwardEquality, backwardEquality, canonicalTerm,
    freeBoundTerm] at hmpSymmetry
  simp only [backwardEquality, originalContext, originalBound, shiftedGamma,
    canonicalTerm, freeBoundTerm] at hweakBackward
  simp only [subjectTerm] at hreflexivity
  simp only [subjectEquality, subjectTerm, originalContext, originalBound,
    shiftedGamma] at hweakSubject
  simp only [originalContext, originalBound, shiftedGamma, subjectTerm,
    freeBoundTerm, canonicalTerm, subjectResource, backwardResource,
    backwardUnderOriginalResource, symmetryImplication, forwardEquality,
    backwardEquality, subjectEquality] at htransport
  simp only [originalContext, originalBound, shiftedGamma, canonicalBound] at hmpOriginalCanonical
  simp only [originalContext, originalBound, shiftedGamma, canonicalBound,
    targetFormula] at hmpCanonicalTarget
  simp only [shiftedGamma, originalBound, targetFormula] at horiginalDischarge
  simp only [universalBody] at huniversalIntroduction
  change compileContextualTermBoundedUniversalPayloadEnvelope Gamma bound
      boundTerm body boundEqualityResource branchResource <=
    fixedWidthOpenIndexContextualBranchesFixedPayloadPolynomial scale +
      compileShiftedBoundEqualityFixedPayloadPolynomial scale +
      2 * paPrimitiveCostEnvelope termBound + transportLocal +
      12 * localBound
  rw [hlocalBound]
  unfold compileContextualTermBoundedUniversalPayloadEnvelope
  dsimp only [shiftedGamma, originalBound, canonicalBound, originalContext,
    canonicalImplication, forwardEquality, backwardEquality, subjectEquality,
    symmetryImplication, originalCanonicalImplication,
    originalTargetImplication, universalBody, freeBoundTerm, canonicalTerm,
    subjectTerm, backwardResource, backwardUnderOriginalResource,
    subjectResource, transportLocal]
  omega

#print axioms
  fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial_le_fullyFixed

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellFixedBounds
