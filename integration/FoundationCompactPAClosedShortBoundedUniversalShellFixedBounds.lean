import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds

/-!
# Generic fixed bound for a closed short-numeral universal shell

This module isolates the quantitative shell shared by direct bounded-universal
compilers whose outer context is empty and whose bound is a closed short
binary numeral.  Formula-specific callers only provide fixed bounds for the
body, finite branches, and normalized-bound equality.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactSyntaxTransformationCodeBounds

def closedShortUniversalShellTermPolynomial
    (numericBound bitBound : Nat) : Nat :=
  6 * binaryNumeralTermCodeEnvelope bitBound +
    iteratedSuccessorTermCodePolynomial 0 numericBound +
    (binaryTermCode (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)).length +
    (binaryTermCode (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length + 1

def closedShortUniversalShellRawFormulaPolynomial
    (numericBound bitBound syntaxCode bodyCode : Nat) : Nat :=
  let termCode := closedShortUniversalShellTermPolynomial numericBound bitBound
  boundedUniversalClosedFormulaEnvelope syntaxCode +
    paFormulaCodeEnvelope termCode +
    (2 * termCode + finiteCaseLessThanFormulaCodeOverhead) +
    2 * bodyCode + 1

def closedShortUniversalShellSourceFormulaPolynomial
    (numericBound bitBound syntaxCode bodyCode : Nat) : Nat :=
  16 * closedShortUniversalShellRawFormulaPolynomial numericBound bitBound
    syntaxCode bodyCode + 128

def closedShortUniversalShellFormulaPolynomial
    (numericBound bitBound syntaxCode bodyCode : Nat) : Nat :=
  64 * closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
    syntaxCode bodyCode + 64

def closedShortUniversalShellLocalPayloadPolynomial
    (numericBound bitBound syntaxCode bodyCode : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (closedShortUniversalShellFormulaPolynomial numericBound bitBound
      syntaxCode bodyCode)

def closedShortUniversalShellFixedPayloadPolynomial
    (numericBound bitBound syntaxCode bodyCode branchBound
      boundEqualityBound : Nat) : Nat :=
  let termCode := closedShortUniversalShellTermPolynomial numericBound bitBound
  let formulaCode := closedShortUniversalShellFormulaPolynomial numericBound
    bitBound syntaxCode bodyCode
  let localBound := closedShortUniversalShellLocalPayloadPolynomial numericBound
    bitBound syntaxCode bodyCode
  branchBound + boundEqualityBound +
    2 * paPrimitiveCostEnvelope termCode +
    arbitraryContextRelationTransportLocalEnvelope formulaCode termCode +
    12 * localBound

theorem closedShortTermBoundedUniversalFormula_code_length_le_source
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bound numericBound bitBound syntaxCode bodyCode : Nat)
    (hboundSize : Nat.size bound <= bitBound)
    (hbody : (binaryFormulaCode body).length <= bodyCode) :
    (binaryFormulaCode
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm bound)) body :
          LO.FirstOrder.ArithmeticProposition)).length <=
      closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
        syntaxCode bodyCode := by
  let boundTerm := Rew.bShift (shortBinaryNumeralTerm bound)
  let universalBody := termBoundedUniversalBody boundTerm body
  let termBound := closedShortUniversalShellTermPolynomial numericBound bitBound
  let rawFormulaBound := closedShortUniversalShellRawFormulaPolynomial
    numericBound bitBound syntaxCode bodyCode
  let sourceFormulaBound := closedShortUniversalShellSourceFormulaPolynomial
    numericBound bitBound syntaxCode bodyCode
  have hshortCode :
      (binaryTermCode (shortBinaryNumeralTerm bound)).length <=
        binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope bound bitBound hboundSize
  have hboundTermShift := binaryTermCode_bShift_length_le_add_symbols
    (shortBinaryNumeralTerm bound)
  have hshortSymbols := termSymbolCount_le_binaryTermCode_length
    (shortBinaryNumeralTerm bound)
  have hboundTermRaw : (binaryTermCode boundTerm).length <=
      3 * (binaryTermCode (shortBinaryNumeralTerm bound)).length := by
    dsimp only [boundTerm]
    omega
  have hboundTerm : (binaryTermCode boundTerm).length <= termBound := by
    dsimp only [termBound]
    unfold closedShortUniversalShellTermPolynomial
    omega
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
    unfold closedShortUniversalShellRawFormulaPolynomial
    have hzeroTerm :
        (binaryTermCode
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
            termBound := by
      dsimp only [termBound]
      unfold closedShortUniversalShellTermPolynomial
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
  have hbodyRaw : (binaryFormulaCode body).length <= rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold closedShortUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have huniversalBodyIntermediate :
      (binaryFormulaCode universalBody).length <=
        4 * rawFormulaBound + 64 := by
    omega
  have huniversalBody : (binaryFormulaCode universalBody).length <=
      sourceFormulaBound := by
    exact huniversalBodyIntermediate.trans (by
      dsimp only [sourceFormulaBound]
      unfold closedShortUniversalShellSourceFormulaPolynomial
      omega)
  have huniversalFormulaRaw := binaryFormulaCode_all_length_le universalBody
  have huniversalFormulaIntermediate :
      (binaryFormulaCode
        (∀⁰ universalBody : LO.FirstOrder.ArithmeticProposition)).length <=
          4 * rawFormulaBound + 72 := by
    omega
  exact huniversalFormulaIntermediate.trans (by
    unfold closedShortUniversalShellSourceFormulaPolynomial
    omega)

theorem
    compileContextualTermBoundedUniversalPayloadEnvelope_short_le_fixed_of_context
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (bound numericBound bitBound syntaxCode bodyCode : Nat)
    (boundEqualityResource branchResource boundEqualityBound branchBound : Nat)
    (hbound : bound <= numericBound)
    (hboundSize : Nat.size bound <= bitBound)
    (hsyntaxBound : bound <= syntaxCode)
    (hbody : (binaryFormulaCode body).length <= bodyCode)
    (hboundEquality : boundEqualityResource <= boundEqualityBound)
    (hbranches : branchResource <= branchBound)
    (hGammaCard : Gamma.card <= 1)
    (hGammaSource : FormulaCodeBound Gamma
      (closedShortUniversalShellSourceFormulaPolynomial numericBound bitBound
        syntaxCode bodyCode))
    (hshiftedFormula : FormulaCodeBound (Gamma.image Rewriting.shift)
      (closedShortUniversalShellFormulaPolynomial numericBound bitBound
        syntaxCode bodyCode)) :
    compileContextualTermBoundedUniversalPayloadEnvelope Gamma bound
        (Rew.bShift (shortBinaryNumeralTerm bound)) body
        boundEqualityResource branchResource <=
      closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
        syntaxCode bodyCode branchBound boundEqualityBound := by
  let shiftedGamma := Gamma.image Rewriting.shift
  let boundTerm := Rew.bShift (shortBinaryNumeralTerm bound)
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
  let termBound := closedShortUniversalShellTermPolynomial numericBound bitBound
  let rawFormulaBound := closedShortUniversalShellRawFormulaPolynomial
    numericBound bitBound syntaxCode bodyCode
  let sourceFormulaBound := closedShortUniversalShellSourceFormulaPolynomial
    numericBound bitBound syntaxCode bodyCode
  let formulaBound := closedShortUniversalShellFormulaPolynomial numericBound
    bitBound syntaxCode bodyCode
  let localBound := closedShortUniversalShellLocalPayloadPolynomial numericBound
    bitBound syntaxCode bodyCode
  let transportLocal := arbitraryContextRelationTransportLocalEnvelope
    formulaBound termBound
  have hshiftedCard : shiftedGamma.card <= 1 := by
    exact Finset.card_image_le.trans hGammaCard
  have hshortCode :
      (binaryTermCode (shortBinaryNumeralTerm bound)).length <=
        binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope bound bitBound hboundSize
  have hrawSource : rawFormulaBound <= sourceFormulaBound := by
    dsimp only [rawFormulaBound, sourceFormulaBound]
    unfold closedShortUniversalShellSourceFormulaPolynomial
    omega
  have hsourceFormula : sourceFormulaBound <= formulaBound := by
    dsimp only [sourceFormulaBound, formulaBound]
    unfold closedShortUniversalShellFormulaPolynomial
    omega
  have hGammaSource' : FormulaCodeBound Gamma sourceFormulaBound := by
    simpa only [sourceFormulaBound] using hGammaSource
  have hshiftedFormula' :
      FormulaCodeBound shiftedGamma formulaBound := by
    simpa only [shiftedGamma, formulaBound] using hshiftedFormula
  have hboundTermShift := binaryTermCode_bShift_length_le_add_symbols
    (shortBinaryNumeralTerm bound)
  have hshortSymbols := termSymbolCount_le_binaryTermCode_length
    (shortBinaryNumeralTerm bound)
  have hboundTermRaw : (binaryTermCode boundTerm).length <=
      3 * (binaryTermCode (shortBinaryNumeralTerm bound)).length := by
    dsimp only [boundTerm]
    omega
  have hboundTerm : (binaryTermCode boundTerm).length <= termBound := by
    dsimp only [termBound]
    unfold closedShortUniversalShellTermPolynomial
    omega
  have hfreeBoundRaw := binaryTermCode_free_length_le boundTerm
  have hfreeBound : (binaryTermCode freeBoundTerm).length <= termBound := by
    dsimp only [freeBoundTerm, termBound]
    unfold closedShortUniversalShellTermPolynomial
    omega
  have hcanonicalTermRaw :=
    iteratedSuccessorTerm_code_length_le_polynomial 0 bound
  have hcanonicalTermMono :=
    iteratedSuccessorTermCodePolynomial_mono 0 hbound
  have hcanonicalTerm : (binaryTermCode canonicalTerm).length <=
      termBound := by
    dsimp only [canonicalTerm, termBound]
    unfold closedShortUniversalShellTermPolynomial
    omega
  have hsubjectTerm : (binaryTermCode subjectTerm).length <= termBound := by
    dsimp only [subjectTerm, termBound]
    unfold closedShortUniversalShellTermPolynomial
    omega
  have hbodyRaw : (binaryFormulaCode body).length <= rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold closedShortUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have htargetFree := binaryFormulaCode_free_length_le body
  have htargetTight : (binaryFormulaCode targetFormula).length <=
      2 * (binaryFormulaCode body).length := by
    simpa only [targetFormula] using htargetFree
  have htarget : (binaryFormulaCode targetFormula).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold closedShortUniversalShellRawFormulaPolynomial
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
    unfold closedShortUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hcanonicalBoundRaw := finiteBoundFormula_code_le_boundedUniversal bound
    syntaxCode hsyntaxBound
  have hcanonicalBoundTight : (binaryFormulaCode canonicalBound).length <=
      boundedUniversalClosedFormulaEnvelope syntaxCode := by
    simpa only [canonicalBound] using hcanonicalBoundRaw
  have hcanonicalBound : (binaryFormulaCode canonicalBound).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold closedShortUniversalShellRawFormulaPolynomial
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
    unfold closedShortUniversalShellRawFormulaPolynomial
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
    unfold closedShortUniversalShellRawFormulaPolynomial
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
    unfold closedShortUniversalShellRawFormulaPolynomial
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
    have : (binaryFormulaCode (left 🡒 right)).length <=
        sourceFormulaBound := by
      dsimp only [sourceFormulaBound]
      unfold closedShortUniversalShellSourceFormulaPolynomial
      omega
    exact this
  have hcanonicalImplication :
      (binaryFormulaCode canonicalImplication).length <=
        sourceFormulaBound := by
    dsimp only [canonicalImplication]
    exact himplication canonicalBound targetFormula hcanonicalBound htarget
  have hsymmetryImplication :
      (binaryFormulaCode symmetryImplication).length <=
        sourceFormulaBound := by
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
      unfold closedShortUniversalShellFormulaPolynomial
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
    unfold closedShortUniversalShellRawFormulaPolynomial
    have hzeroTerm :
        (binaryTermCode
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
            termBound := by
      dsimp only [termBound]
      unfold closedShortUniversalShellTermPolynomial
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
    unfold closedShortUniversalShellSourceFormulaPolynomial
    omega
  have huniversalFormulaRaw := binaryFormulaCode_all_length_le universalBody
  have huniversalFormula :
      (binaryFormulaCode
        (∀⁰ universalBody : LO.FirstOrder.ArithmeticProposition)).length <=
          sourceFormulaBound := by
    dsimp only [sourceFormulaBound]
    unfold closedShortUniversalShellSourceFormulaPolynomial
    omega
  have hfreeUniversalBodyRaw := binaryFormulaCode_free_length_le universalBody
  have hfreeUniversalBody :
      (binaryFormulaCode (Rewriting.free universalBody)).length <=
        formulaBound := by
    dsimp only [formulaBound]
    unfold closedShortUniversalShellFormulaPolynomial
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
  have horiginalContextBound : FormulaCodeBound originalContext formulaBound :=
    by
      dsimp only [originalContext]
      exact hshiftedFormula'.insert hnegatedOriginalBound
  have horiginalContextCard : originalContext.card <= 4 := by
    have hstep := Finset.card_insert_le (∼originalBound) shiftedGamma
    dsimp only [originalContext]
    omega
  have hcanonicalDischarge :=
    contextualDischargeFullAssemblyCost_le_openIndexUniversalShell
      shiftedGamma canonicalBound targetFormula formulaBound (by omega)
      hshiftedFormula' htargetFormula hcanonicalImplicationFormula
      hnegatedCanonicalBound
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
  have horiginalAssumption := assumptionFullPayloadCost_le_small
    originalContext originalBound formulaBound horiginalContextCard
      horiginalContextBound horiginalBoundFormula
  have hsymmetry := equalitySymmetryImplication_payloadLength_le_primitive
    canonicalTerm freeBoundTerm termBound hcanonicalTerm hfreeBound
  have hsymmetryInsertBound : FormulaCodeBound
      (insert symmetryImplication shiftedGamma) formulaBound :=
    hshiftedFormula'.insert hsymmetryImplicationFormula
  have hsymmetryInsertCard :
      (insert symmetryImplication shiftedGamma).card <= 8 := by
    have hstep := Finset.card_insert_le symmetryImplication shiftedGamma
    omega
  have hweakSymmetry := weakeningFullAssemblyCost_le_small
    (insert symmetryImplication shiftedGamma) formulaBound
      hsymmetryInsertCard hsymmetryInsertBound
  have hmpSymmetry := contextualModusPonensFullAssemblyCost_le_small
    shiftedGamma forwardEquality backwardEquality formulaBound (by omega)
      hshiftedFormula' hforwardEqualityFormula hbackwardEqualityFormula
      hsymmetryImplicationFormula hnegatedSymmetryImplication hnegatedBackward
  have hbackwardInsertBound : FormulaCodeBound
      (insert backwardEquality originalContext) formulaBound :=
    horiginalContextBound.insert hbackwardEqualityFormula
  have hbackwardInsertCard :
      (insert backwardEquality originalContext).card <= 8 := by
    have hstep := Finset.card_insert_le backwardEquality originalContext
    omega
  have hweakBackward := weakeningFullAssemblyCost_le_small
    (insert backwardEquality originalContext) formulaBound
      hbackwardInsertCard hbackwardInsertBound
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
    contextualDischargeFullAssemblyCost_le_openIndexUniversalShell
      shiftedGamma originalBound targetFormula formulaBound (by omega)
      hshiftedFormula' htargetFormula horiginalTargetImplicationFormula
      hnegatedOriginalBound
  have hshiftSource : 2 * sourceFormulaBound <= formulaBound := by
    dsimp only [formulaBound]
    unfold closedShortUniversalShellFormulaPolynomial
    omega
  have huniversalIntroduction :=
    contextualUniversalIntroductionFullAssemblyCost_le_openIndexUniversalShell
      Gamma universalBody sourceFormulaBound formulaBound (by omega)
      hGammaSource' (huniversalBody.trans hformulaPositive)
      hfreeUniversalBody huniversalFormula hshiftSource
  have hlocalBound : localBound =
      smallContextAssemblyEnvelope formulaBound := by
    dsimp only [localBound, formulaBound]
    rfl
  simp only [shiftedGamma, canonicalBound, targetFormula]
    at hcanonicalDischarge
  simp only [canonicalImplication, canonicalBound, targetFormula,
    originalContext, originalBound, shiftedGamma] at hweakCanonical
  simp only [originalContext, originalBound, shiftedGamma]
    at horiginalAssumption
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
  simp only [originalContext, originalBound, shiftedGamma, canonicalBound]
    at hmpOriginalCanonical
  simp only [originalContext, originalBound, shiftedGamma, canonicalBound,
    targetFormula] at hmpCanonicalTarget
  simp only [shiftedGamma, originalBound, targetFormula]
    at horiginalDischarge
  simp only [universalBody] at huniversalIntroduction
  change compileContextualTermBoundedUniversalPayloadEnvelope Gamma bound
      boundTerm body boundEqualityResource branchResource <=
    branchBound + boundEqualityBound +
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

theorem
    compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (bound numericBound bitBound syntaxCode bodyCode : Nat)
    (boundEqualityResource branchResource boundEqualityBound branchBound : Nat)
    (hbound : bound <= numericBound)
    (hboundSize : Nat.size bound <= bitBound)
    (hsyntaxBound : bound <= syntaxCode)
    (hbody : (binaryFormulaCode body).length <= bodyCode)
    (hboundEquality : boundEqualityResource <= boundEqualityBound)
    (hbranches : branchResource <= branchBound) :
    compileContextualTermBoundedUniversalPayloadEnvelope ∅ bound
        (Rew.bShift (shortBinaryNumeralTerm bound)) body
        boundEqualityResource branchResource <=
      closedShortUniversalShellFixedPayloadPolynomial numericBound bitBound
        syntaxCode bodyCode branchBound boundEqualityBound := by
  exact
    compileContextualTermBoundedUniversalPayloadEnvelope_short_le_fixed_of_context
      body ∅ bound numericBound bitBound syntaxCode bodyCode
      boundEqualityResource branchResource boundEqualityBound branchBound
      hbound hboundSize hsyntaxBound hbody hboundEquality hbranches
      (by simp)
      (by
        intro formula hformula
        simp at hformula)
      (by
        intro formula hformula
        simp at hformula)

#print axioms
  closedShortTermBoundedUniversalFormula_code_length_le_source
#print axioms
  compileContextualTermBoundedUniversalPayloadEnvelope_short_le_fixed_of_context
#print axioms
  compileContextualTermBoundedUniversalPayloadEnvelope_empty_short_le_fixed

end FoundationCompactPAClosedShortBoundedUniversalShellFixedBounds
