import integration.FoundationCompactNumericListedDirectAdditiveBoundaryTableDirectCompiler
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fixed polynomial bounds for the direct additive boundary table

This layer removes the remaining concrete syntax coordinates from the uniform
boundary-row compiler.  Both the arity-two witness terminal and the arity-three
universal body are bounded by explicit polynomials in one numeric coordinate
and one bit-width coordinate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectFixedPolynomialBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalCompilerBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAFiniteExhaustionSuccessor
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPANegativeEqualityBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitDirectUniversalBranchesPolynomialBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveBoundaryTableFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveBoundaryTableDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

def boundaryRowBranchSubstitutionTermCodePolynomial
    (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  5 * numeralCode +
    (binaryTermCode
      (boundaryTableClosedShift 2 (&0 : ValuationTerm))).length +
    (binaryTermCode
      (boundaryTableClosedShift 2 (‘&0 + 1’ : ValuationTerm))).length +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 2)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 2)).length + 4

def boundaryRowEmbeddedEntryFormulaCodeFromTermPolynomial
    (termCode : Nat) : Nat :=
  uniformRewritingFormulaCodeEnvelope
    termCode
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val)).length

def boundaryRowEmbeddedEntryFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  boundaryRowEmbeddedEntryFormulaCodeFromTermPolynomial
    (boundaryRowBranchSubstitutionTermCodePolynomial bitBound)

def boundaryRowDirectTerminalFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let entryCode := boundaryRowEmbeddedEntryFormulaCodePolynomial bitBound
  let ltCode :=
    (binaryFormulaCode
      (“#1 < #0” : ArithmeticSemiformula Nat 2)).length
  2 * entryCode + ltCode + 2 * (binaryNatCode 4).length + 1

private theorem boundaryClosedShift_two_code_length_le_five
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    (binaryTermCode (boundaryTableClosedShift 2 term)).length <=
      5 * bound := by
  have hsymbols : termSymbolCount term <= bound :=
    (termSymbolCount_le_binaryTermCode_length term).trans hterm
  have hfirstRaw := binaryTermCode_bShift_length_le_add_symbols term
  have hfirst : (binaryTermCode (Rew.bShift term)).length <=
      3 * bound := by
    omega
  have hshiftedSymbols : termSymbolCount (Rew.bShift term) <= bound := by
    rw [termSymbolCount_bShift]
    exact hsymbols
  have hsecondRaw :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift term)
  rw [boundaryTableClosedShift_succ, boundaryTableClosedShift_succ,
    boundaryTableClosedShift_zero]
  omega

private theorem compactFixedWidthEntryEmbeddedSubstitution_code_length_le
    {targetArity : Nat} (termCode : Nat)
    (terms : Fin 4 -> ArithmeticSemiterm Nat targetArity)
    (hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        terms)).length <=
      boundaryRowEmbeddedEntryFormulaCodeFromTermPolynomial termCode := by
  let source : ArithmeticSemiformula Nat 4 :=
    Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val
  let rewriting : Rew ℒₒᵣ Nat 4 Nat targetArity := Rew.subst terms
  have hrewriting : RewritingImageCodeBound rewriting termCode := by
    constructor
    · intro coordinate
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      exact hterms coordinate
    · intro coordinate
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting termCode
    hrewriting source
  simpa only [boundaryRowEmbeddedEntryFormulaCodeFromTermPolynomial, source,
    rewriting] using hraw

theorem compactAdditiveBoundaryTableRowDirectTerminal_code_length_le_fixed
    (tokenCount boundaryTable bitBound : Nat)
    (htokenSize : Nat.size tokenCount <= bitBound)
    (htableSize : Nat.size boundaryTable <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveBoundaryTableRowDirectTerminal
        tokenCount boundaryTable)).length <=
      boundaryRowDirectTerminalFormulaCodePolynomial bitBound := by
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm := boundaryTableClosedShift 2 (&0 : ValuationTerm)
  let rightIndexTerm := boundaryTableClosedShift 2 (‘&0 + 1’ : ValuationTerm)
  let leftValueTerm := (#1 : ArithmeticSemiterm Nat 2)
  let rightValueTerm := (#0 : ArithmeticSemiterm Nat 2)
  let leftTerms : Fin 4 -> ArithmeticSemiterm Nat 2 :=
    ![boundaryTableClosedShift 2 tableTerm,
      boundaryTableClosedShift 2 widthTerm,
      leftIndexTerm, leftValueTerm]
  let rightTerms : Fin 4 -> ArithmeticSemiterm Nat 2 :=
    ![boundaryTableClosedShift 2 tableTerm,
      boundaryTableClosedShift 2 widthTerm,
      rightIndexTerm, rightValueTerm]
  let leftFormula : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ leftTerms
  let rightFormula : ArithmeticSemiformula Nat 2 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ rightTerms
  let ltFormula : ArithmeticSemiformula Nat 2 := “#1 < #0”
  let termCode := boundaryRowBranchSubstitutionTermCodePolynomial bitBound
  let entryCode := boundaryRowEmbeddedEntryFormulaCodePolynomial bitBound
  have htableCode : (binaryTermCode tableTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope boundaryTable bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope tokenCount bitBound htokenSize
  have htableShiftRaw := boundaryClosedShift_two_code_length_le_five tableTerm
    (binaryNumeralTermCodeEnvelope bitBound) htableCode
  have hwidthShiftRaw := boundaryClosedShift_two_code_length_le_five widthTerm
    (binaryNumeralTermCodeEnvelope bitBound) hwidthCode
  have htableShift :
      (binaryTermCode
        (boundaryTableClosedShift 2 tableTerm)).length <= termCode := by
    exact htableShiftRaw.trans (by
      unfold termCode boundaryRowBranchSubstitutionTermCodePolynomial
      dsimp only
      omega)
  have hwidthShift :
      (binaryTermCode
        (boundaryTableClosedShift 2 widthTerm)).length <= termCode := by
    exact hwidthShiftRaw.trans (by
      unfold termCode boundaryRowBranchSubstitutionTermCodePolynomial
      dsimp only
      omega)
  have hleftIndex : (binaryTermCode leftIndexTerm).length <= termCode := by
    unfold termCode boundaryRowBranchSubstitutionTermCodePolynomial
    dsimp only [leftIndexTerm]
    omega
  have hrightIndex : (binaryTermCode rightIndexTerm).length <= termCode := by
    unfold termCode boundaryRowBranchSubstitutionTermCodePolynomial
    dsimp only [rightIndexTerm]
    omega
  have hleftValue : (binaryTermCode leftValueTerm).length <= termCode := by
    unfold termCode boundaryRowBranchSubstitutionTermCodePolynomial
    dsimp only [leftValueTerm]
    omega
  have hrightValue : (binaryTermCode rightValueTerm).length <= termCode := by
    unfold termCode boundaryRowBranchSubstitutionTermCodePolynomial
    dsimp only [rightValueTerm]
    omega
  have hleftTerms : forall coordinate,
      (binaryTermCode (leftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htableShift
    · exact hwidthShift
    · exact hleftIndex
    · exact hleftValue
  have hrightTerms : forall coordinate,
      (binaryTermCode (rightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htableShift
    · exact hwidthShift
    · exact hrightIndex
    · exact hrightValue
  have hleft : (binaryFormulaCode leftFormula).length <= entryCode := by
    simpa only [leftFormula, entryCode, termCode,
      boundaryRowEmbeddedEntryFormulaCodePolynomial] using
      compactFixedWidthEntryEmbeddedSubstitution_code_length_le
        termCode leftTerms hleftTerms
  have hright : (binaryFormulaCode rightFormula).length <= entryCode := by
    simpa only [rightFormula, entryCode, termCode,
      boundaryRowEmbeddedEntryFormulaCodePolynomial] using
      compactFixedWidthEntryEmbeddedSubstitution_code_length_le
        termCode rightTerms hrightTerms
  have hinner := andSemiformula_code_length_le rightFormula ltFormula
  have houter := andSemiformula_code_length_le leftFormula
    (rightFormula ⋏ ltFormula)
  change
    (binaryFormulaCode (leftFormula ⋏
      (rightFormula ⋏ ltFormula))).length <= _
  unfold boundaryRowDirectTerminalFormulaCodePolynomial
  dsimp only [entryCode, ltFormula] at hinner houter ⊢
  omega

def boundaryRowUniformBranchFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 2
    (unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound)
    numericBound
    (boundaryRowDirectTerminalFormulaCodePolynomial bitBound)
    (boundaryRowTerminalFullyUniformPayloadPolynomial numericBound bitBound)

theorem
    compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope_le_fixed
    (tokenCount boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope
        tokenCount boundaryTable numericBound bitBound <=
      boundaryRowUniformBranchFixedPayloadPolynomial numericBound
        bitBound := by
  have htokenSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hbody :=
    compactAdditiveBoundaryTableRowDirectTerminal_code_length_le_fixed
      tokenCount boundaryTable bitBound htokenSize htableSize
  unfold compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope
    boundaryRowUniformBranchFixedPayloadPolynomial
  dsimp only
  exact explicitBoundedWitnessDirectPublicPayloadEnvelope_two_mono
    (unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound)
    (boundaryRowTerminalFullyUniformPayloadPolynomial numericBound bitBound)
    htokenCount hbody

def boundaryRowUniversalSubstitutionTermCodePolynomial
    (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  7 * numeralCode +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 3)).length +
    (binaryTermCode (#1 : ArithmeticSemiterm Nat 3)).length +
    (binaryTermCode (#2 : ArithmeticSemiterm Nat 3)).length +
    (binaryTermCode (‘#2 + 1’ : ArithmeticSemiterm Nat 3)).length + 4

def boundaryRowUniversalEmbeddedEntryFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  boundaryRowEmbeddedEntryFormulaCodeFromTermPolynomial
    (boundaryRowUniversalSubstitutionTermCodePolynomial bitBound)

def boundaryRowUniversalTerminalFormulaCodePolynomial
    (bitBound : Nat) : Nat :=
  let entryCode :=
    boundaryRowUniversalEmbeddedEntryFormulaCodePolynomial bitBound
  let ltCode :=
    (binaryFormulaCode
      (“#1 < #0” : ArithmeticSemiformula Nat 3)).length
  2 * entryCode + ltCode + 2 * (binaryNatCode 4).length + 1

def boundaryRowUniversalBodyFormulaCodePolynomial
    (numericBound bitBound : Nat) : Nat :=
  let terminalCode :=
    boundaryRowUniversalTerminalFormulaCodePolynomial bitBound
  let innerCode := explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2
    numericBound terminalCode
  explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 1 numericBound
    innerCode

private theorem boundaryClosedShift_three_code_length_le_seven
    (term : ValuationTerm) (bound : Nat)
    (hterm : (binaryTermCode term).length <= bound) :
    (binaryTermCode (boundaryTableClosedShift 3 term)).length <=
      7 * bound := by
  have hsymbols : termSymbolCount term <= bound :=
    (termSymbolCount_le_binaryTermCode_length term).trans hterm
  have hfirstRaw := binaryTermCode_bShift_length_le_add_symbols term
  have hfirst : (binaryTermCode (Rew.bShift term)).length <=
      3 * bound := by
    omega
  have hfirstSymbols : termSymbolCount (Rew.bShift term) <= bound := by
    rw [termSymbolCount_bShift]
    exact hsymbols
  have hsecondRaw :=
    binaryTermCode_bShift_length_le_add_symbols (Rew.bShift term)
  have hsecond :
      (binaryTermCode (Rew.bShift (Rew.bShift term))).length <=
        5 * bound := by
    omega
  have hsecondSymbols :
      termSymbolCount (Rew.bShift (Rew.bShift term)) <= bound := by
    rw [termSymbolCount_bShift, termSymbolCount_bShift]
    exact hsymbols
  have hthirdRaw := binaryTermCode_bShift_length_le_add_symbols
    (Rew.bShift (Rew.bShift term))
  rw [boundaryTableClosedShift_succ, boundaryTableClosedShift_succ,
    boundaryTableClosedShift_succ, boundaryTableClosedShift_zero]
  omega

theorem compactAdditiveBoundaryTableRowTerminal_code_length_le_fixed
    (tokenCount boundaryTable bitBound : Nat)
    (htokenSize : Nat.size tokenCount <= bitBound)
    (htableSize : Nat.size boundaryTable <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveBoundaryTableRowTerminal
        tokenCount boundaryTable)).length <=
      boundaryRowUniversalTerminalFormulaCodePolynomial bitBound := by
  let tableTerm := shortBinaryNumeralTerm boundaryTable
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let leftIndexTerm := (#2 : ArithmeticSemiterm Nat 3)
  let rightIndexTerm := (‘#2 + 1’ : ArithmeticSemiterm Nat 3)
  let leftValueTerm := (#1 : ArithmeticSemiterm Nat 3)
  let rightValueTerm := (#0 : ArithmeticSemiterm Nat 3)
  let leftTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![boundaryTableClosedShift 3 tableTerm,
      boundaryTableClosedShift 3 widthTerm,
      leftIndexTerm, leftValueTerm]
  let rightTerms : Fin 4 -> ArithmeticSemiterm Nat 3 :=
    ![boundaryTableClosedShift 3 tableTerm,
      boundaryTableClosedShift 3 widthTerm,
      rightIndexTerm, rightValueTerm]
  let leftFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ leftTerms
  let rightFormula : ArithmeticSemiformula Nat 3 :=
    (Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜ rightTerms
  let ltFormula : ArithmeticSemiformula Nat 3 := “#1 < #0”
  let termCode := boundaryRowUniversalSubstitutionTermCodePolynomial bitBound
  let entryCode :=
    boundaryRowUniversalEmbeddedEntryFormulaCodePolynomial bitBound
  have htableCode : (binaryTermCode tableTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope boundaryTable bitBound htableSize
  have hwidthCode : (binaryTermCode widthTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope tokenCount bitBound htokenSize
  have htableShiftRaw := boundaryClosedShift_three_code_length_le_seven
    tableTerm (binaryNumeralTermCodeEnvelope bitBound) htableCode
  have hwidthShiftRaw := boundaryClosedShift_three_code_length_le_seven
    widthTerm (binaryNumeralTermCodeEnvelope bitBound) hwidthCode
  have htableShift :
      (binaryTermCode
        (boundaryTableClosedShift 3 tableTerm)).length <= termCode := by
    exact htableShiftRaw.trans (by
      unfold termCode boundaryRowUniversalSubstitutionTermCodePolynomial
      dsimp only
      omega)
  have hwidthShift :
      (binaryTermCode
        (boundaryTableClosedShift 3 widthTerm)).length <= termCode := by
    exact hwidthShiftRaw.trans (by
      unfold termCode boundaryRowUniversalSubstitutionTermCodePolynomial
      dsimp only
      omega)
  have hleftIndex : (binaryTermCode leftIndexTerm).length <= termCode := by
    unfold termCode boundaryRowUniversalSubstitutionTermCodePolynomial
    dsimp only [leftIndexTerm]
    omega
  have hrightIndex : (binaryTermCode rightIndexTerm).length <= termCode := by
    unfold termCode boundaryRowUniversalSubstitutionTermCodePolynomial
    dsimp only [rightIndexTerm]
    omega
  have hleftValue : (binaryTermCode leftValueTerm).length <= termCode := by
    unfold termCode boundaryRowUniversalSubstitutionTermCodePolynomial
    dsimp only [leftValueTerm]
    omega
  have hrightValue : (binaryTermCode rightValueTerm).length <= termCode := by
    unfold termCode boundaryRowUniversalSubstitutionTermCodePolynomial
    dsimp only [rightValueTerm]
    omega
  have hleftTerms : forall coordinate,
      (binaryTermCode (leftTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htableShift
    · exact hwidthShift
    · exact hleftIndex
    · exact hleftValue
  have hrightTerms : forall coordinate,
      (binaryTermCode (rightTerms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact htableShift
    · exact hwidthShift
    · exact hrightIndex
    · exact hrightValue
  have hleft : (binaryFormulaCode leftFormula).length <= entryCode := by
    simpa only [leftFormula, entryCode,
      boundaryRowUniversalEmbeddedEntryFormulaCodePolynomial] using
      compactFixedWidthEntryEmbeddedSubstitution_code_length_le
        termCode leftTerms hleftTerms
  have hright : (binaryFormulaCode rightFormula).length <= entryCode := by
    simpa only [rightFormula, entryCode,
      boundaryRowUniversalEmbeddedEntryFormulaCodePolynomial] using
      compactFixedWidthEntryEmbeddedSubstitution_code_length_le
        termCode rightTerms hrightTerms
  have hinner := andSemiformula_code_length_le rightFormula ltFormula
  have houter := andSemiformula_code_length_le leftFormula
    (rightFormula ⋏ ltFormula)
  change
    (binaryFormulaCode (leftFormula ⋏
      (rightFormula ⋏ ltFormula))).length <= _
  unfold boundaryRowUniversalTerminalFormulaCodePolynomial
  dsimp only [entryCode, ltFormula] at hinner houter ⊢
  omega

theorem compactAdditiveBoundaryTableRowBody_code_length_le_fixed
    (tokenCount boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveBoundaryTableRowBody
        tokenCount boundaryTable)).length <=
      boundaryRowUniversalBodyFormulaCodePolynomial numericBound
        bitBound := by
  let terminal := compactAdditiveBoundaryTableRowTerminal
    tokenCount boundaryTable
  let inner := terminal.bexsLTSucc
    (boundaryTableClosedShift 2 (shortBinaryNumeralTerm tokenCount))
  let terminalCode :=
    boundaryRowUniversalTerminalFormulaCodePolynomial bitBound
  let innerCode := explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope 2
    numericBound terminalCode
  have htokenSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hterminal : (binaryFormulaCode terminal).length <= terminalCode := by
    simpa only [terminal, terminalCode] using
      compactAdditiveBoundaryTableRowTerminal_code_length_le_fixed
        tokenCount boundaryTable bitBound htokenSize htableSize
  have hinnerRaw := explicitBoundedWitnessRecursiveBody_code_length_le_public
    (arity := 2) tokenCount terminalCode terminal hterminal
  have hinnerMono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_completed 2
      htokenCount (Nat.le_refl terminalCode)
  have hinner : (binaryFormulaCode inner).length <= innerCode := by
    exact hinnerRaw.trans (by
      simpa only [innerCode] using hinnerMono)
  have houterRaw := explicitBoundedWitnessRecursiveBody_code_length_le_public
    (arity := 1) tokenCount innerCode inner hinner
  have houterMono :=
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono_completed 1
      htokenCount (Nat.le_refl innerCode)
  unfold compactAdditiveBoundaryTableRowBody
    boundaryRowUniversalBodyFormulaCodePolynomial
  dsimp only [terminal, inner, terminalCode, innerCode] at houterRaw houterMono ⊢
  exact houterRaw.trans houterMono

def boundaryRowDirectUniversalSyntaxFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound +
    boundaryRowUniversalBodyFormulaCodePolynomial numericBound bitBound + 1

def boundaryRowDirectUniversalFormulaFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxCode :=
    boundaryRowDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  boundedUniversalClosedFormulaEnvelope syntaxCode +
    2 * boundaryRowUniversalBodyFormulaCodePolynomial numericBound bitBound + 1

def boundaryRowDirectUniversalLocalFixedPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (boundaryRowDirectUniversalFormulaFixedPolynomial numericBound bitBound)

def boundaryRowUniformDirectBranchesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  (numericBound + 1) *
    (boundaryRowUniformBranchFixedPayloadPolynomial numericBound bitBound +
      3 * boundaryRowDirectUniversalLocalFixedPolynomial numericBound
        bitBound)

private theorem explicitDirectUniversalLocalPayloadEnvelope_le_fixed
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    explicitDirectUniversalLocalPayloadEnvelope partCount
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable) <=
      boundaryRowDirectUniversalLocalFixedPolynomial numericBound
        bitBound := by
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let bodyCode := boundaryRowUniversalBodyFormulaCodePolynomial numericBound
    bitBound
  let exactSyntax := explicitDirectUniversalSyntaxResource partCount body
  let fixedSyntax :=
    boundaryRowDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  let exactFormula := explicitDirectUniversalFormulaEnvelope partCount body
  let fixedFormula :=
    boundaryRowDirectUniversalFormulaFixedPolynomial numericBound bitBound
  have hbody : (binaryFormulaCode body).length <= bodyCode := by
    simpa only [body, bodyCode] using
      compactAdditiveBoundaryTableRowBody_code_length_le_fixed tokenCount
        boundaryTable numericBound bitBound htokenCount htableSize hnumericSize
  have hsyntax : exactSyntax <= fixedSyntax := by
    unfold exactSyntax fixedSyntax explicitDirectUniversalSyntaxResource
      boundaryRowDirectUniversalSyntaxFixedPolynomial
    dsimp only [body, bodyCode] at hbody ⊢
    omega
  have hclosed := boundedUniversalClosedFormulaEnvelope_mono_completed hsyntax
  have hformula : exactFormula <= fixedFormula := by
    unfold exactFormula fixedFormula explicitDirectUniversalFormulaEnvelope
      boundaryRowDirectUniversalFormulaFixedPolynomial
    dsimp only [exactSyntax, fixedSyntax, body, bodyCode] at hclosed hbody ⊢
    omega
  exact smallContextAssemblyEnvelope_mono_local hformula

theorem
    compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope_le_fixed
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
        tokenCount partCount boundaryTable numericBound bitBound <=
      boundaryRowUniformDirectBranchesFixedPayloadPolynomial numericBound
        bitBound := by
  have hraw :=
    compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope_le_polynomial
      tokenCount partCount boundaryTable numericBound bitBound
  have hbranch :=
    compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope_le_fixed
      tokenCount boundaryTable numericBound bitBound htokenCount htableSize
      hnumericSize
  have hlocal := explicitDirectUniversalLocalPayloadEnvelope_le_fixed
    tokenCount partCount boundaryTable numericBound bitBound htokenCount
    hpartCount htableSize hnumericSize
  unfold explicitDirectUniversalBranchesPayloadPolynomial at hraw
  unfold boundaryRowUniformDirectBranchesFixedPayloadPolynomial
  exact hraw.trans (Nat.mul_le_mul (by omega) (by omega))

def boundaryRowContextualBranchesFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxCode :=
    boundaryRowDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    boundaryRowDirectUniversalFormulaFixedPolynomial numericBound bitBound
  boundaryRowUniformDirectBranchesFixedPayloadPolynomial numericBound
      bitBound +
    cumulativeFiniteExhaustionPayloadPolynomial syntaxCode +
    boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode +
    4 * smallContextAssemblyEnvelope formulaCode

theorem boundaryRowContextualBranchesResource_le_fixed
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    contextualBranchesUnderBoundPayloadEnvelope ∅ partCount
        (Rewriting.free
          (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable))
        (compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
          tokenCount partCount boundaryTable numericBound bitBound) <=
      boundaryRowContextualBranchesFixedPayloadPolynomial numericBound
        bitBound := by
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let targetFormula := Rewriting.free body
  let syntaxCode :=
    boundaryRowDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  let formulaCode :=
    boundaryRowDirectUniversalFormulaFixedPolynomial numericBound bitBound
  let caseResource :=
    compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
      tokenCount partCount boundaryTable numericBound bitBound
  let caseBound := boundaryRowUniformDirectBranchesFixedPayloadPolynomial
    numericBound bitBound
  let finiteContext := contextualFiniteBoundContext
    (∅ : Finset LO.FirstOrder.ArithmeticProposition) partCount
  let localBound := smallContextAssemblyEnvelope formulaCode
  have hbody : (binaryFormulaCode body).length <=
      boundaryRowUniversalBodyFormulaCodePolynomial numericBound bitBound :=
    compactAdditiveBoundaryTableRowBody_code_length_le_fixed tokenCount
      boundaryTable numericBound bitBound htokenCount htableSize hnumericSize
  have hboundSyntax : partCount <= syntaxCode := by
    unfold syntaxCode boundaryRowDirectUniversalSyntaxFixedPolynomial
    omega
  have hbodySyntax : (binaryFormulaCode body).length <= syntaxCode := by
    exact hbody.trans (by
      unfold syntaxCode boundaryRowDirectUniversalSyntaxFixedPolynomial
      omega)
  have hclosedLe : boundedUniversalClosedFormulaEnvelope syntaxCode <=
      formulaCode := by
    unfold formulaCode boundaryRowDirectUniversalFormulaFixedPolynomial
    dsimp only [syntaxCode]
    omega
  have htargetCode : (binaryFormulaCode targetFormula).length <=
      formulaCode := by
    have hfree := binaryFormulaCode_free_length_le body
    dsimp only [targetFormula]
    exact hfree.trans (by
      unfold formulaCode boundaryRowDirectUniversalFormulaFixedPolynomial
      dsimp only [syntaxCode]
      omega)
  have hnegatedFiniteBound :=
    negatedFiniteBoundFormula_code_le_boundedUniversal partCount syntaxCode
      hboundSyntax
  have hdoubleNegatedFiniteBound :=
    doubleNegatedFiniteBoundFormula_code_le_boundedUniversal partCount
      syntaxCode hboundSyntax
  have hnegatedCases :=
    negatedFiniteEqualityCases_code_le_boundedUniversal partCount syntaxCode
      (by omega)
  have hfiniteExhaustion :=
    finiteExhaustionFormula_code_le_boundedUniversal partCount syntaxCode
      hboundSyntax
  have hnegatedFiniteExhaustion :=
    negatedFiniteExhaustionFormula_code_le_boundedUniversal partCount
      syntaxCode hboundSyntax
  have hfiniteContextBound : FormulaCodeBound finiteContext formulaCode := by
    dsimp only [finiteContext]
    unfold contextualFiniteBoundContext
    exact (show FormulaCodeBound
      (∅ : Finset LO.FirstOrder.ArithmeticProposition) formulaCode by
        intro formula hformula
        simp at hformula).insert (hnegatedFiniteBound.trans hclosedLe)
  have hfiniteContextCard : finiteContext.card <= 4 := by
    dsimp only [finiteContext]
    simp [contextualFiniteBoundContext]
  have hlower :
      lowerBoundContradictionFullPayloadCost partCount targetFormula <=
        localBound := by
    exact lowerBoundContradictionFullPayloadCost_le_completed partCount
      targetFormula formulaCode htargetCode
      ((finiteBoundFormula_code_le_boundedUniversal partCount syntaxCode
        hboundSyntax).trans hclosedLe)
      (hnegatedFiniteBound.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe)
  have hweakContextBound : FormulaCodeBound
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula partCount (&0)) finiteContext))
      formulaCode :=
    (hfiniteContextBound.insert
      (hdoubleNegatedFiniteBound.trans hclosedLe)).insert htargetCode
  have hweakContextCard :
      (insert targetFormula
        (insert (∼finiteLowerBoundFormula partCount (&0))
          finiteContext)).card <= 8 := by
    have hfirst := Finset.card_insert_le
      (∼finiteLowerBoundFormula partCount (&0)) finiteContext
    have hsecond := Finset.card_insert_le targetFormula
      (insert (∼finiteLowerBoundFormula partCount (&0)) finiteContext)
    omega
  have hweak := weakeningFullAssemblyCost_le_small
    (insert targetFormula
      (insert (∼finiteLowerBoundFormula partCount (&0)) finiteContext))
    formulaCode hweakContextCard hweakContextBound
  have heliminate := eliminateDisjunctionAssumptionFullAssemblyCost_le_small
    finiteContext targetFormula (finiteEqualityCases (&0) partCount)
      (finiteLowerBoundFormula partCount (&0)) formulaCode
      hfiniteContextCard hfiniteContextBound htargetCode
      (hnegatedCases.trans hclosedLe)
      (hdoubleNegatedFiniteBound.trans hclosedLe) (by
        simpa only [finiteExhaustionFormula, finiteLowerBoundFormula] using
          hnegatedFiniteExhaustion.trans hclosedLe)
  have hcut := cutClosedAssumptionFullAssemblyCost_le_completed
    finiteContext (finiteExhaustionFormula partCount (&0)) targetFormula
      formulaCode hfiniteContextCard hfiniteContextBound
      (hfiniteExhaustion.trans hclosedLe)
      (hnegatedFiniteExhaustion.trans hclosedLe) htargetCode
  have hexhaustion :=
    finiteExhaustionAtEigenvariableStructuralPayloadBound_le_polynomial
      partCount syntaxCode hboundSyntax
  have hcase : caseResource <= caseBound := by
    dsimp only [caseResource, caseBound]
    exact
      compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope_le_fixed
        tokenCount partCount boundaryTable numericBound bitBound htokenCount
        hpartCount htableSize hnumericSize
  change contextualBranchesUnderBoundPayloadEnvelope ∅ partCount
      targetFormula caseResource <= _
  unfold boundaryRowContextualBranchesFixedPayloadPolynomial
  dsimp only [syntaxCode, formulaCode, caseBound, localBound]
  exact contextualBranchesUnderBoundPayloadEnvelope_le_components_completed ∅
    partCount targetFormula caseResource caseBound
    (cumulativeFiniteExhaustionPayloadPolynomial syntaxCode)
    (boundedUniversalFiniteExhaustionSpecializationEnvelope syntaxCode)
    localBound hcase hexhaustion hlower hweak heliminate hcut

def boundaryRowUniversalShellTermPolynomial
    (numericBound bitBound : Nat) : Nat :=
  6 * binaryNumeralTermCodeEnvelope bitBound +
    iteratedSuccessorTermCodePolynomial 0 numericBound +
    (binaryTermCode (&0 : ValuationTerm)).length +
    (binaryTermCode (#0 : ArithmeticSemiterm Nat 1)).length + 1

def boundaryRowUniversalShellRawFormulaPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let termCode := boundaryRowUniversalShellTermPolynomial numericBound bitBound
  let syntaxCode :=
    boundaryRowDirectUniversalSyntaxFixedPolynomial numericBound bitBound
  boundedUniversalClosedFormulaEnvelope syntaxCode +
    paFormulaCodeEnvelope termCode +
    (2 * termCode + finiteCaseLessThanFormulaCodeOverhead) +
    2 * boundaryRowUniversalBodyFormulaCodePolynomial numericBound bitBound + 1

def boundaryRowUniversalShellSourceFormulaPolynomial
    (numericBound bitBound : Nat) : Nat :=
  16 * boundaryRowUniversalShellRawFormulaPolynomial numericBound bitBound +
    128

def boundaryRowUniversalShellFormulaPolynomial
    (numericBound bitBound : Nat) : Nat :=
  64 * boundaryRowUniversalShellSourceFormulaPolynomial numericBound bitBound +
    64

def boundaryRowUniversalShellLocalPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (boundaryRowUniversalShellFormulaPolynomial numericBound bitBound)

def boundaryRowUniformDirectUniversalFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let termCode := boundaryRowUniversalShellTermPolynomial numericBound bitBound
  let formulaCode :=
    boundaryRowUniversalShellFormulaPolynomial numericBound bitBound
  let localBound :=
    boundaryRowUniversalShellLocalPayloadPolynomial numericBound bitBound
  boundaryRowContextualBranchesFixedPayloadPolynomial numericBound bitBound +
    closedShortBoundEqualityPayloadPolynomial numericBound +
    2 * paPrimitiveCostEnvelope termCode +
    arbitraryContextRelationTransportLocalEnvelope formulaCode termCode +
    12 * localBound

theorem
    compactAdditiveBoundaryTableRowsUniformDirectUniversalResource_le_fixed
    (tokenCount partCount boundaryTable numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (hpartCount : partCount <= numericBound)
    (htableSize : Nat.size boundaryTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveBoundaryTableRowsUniformDirectUniversalResource tokenCount
        partCount boundaryTable numericBound bitBound <=
      boundaryRowUniformDirectUniversalFixedPayloadPolynomial numericBound
        bitBound := by
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition := ∅
  let shiftedGamma := Gamma.image Rewriting.shift
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let boundTerm := Rew.bShift (shortBinaryNumeralTerm partCount)
  let bound := partCount
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
    closedShortBoundEqualityPayloadPolynomial partCount
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope ∅ partCount
    targetFormula
    (compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope
      tokenCount partCount boundaryTable numericBound bitBound)
  let termBound := boundaryRowUniversalShellTermPolynomial numericBound
    bitBound
  let rawFormulaBound :=
    boundaryRowUniversalShellRawFormulaPolynomial numericBound bitBound
  let sourceFormulaBound :=
    boundaryRowUniversalShellSourceFormulaPolynomial numericBound bitBound
  let formulaBound :=
    boundaryRowUniversalShellFormulaPolynomial numericBound bitBound
  let localBound :=
    boundaryRowUniversalShellLocalPayloadPolynomial numericBound bitBound
  let transportLocal := arbitraryContextRelationTransportLocalEnvelope
    formulaBound termBound
  have hGammaCard : Gamma.card <= 1 := by
    simp [Gamma]
  have hshiftedCard : shiftedGamma.card <= 1 := by
    exact Finset.card_image_le.trans hGammaCard
  have hbound : bound <= numericBound := by
    simpa only [bound] using hpartCount
  have hcountSize : Nat.size partCount <= bitBound :=
    (Nat.size_le_size hpartCount).trans hnumericSize
  have hshortCode :
      (binaryTermCode (shortBinaryNumeralTerm partCount)).length <=
        binaryNumeralTermCodeEnvelope bitBound :=
    binaryNumeralTerm_code_length_le_envelope partCount bitBound hcountSize
  have hrawSource : rawFormulaBound <= sourceFormulaBound := by
    dsimp only [rawFormulaBound, sourceFormulaBound]
    unfold boundaryRowUniversalShellSourceFormulaPolynomial
    omega
  have hsourceFormula : sourceFormulaBound <= formulaBound := by
    dsimp only [sourceFormulaBound, formulaBound]
    unfold boundaryRowUniversalShellFormulaPolynomial
    omega
  have hGammaSource : FormulaCodeBound Gamma sourceFormulaBound := by
    intro formula hformula
    simp [Gamma] at hformula
  have hshiftedFormula : FormulaCodeBound shiftedGamma formulaBound := by
    intro formula hformula
    simp [shiftedGamma, Gamma] at hformula
  have hboundTermShift := binaryTermCode_bShift_length_le_add_symbols
    (shortBinaryNumeralTerm partCount)
  have hshortSymbols := termSymbolCount_le_binaryTermCode_length
    (shortBinaryNumeralTerm partCount)
  have hboundTermRaw : (binaryTermCode boundTerm).length <=
      3 * (binaryTermCode (shortBinaryNumeralTerm partCount)).length := by
    dsimp only [boundTerm]
    omega
  have hboundTerm : (binaryTermCode boundTerm).length <= termBound := by
    dsimp only [termBound]
    unfold boundaryRowUniversalShellTermPolynomial
    omega
  have hfreeBoundRaw := binaryTermCode_free_length_le boundTerm
  have hfreeBound : (binaryTermCode freeBoundTerm).length <= termBound := by
    dsimp only [freeBoundTerm, termBound]
    unfold boundaryRowUniversalShellTermPolynomial
    omega
  have hcanonicalTermRaw :=
    iteratedSuccessorTerm_code_length_le_polynomial 0 bound
  have hcanonicalTermMono :=
    iteratedSuccessorTermCodePolynomial_mono 0 hbound
  have hcanonicalTerm : (binaryTermCode canonicalTerm).length <=
      termBound := by
    dsimp only [canonicalTerm, termBound]
    unfold boundaryRowUniversalShellTermPolynomial
    omega
  have hsubjectTerm : (binaryTermCode subjectTerm).length <= termBound := by
    dsimp only [subjectTerm, termBound]
    unfold boundaryRowUniversalShellTermPolynomial
    omega
  have hbodyFixed : (binaryFormulaCode body).length <=
      boundaryRowUniversalBodyFormulaCodePolynomial numericBound
        bitBound := by
    simpa only [body] using
      compactAdditiveBoundaryTableRowBody_code_length_le_fixed tokenCount
        boundaryTable numericBound bitBound htokenCount htableSize
        hnumericSize
  have hbody : (binaryFormulaCode body).length <= rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold boundaryRowUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have htargetFree := binaryFormulaCode_free_length_le body
  have htargetTight : (binaryFormulaCode targetFormula).length <=
      2 * (binaryFormulaCode body).length := by
    simpa only [targetFormula] using htargetFree
  have htarget : (binaryFormulaCode targetFormula).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold boundaryRowUniversalShellRawFormulaPolynomial
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
    unfold boundaryRowUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have hsyntaxBound : bound <=
      boundaryRowDirectUniversalSyntaxFixedPolynomial numericBound
        bitBound := by
    dsimp only [bound]
    unfold boundaryRowDirectUniversalSyntaxFixedPolynomial
    omega
  have hcanonicalBoundRaw := finiteBoundFormula_code_le_boundedUniversal bound
    (boundaryRowDirectUniversalSyntaxFixedPolynomial numericBound bitBound)
      hsyntaxBound
  have hcanonicalBoundTight : (binaryFormulaCode canonicalBound).length <=
      boundedUniversalClosedFormulaEnvelope
        (boundaryRowDirectUniversalSyntaxFixedPolynomial numericBound
          bitBound) := by
    simpa only [canonicalBound] using hcanonicalBoundRaw
  have hcanonicalBound : (binaryFormulaCode canonicalBound).length <=
      rawFormulaBound := by
    dsimp only [rawFormulaBound]
    unfold boundaryRowUniversalShellRawFormulaPolynomial
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
    unfold boundaryRowUniversalShellRawFormulaPolynomial
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
    unfold boundaryRowUniversalShellRawFormulaPolynomial
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
    unfold boundaryRowUniversalShellRawFormulaPolynomial
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
      unfold boundaryRowUniversalShellSourceFormulaPolynomial
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
      (hformula : (binaryFormulaCode formula).length <= sourceFormulaBound) =>
    by
      have hraw := binaryFormulaCode_neg_length_le formula
      have : (binaryFormulaCode (∼formula)).length <= formulaBound := by
        dsimp only [formulaBound]
        unfold boundaryRowUniversalShellFormulaPolynomial
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
    unfold boundaryRowUniversalShellRawFormulaPolynomial
    have hzeroTerm :
        (binaryTermCode
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
            termBound := by
      have hzeroCode :
          (binaryTermCode
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
              (binaryTermCode (&0 : ValuationTerm)).length := by decide
      dsimp only [termBound]
      unfold boundaryRowUniversalShellTermPolynomial
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
    unfold boundaryRowUniversalShellSourceFormulaPolynomial
    omega
  have huniversalFormulaRaw := binaryFormulaCode_all_length_le universalBody
  have huniversalFormula :
      (binaryFormulaCode
        (∀⁰ universalBody : LO.FirstOrder.ArithmeticProposition)).length <=
          sourceFormulaBound := by
    dsimp only [sourceFormulaBound]
    unfold boundaryRowUniversalShellSourceFormulaPolynomial
    omega
  have hfreeUniversalBodyRaw := binaryFormulaCode_free_length_le universalBody
  have hfreeUniversalBody :
      (binaryFormulaCode (Rewriting.free universalBody)).length <=
        formulaBound := by
    dsimp only [formulaBound]
    unfold boundaryRowUniversalShellFormulaPolynomial
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
      exact hshiftedFormula.insert hnegatedOriginalBound
  have horiginalContextCard : originalContext.card <= 4 := by
    have hstep := Finset.card_insert_le (∼originalBound) shiftedGamma
    dsimp only [originalContext]
    omega
  have hboundEquality : boundEqualityResource <=
      closedShortBoundEqualityPayloadPolynomial numericBound := by
    dsimp only [boundEqualityResource]
    exact closedShortBoundEqualityPayloadPolynomial_mono_completed hpartCount
  have hbranches : branchResource <=
      boundaryRowContextualBranchesFixedPayloadPolynomial numericBound
        bitBound := by
    dsimp only [branchResource, targetFormula]
    exact boundaryRowContextualBranchesResource_le_fixed tokenCount partCount
      boundaryTable numericBound bitBound htokenCount hpartCount htableSize
        hnumericSize
  have hcanonicalDischarge :=
    contextualDischargeFullAssemblyCost_le_openIndexUniversalShell
      shiftedGamma canonicalBound targetFormula formulaBound (by omega)
        hshiftedFormula htargetFormula hcanonicalImplicationFormula
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
    hshiftedFormula.insert hsymmetryImplicationFormula
  have hsymmetryInsertCard :
      (insert symmetryImplication shiftedGamma).card <= 8 := by
    have hstep := Finset.card_insert_le symmetryImplication shiftedGamma
    omega
  have hweakSymmetry := weakeningFullAssemblyCost_le_small
    (insert symmetryImplication shiftedGamma) formulaBound
      hsymmetryInsertCard hsymmetryInsertBound
  have hmpSymmetry := contextualModusPonensFullAssemblyCost_le_small
    shiftedGamma forwardEquality backwardEquality formulaBound (by omega)
      hshiftedFormula hforwardEqualityFormula hbackwardEqualityFormula
        hsymmetryImplicationFormula hnegatedSymmetryImplication
          hnegatedBackward
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
      hcanonicalImplicationFormula hnegatedCanonicalImplication
      hnegatedTarget
  have horiginalDischarge :=
    contextualDischargeFullAssemblyCost_le_openIndexUniversalShell
      shiftedGamma originalBound targetFormula formulaBound (by omega)
      hshiftedFormula htargetFormula horiginalTargetImplicationFormula
      hnegatedOriginalBound
  have hshiftSource : 2 * sourceFormulaBound <= formulaBound := by
    dsimp only [formulaBound]
    unfold boundaryRowUniversalShellFormulaPolynomial
    omega
  have huniversalIntroduction :=
    contextualUniversalIntroductionFullAssemblyCost_le_openIndexUniversalShell
      Gamma universalBody sourceFormulaBound formulaBound (by omega)
      hGammaSource (huniversalBody.trans hformulaPositive)
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
    boundaryRowContextualBranchesFixedPayloadPolynomial numericBound
        bitBound +
      closedShortBoundEqualityPayloadPolynomial numericBound +
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
  compactAdditiveBoundaryTableRowDirectTerminal_code_length_le_fixed
#print axioms
  compactAdditiveBoundaryTableRowUniformBranchDirectPayloadEnvelope_le_fixed
#print axioms compactAdditiveBoundaryTableRowTerminal_code_length_le_fixed
#print axioms compactAdditiveBoundaryTableRowBody_code_length_le_fixed
#print axioms
  compactAdditiveBoundaryTableRowsUniformDirectBranchesStructuralEnvelope_le_fixed
#print axioms boundaryRowContextualBranchesResource_le_fixed
#print axioms
  compactAdditiveBoundaryTableRowsUniformDirectUniversalResource_le_fixed

end FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectFixedPolynomialBounds
