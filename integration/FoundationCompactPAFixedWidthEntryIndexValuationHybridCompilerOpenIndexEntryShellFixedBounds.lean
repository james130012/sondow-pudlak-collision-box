import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellFixedBounds
import integration.FoundationCompactSyntaxUniformRewritingCodeBounds

/-!
# Complete fixed bound for the open-index fixed-width entry shell

This layer charges the three outer conjunctions and the existential witness
introduction after the atomic guards and bounded universal have already been
closed.  Its final endpoint depends only on the common open-index scale.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPABinaryLengthValuationContextCompilerFixedPolynomialBounds
open FoundationCompactPABoundedUniversalPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexScalarBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniversalShellSyntaxFixedBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds

def fixedWidthOpenIndexEntryTermCodePolynomial (scale : Nat) : Nat :=
  fixedWidthOpenIndexUniversalShellTermPolynomial scale +
    fixedWidthOpenIndexTopAtomicTermCodePolynomial scale +
    binaryNumeralTermCodeEnvelope scale + 8 * scale +
    (binaryTermCode
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length +
    (binaryTermCode paOneTerm).length +
    binaryFunctionTermCodeOverhead Language.Add.add + 16

def fixedWidthOpenIndexEntryLengthFormulaPolynomial
    (termBound : Nat) : Nat :=
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
    Rewriting.emb (ξ := Nat) lengthDef.val
  let sourceCode := (binaryFormulaCode source).length
  uniformRewritingFormulaFactor (termBound + 4) (termBound + 1) sourceCode *
    sourceCode

def fixedWidthOpenIndexEntryLiftedUniversalFormulaPolynomial
    (scale : Nat) : Nat :=
  let sourceCode :=
    fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial scale
  uniformRewritingFormulaFactor 4 1 sourceCode * sourceCode

def fixedWidthOpenIndexEntryRelationFormulaPolynomial
    (termBound : Nat) : Nat :=
  16 * termBound +
    8 * ((binaryNatCode 0).length + (binaryNatCode 2).length +
      (binaryNatCode 4).length + (binaryNatCode 5).length +
      (binaryNatCode (Encodable.encode
        (Language.Eq.eq : LO.FirstOrder.Language.Rel ℒₒᵣ 2))).length +
      (binaryNatCode (Encodable.encode
        (Language.LT.lt : LO.FirstOrder.Language.Rel ℒₒᵣ 2))).length +
      binaryFunctionTermCodeOverhead Language.Add.add + 1) + 128

def fixedWidthOpenIndexEntryContextFormulaPolynomial
    (scale : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 scale
    (binaryTermCode (&0 : ValuationTerm)).length

def fixedWidthOpenIndexEntryFormulaSeed (scale : Nat) : Nat :=
  let termBound := fixedWidthOpenIndexEntryTermCodePolynomial scale
  let atomicBound := fixedWidthOpenIndexTopAtomicFormulaCodePolynomial scale
    termBound
  let lengthBound :=
    fixedWidthOpenIndexEntryLengthFormulaPolynomial termBound
  let universalBound :=
    fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial scale
  let liftedUniversalBound :=
    fixedWidthOpenIndexEntryLiftedUniversalFormulaPolynomial scale
  let relationBound :=
    fixedWidthOpenIndexEntryRelationFormulaPolynomial termBound
  let contextBound := fixedWidthOpenIndexEntryContextFormulaPolynomial scale
  atomicBound + lengthBound + universalBound + liftedUniversalBound +
    relationBound + contextBound + termBound + 1

def fixedWidthOpenIndexEntryFormulaPolynomial (scale : Nat) : Nat :=
  128 * fixedWidthOpenIndexEntryFormulaSeed scale + 256

def fixedWidthOpenIndexEntryLocalPayloadPolynomial (scale : Nat) : Nat :=
  smallContextAssemblyEnvelope
    (fixedWidthOpenIndexEntryFormulaPolynomial scale)

def compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (scale : Nat) : Nat :=
  let termBound := fixedWidthOpenIndexEntryTermCodePolynomial scale
  let localBound := fixedWidthOpenIndexEntryLocalPayloadPolynomial scale
  compilePositiveRelationFixedPayloadPolynomial scale termBound +
    compileBinaryLengthAtValuationFixedPayloadPolynomial scale termBound +
    fixedWidthOpenIndexSizeGuardFixedPayloadPolynomial scale termBound +
    fixedWidthOpenIndexUniversalFullyFixedPayloadPolynomial scale +
    11 * localBound

private theorem atomicScale_zero_le_entryScale
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale) :
    valuation 0 <= scale := by
  have hraw : valuation 0 <=
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm := by
    unfold fixedWidthOpenIndexAtomicCoordinateScale
      fixedWidthOpenIndexPublicCoordinateScale
    omega
  exact hraw.trans hscale

private theorem inputTermCode_le_entryTermCode
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm candidate : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (hcandidate :
      (binaryTermCode candidate).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm) :
    (binaryTermCode candidate).length <=
      fixedWidthOpenIndexEntryTermCodePolynomial scale := by
  have hcode := hcandidate.trans hscale
  unfold fixedWidthOpenIndexEntryTermCodePolynomial
  omega

private theorem bShiftInputTermCode_le_entryTermCode
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm candidate : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale)
    (hcandidate :
      (binaryTermCode candidate).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm) :
    (binaryTermCode (Rew.bShift candidate)).length <=
      fixedWidthOpenIndexEntryTermCodePolynomial scale := by
  have hcode := hcandidate.trans hscale
  have hshift := binaryTermCode_bShift_length_le_add_symbols candidate
  have hsymbols := termSymbolCount_le_binaryTermCode_length candidate
  unfold fixedWidthOpenIndexEntryTermCodePolynomial
  omega

private theorem shortSizeTermCode_le_entryTermCode
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale) :
    (binaryTermCode
      (shortBinaryNumeralTerm
        (Nat.size (termValue valuation valueTerm)))).length <=
      fixedWidthOpenIndexEntryTermCodePolynomial scale := by
  let size := Nat.size (termValue valuation valueTerm)
  have hsize : size <= scale := by
    have hraw : size <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      dsimp only [size]
      unfold fixedWidthOpenIndexAtomicCoordinateScale
        fixedWidthOpenIndexPublicCoordinateScale
      omega
    exact hraw.trans hscale
  have hsizeWidth : Nat.size size <= scale :=
    (natSize_le_self_uniform size).trans hsize
  have hcode := binaryNumeralTerm_code_length_le_envelope size scale hsizeWidth
  dsimp only [size] at hcode
  unfold fixedWidthOpenIndexEntryTermCodePolynomial
  omega

private theorem boundVariableCode_le_entryTermCode (scale : Nat) :
    (binaryTermCode
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
      fixedWidthOpenIndexEntryTermCodePolynomial scale := by
  unfold fixedWidthOpenIndexEntryTermCodePolynomial
  omega

private theorem embeddedLengthFormula_code_le_entry
    {arity : Nat}
    (sizeTerm valueTerm : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (termBound : Nat)
    (hsize : (binaryTermCode sizeTerm).length <= termBound)
    (hvalue : (binaryTermCode valueTerm).length <= termBound) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) lengthDef.val) ⇜
        ![sizeTerm, valueTerm])).length <=
      fixedWidthOpenIndexEntryLengthFormulaPolynomial termBound := by
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
    Rewriting.emb (ξ := Nat) lengthDef.val
  let terms : Fin 2 -> LO.FirstOrder.ArithmeticSemiterm Nat arity :=
    ![sizeTerm, valueTerm]
  let sourceCode := (binaryFormulaCode source).length
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termBound := by
    intro coordinate
    cases coordinate using Fin.cases with
    | zero => simpa [terms] using hsize
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => simpa [terms] using hvalue
        | succ coordinate => exact Fin.elim0 coordinate
  have himage : RewritingImageCodeBound (Rew.subst terms) termBound := by
    constructor
    · intro coordinate
      simpa only [Rew.subst_bvar] using hterms coordinate
    · intro index
      simp
  have huniform := UniformRewritingImageBound.ofCodeBound himage
  have hrewrite := binaryFormulaCode_rewriting_length_le_factor source
    (Rew.subst terms) (by omega) (by omega) huniform
  have hsymbols := formulaSymbolCount_le_binaryFormulaCode_length source
  have hfactor :
      uniformRewritingFormulaFactor (termBound + 4) (termBound + 1)
          (formulaSymbolCount source) <=
        uniformRewritingFormulaFactor (termBound + 4) (termBound + 1)
          sourceCode := by
    dsimp only [sourceCode]
    unfold uniformRewritingFormulaFactor
    nlinarith
  have hproduct :
      uniformRewritingFormulaFactor (termBound + 4) (termBound + 1)
          (formulaSymbolCount source) * sourceCode <=
        uniformRewritingFormulaFactor (termBound + 4) (termBound + 1)
          sourceCode * sourceCode :=
    Nat.mul_le_mul_right sourceCode hfactor
  have hfinal := hrewrite.trans (by
    simpa only [sourceCode] using hproduct)
  simpa only [source, terms, sourceCode,
    fixedWidthOpenIndexEntryLengthFormulaPolynomial] using hfinal

private theorem binaryAddTerm_code_length_le_entry
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryTermCode
      (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        binaryFunctionTermCodeOverhead Language.Add.add := by
  simp [Matrix.fun_eq_vec_two, binaryTermCode,
    binaryFunctionTermCodeOverhead]
  omega

private theorem binaryAddTerm_freeVariables_entry
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem paAddTerm_freeVariables_entry
    (left right : ValuationTerm) :
    (paAddTerm left right).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
  exact binaryAddTerm_freeVariables_entry left right

private theorem binaryRelationFormula_code_length_le_entry
    {arity : Nat}
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right])).length <=
      (binaryTermCode left).length + (binaryTermCode right).length +
        (binaryNatCode 0).length + (binaryNatCode 2).length +
        (binaryNatCode (Encodable.encode relationSymbol)).length := by
  simp [Matrix.fun_eq_vec_two, binaryFormulaCode]
  omega

private theorem binaryRelationFormula_freeVariables_entry
    {arity : Nat}
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (LO.FirstOrder.Semiformula.rel relationSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem binaryAndSemiformula_code_length_le_entry
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode (left ⋏ right)).length <=
      (binaryFormulaCode left).length +
        (binaryFormulaCode right).length + 8 := by
  have htag : (binaryNatCode 4).length <= 8 := by decide
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem lessThanSemiformula_code_le_entryRelation
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (binaryFormulaCode
      (“!!left < !!right” :
        LO.FirstOrder.ArithmeticSemiformula Nat arity)).length <=
      fixedWidthOpenIndexEntryRelationFormulaPolynomial termBound := by
  have hraw := binaryRelationFormula_code_length_le_entry
    Language.LT.lt left right
  change
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![left, right])).length <= _
  unfold fixedWidthOpenIndexEntryRelationFormulaPolynomial
  omega

private theorem lessOrEqualSemiformula_code_le_entryRelation
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (termBound : Nat)
    (hleft : (binaryTermCode left).length <= termBound)
    (hright : (binaryTermCode right).length <= termBound) :
    (binaryFormulaCode
      (“!!left ≤ !!right” :
        LO.FirstOrder.ArithmeticSemiformula Nat arity)).length <=
      fixedWidthOpenIndexEntryRelationFormulaPolynomial termBound := by
  rw [LO.FirstOrder.Semiformula.Operator.le_def]
  let equalityFormula : LO.FirstOrder.ArithmeticSemiformula Nat arity :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq ![left, right]
  let strictFormula : LO.FirstOrder.ArithmeticSemiformula Nat arity :=
    LO.FirstOrder.Semiformula.rel Language.LT.lt ![left, right]
  have hequality := binaryRelationFormula_code_length_le_entry
    Language.Eq.eq left right
  have hstrict := binaryRelationFormula_code_length_le_entry
    Language.LT.lt left right
  have hor :
      (binaryFormulaCode (equalityFormula ⋎ strictFormula)).length <=
        (binaryFormulaCode equalityFormula).length +
          (binaryFormulaCode strictFormula).length + 8 := by
    have htag : (binaryNatCode 5).length <= 8 := by decide
    simp only [binaryFormulaCode, List.length_append]
    omega
  dsimp only [equalityFormula, strictFormula] at hequality hstrict hor ⊢
  unfold fixedWidthOpenIndexEntryRelationFormulaPolynomial
  omega

private theorem fixedWidthUniversalFormula_code_le_entryUniversalSource
    (valuation : Nat -> Nat)
    (tableTerm widthTerm indexTerm valueTerm : ValuationTerm)
    (scale : Nat)
    (hscale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm <= scale) :
    (binaryFormulaCode
      (fixedWidthUniversalFormula tableTerm widthTerm indexTerm
        valueTerm)).length <=
      fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial scale := by
  let body := fixedWidthBitBody tableTerm widthTerm indexTerm valueTerm
  let boundTerm := Rew.bShift widthTerm
  let universalBody := termBoundedUniversalBody boundTerm body
  let termBound := fixedWidthOpenIndexUniversalShellTermPolynomial scale
  let rawFormulaBound :=
    fixedWidthOpenIndexUniversalShellRawFormulaPolynomial scale
  let sourceFormulaBound :=
    fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial scale
  have hwidthCode : (binaryTermCode widthTerm).length <= scale := by
    have hraw : (binaryTermCode widthTerm).length <=
        fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm valueTerm := by
      unfold fixedWidthOpenIndexAtomicCoordinateScale
      omega
    exact hraw.trans hscale
  have hboundTermShift := binaryTermCode_bShift_length_le_add_symbols widthTerm
  have hwidthSymbols := termSymbolCount_le_binaryTermCode_length widthTerm
  have hboundTerm : (binaryTermCode boundTerm).length <= termBound := by
    dsimp only [boundTerm, termBound]
    unfold fixedWidthOpenIndexUniversalShellTermPolynomial
    omega
  have hbodyRaw := fixedWidthBitBody_code_le_fixed valuation tableTerm widthTerm
    indexTerm valueTerm scale hscale
  have hbody : (binaryFormulaCode body).length <= rawFormulaBound := by
    dsimp only [body, rawFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
    dsimp only
    omega
  have htermFormulaRaw := finiteCaseLessThanFormula_code_length_le
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) boundTerm
  have hzeroTerm :
      (binaryTermCode
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <= termBound := by
    have hzeroCode :
        (binaryTermCode
          (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <=
          (binaryTermCode (&0 : ValuationTerm)).length := by decide
    dsimp only [termBound]
    unfold fixedWidthOpenIndexUniversalShellTermPolynomial
    omega
  have htermFormula :
      (binaryFormulaCode (termBoundFormula boundTerm)).length <=
        rawFormulaBound := by
    have htight :
        (binaryFormulaCode (termBoundFormula boundTerm)).length <=
          (binaryTermCode
            (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length +
            (binaryTermCode boundTerm).length +
              finiteCaseLessThanFormulaCodeOverhead := by
      simpa only [termBoundFormula] using htermFormulaRaw
    calc
      _ <= 2 * termBound + finiteCaseLessThanFormulaCodeOverhead := by omega
      _ <= rawFormulaBound := by
        dsimp only [rawFormulaBound, termBound]
        unfold fixedWidthOpenIndexUniversalShellRawFormulaPolynomial
        dsimp only
        omega
  have huniversalBodyRaw := binarySemiformulaCode_implication_length_le
    (termBoundFormula boundTerm) body
  have htagFive : (binaryNatCode 5).length <= 64 := by decide
  have huniversalBodyWithTag :
      (binaryFormulaCode universalBody).length + 8 <=
        sourceFormulaBound := by
    have htight : (binaryFormulaCode universalBody).length <=
        2 * (binaryFormulaCode (termBoundFormula boundTerm)).length +
          (binaryFormulaCode body).length + (binaryNatCode 5).length := by
      simpa only [universalBody, termBoundedUniversalBody] using
        huniversalBodyRaw
    dsimp only [sourceFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial
    omega
  have hall := binaryFormulaCode_all_length_le universalBody
  have hsourceRaw : rawFormulaBound <= sourceFormulaBound := by
    dsimp only [rawFormulaBound, sourceFormulaBound]
    unfold fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial
    omega
  unfold fixedWidthUniversalFormula
  change
    (binaryFormulaCode
      (∀⁰ universalBody : LO.FirstOrder.ArithmeticProposition)).length <=
      sourceFormulaBound
  exact hall.trans huniversalBodyWithTag

private theorem bShiftFormula_code_le_entryLiftedUniversal
    (formula : ValuationFormula) (scale : Nat)
    (hformula : (binaryFormulaCode formula).length <=
      fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial scale) :
    (binaryFormulaCode (Rew.bShift ▹ formula)).length <=
      fixedWidthOpenIndexEntryLiftedUniversalFormulaPolynomial scale := by
  have hbshift : UniformRewritingImageBound
      (Rew.bShift : Rew ℒₒᵣ Nat 0 Nat 1) 4 1 := by
    constructor
    · intro coordinate
      exact Fin.elim0 coordinate
    constructor
    · intro coordinate
      exact Fin.elim0 coordinate
    · intro index
      simp
  have hrewrite := binaryFormulaCode_rewriting_length_le_factor formula
    (Rew.bShift : Rew ℒₒᵣ Nat 0 Nat 1) (by omega) (by omega) hbshift
  have hsymbols := formulaSymbolCount_le_binaryFormulaCode_length formula
  let sourceCode :=
    fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial scale
  have hfactor : uniformRewritingFormulaFactor 4 1
      (formulaSymbolCount formula) <=
      uniformRewritingFormulaFactor 4 1 sourceCode := by
    dsimp only [sourceCode]
    unfold uniformRewritingFormulaFactor
    omega
  have hproduct := Nat.mul_le_mul hfactor hformula
  exact hrewrite.trans (by
    dsimp only [sourceCode] at hproduct
    simpa only [fixedWidthOpenIndexEntryLiftedUniversalFormulaPolynomial]
      using hproduct)

private theorem valuationContextFormulaCodeBound_of_subset_singleton_entry
    (variableSet : Finset Nat) (valuation : Nat -> Nat) (scale : Nat)
    (hvariables : variableSet ⊆ {0}) (hzero : valuation 0 <= scale) :
    FormulaCodeBound (valuationContext variableSet valuation)
      (fixedWidthOpenIndexEntryFormulaPolynomial scale) := by
  have hcard : variableSet.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall candidate, candidate ∈ variableSet ->
      valuation candidate <= scale := by
    intro candidate hcandidate
    have hsingle := hvariables hcandidate
    simp only [Finset.mem_singleton] at hsingle
    subst candidate
    exact hzero
  have htermCodes : forall candidate, candidate ∈ variableSet ->
      (binaryTermCode (&candidate : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro candidate hcandidate
    have hsingle := hvariables hcandidate
    simp only [Finset.mem_singleton] at hsingle
    subst candidate
    exact le_rfl
  have hsum := valuationContext_formulaCodeSum_le_uniform variableSet valuation
    1 scale (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues
      htermCodes
  intro formula hformula
  have hmember :=
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCode_le_formulaCodeSum
      hformula
  have hcontext :
      fixedWidthOpenIndexEntryContextFormulaPolynomial scale <=
        fixedWidthOpenIndexEntryFormulaSeed scale := by
    unfold fixedWidthOpenIndexEntryFormulaSeed
      fixedWidthOpenIndexEntryContextFormulaPolynomial
    dsimp only
    omega
  have hseed : fixedWidthOpenIndexEntryFormulaSeed scale <=
      fixedWidthOpenIndexEntryFormulaPolynomial scale := by
    unfold fixedWidthOpenIndexEntryFormulaPolynomial
    omega
  exact hmember.trans (hsum.trans (hcontext.trans hseed))

private theorem valuationContextCard_le_one_of_subset_singleton_entry
    (variableSet : Finset Nat) (valuation : Nat -> Nat)
    (hvariables : variableSet ⊆ {0}) :
    (valuationContext variableSet valuation).card <= 1 := by
  have hsource : variableSet.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have himage : (valuationContext variableSet valuation).card <=
      variableSet.card := by
    unfold valuationContext
    exact Finset.card_image_le
  exact himage.trans hsource

private theorem conjunctionShellCosts_le_entryLocal
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (scale : Nat)
    (hvariables : (left ⋏ right).freeVariables ⊆ {0})
    (hzero : valuation 0 <= scale)
    (hleft : (binaryFormulaCode left).length <=
      fixedWidthOpenIndexEntryFormulaPolynomial scale)
    (hright : (binaryFormulaCode right).length <=
      fixedWidthOpenIndexEntryFormulaPolynomial scale)
    (hconjunction : (binaryFormulaCode (left ⋏ right)).length <=
      fixedWidthOpenIndexEntryFormulaPolynomial scale) :
    let Gamma := valuationContext (left ⋏ right).freeVariables valuation
    weakeningFullAssemblyCost (insert left Gamma) <=
        fixedWidthOpenIndexEntryLocalPayloadPolynomial scale ∧
      weakeningFullAssemblyCost (insert right Gamma) <=
        fixedWidthOpenIndexEntryLocalPayloadPolynomial scale ∧
      conjunctionFullAssemblyCost Gamma left right <=
        fixedWidthOpenIndexEntryLocalPayloadPolynomial scale := by
  let Gamma := valuationContext (left ⋏ right).freeVariables valuation
  let formulaBound := fixedWidthOpenIndexEntryFormulaPolynomial scale
  have hGamma := valuationContextFormulaCodeBound_of_subset_singleton_entry
    (left ⋏ right).freeVariables valuation scale hvariables hzero
  have hGammaCard :=
    valuationContextCard_le_one_of_subset_singleton_entry
      (left ⋏ right).freeVariables valuation hvariables
  have hGammaCardLocal : Gamma.card <= 1 := by
    simpa only [Gamma] using hGammaCard
  have hleftInsert : FormulaCodeBound (insert left Gamma) formulaBound :=
    hGamma.insert hleft
  have hrightInsert : FormulaCodeBound (insert right Gamma) formulaBound :=
    hGamma.insert hright
  have hleftCard : (insert left Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le left Gamma
    omega
  have hrightCard : (insert right Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le right Gamma
    omega
  have hweakLeft := weakeningFullAssemblyCost_le_small
    (insert left Gamma) formulaBound hleftCard hleftInsert
  have hweakRight := weakeningFullAssemblyCost_le_small
    (insert right Gamma) formulaBound hrightCard hrightInsert
  have hconj := conjunctionFullAssemblyCost_le_small Gamma left right
    formulaBound (by omega) hGamma hleft hright hconjunction
  simpa only [Gamma, formulaBound,
    fixedWidthOpenIndexEntryLocalPayloadPolynomial] using
      And.intro hweakLeft (And.intro hweakRight hconj)

private theorem existsShellCosts_le_entryLocal
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (scale : Nat)
    (hvariables :
      (∃⁰ body : ValuationFormula).freeVariables ⊆ {0})
    (hzero : valuation 0 <= scale)
    (hbody : (binaryFormulaCode body).length <=
      fixedWidthOpenIndexEntryFormulaPolynomial scale)
    (hwitness : (binaryTermCode witness).length <=
      fixedWidthOpenIndexEntryFormulaPolynomial scale)
    (hinstance : (binaryFormulaCode (body/[witness])).length <=
      fixedWidthOpenIndexEntryFormulaPolynomial scale)
    (hexistential :
      (binaryFormulaCode (∃⁰ body : ValuationFormula)).length <=
        fixedWidthOpenIndexEntryFormulaPolynomial scale) :
    let Gamma := valuationContext
      (∃⁰ body : ValuationFormula).freeVariables valuation
    weakeningFullAssemblyCost (insert (body/[witness]) Gamma) <=
        fixedWidthOpenIndexEntryLocalPayloadPolynomial scale ∧
      existsIntroFullAssemblyCost Gamma body witness <=
        fixedWidthOpenIndexEntryLocalPayloadPolynomial scale := by
  let Gamma := valuationContext
    (∃⁰ body : ValuationFormula).freeVariables valuation
  let formulaBound := fixedWidthOpenIndexEntryFormulaPolynomial scale
  have hGamma := valuationContextFormulaCodeBound_of_subset_singleton_entry
    (∃⁰ body : ValuationFormula).freeVariables valuation scale hvariables
      hzero
  have hGammaCard :=
    valuationContextCard_le_one_of_subset_singleton_entry
      (∃⁰ body : ValuationFormula).freeVariables valuation hvariables
  have hGammaCardLocal : Gamma.card <= 1 := by
    simpa only [Gamma] using hGammaCard
  have hinsert : FormulaCodeBound (insert (body/[witness]) Gamma)
      formulaBound := hGamma.insert hinstance
  have hinsertCard : (insert (body/[witness]) Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le (body/[witness]) Gamma
    omega
  have hweak := weakeningFullAssemblyCost_le_small
    (insert (body/[witness]) Gamma) formulaBound hinsertCard hinsert
  have hexists := existsIntroFullAssemblyCost_le_small Gamma body witness
    formulaBound (by omega) hGamma hbody hwitness hinstance hexistential
  simpa only [Gamma, formulaBound,
    fixedWidthOpenIndexEntryLocalPayloadPolynomial] using
      And.intro hweak hexists

theorem
    compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial_le_fullyFixed
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
    compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm <=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        scale := by
  let size := Nat.size (termValue valuation valueTerm)
  let sizeTerm : ValuationTerm := shortBinaryNumeralTerm size
  let guardFormula := fixedWidthWitnessGuard size valueTerm
  let lengthFormula := fixedWidthLengthFormula size valueTerm
  let sizeGuardFormula := fixedWidthSizeGuard size widthTerm
  let universalFormula := fixedWidthUniversalFormula tableTerm widthTerm
    indexTerm valueTerm
  let innerFormula := sizeGuardFormula ⋏ universalFormula
  let middleFormula := lengthFormula ⋏ innerFormula
  let postFormula := guardFormula ⋏ middleFormula
  let body := compactFixedWidthEntryAtValuationWitnessBody tableTerm widthTerm
    indexTerm valueTerm
  let witness := shortBinaryNumeralTerm size
  let existentialFormula := (∃⁰ body : ValuationFormula)
  let termBound := fixedWidthOpenIndexEntryTermCodePolynomial scale
  let formulaSeed := fixedWidthOpenIndexEntryFormulaSeed scale
  let formulaBound := fixedWidthOpenIndexEntryFormulaPolynomial scale
  let localBound := fixedWidthOpenIndexEntryLocalPayloadPolynomial scale
  let relationBound :=
    fixedWidthOpenIndexEntryRelationFormulaPolynomial termBound
  let lengthBound := fixedWidthOpenIndexEntryLengthFormulaPolynomial termBound
  let universalBound :=
    fixedWidthOpenIndexUniversalShellSourceFormulaPolynomial scale
  let liftedUniversalBound :=
    fixedWidthOpenIndexEntryLiftedUniversalFormulaPolynomial scale
  have hzero := atomicScale_zero_le_entryScale valuation tableTerm widthTerm
    indexTerm valueTerm scale hscale
  have hvalueCoordinate : (binaryTermCode valueTerm).length <=
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm := by
    unfold fixedWidthOpenIndexAtomicCoordinateScale
    omega
  have hwidthCoordinate : (binaryTermCode widthTerm).length <=
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
        indexTerm valueTerm := by
    unfold fixedWidthOpenIndexAtomicCoordinateScale
    omega
  have hvalueCode : (binaryTermCode valueTerm).length <= termBound := by
    simpa only [termBound] using
      (inputTermCode_le_entryTermCode valuation tableTerm widthTerm indexTerm
        valueTerm valueTerm scale hscale hvalueCoordinate)
  have hwidthCode : (binaryTermCode widthTerm).length <= termBound := by
    simpa only [termBound] using
      (inputTermCode_le_entryTermCode valuation tableTerm widthTerm indexTerm
        valueTerm widthTerm scale hscale hwidthCoordinate)
  have hvalueScale : (binaryTermCode valueTerm).length <= scale :=
    hvalueCoordinate.trans hscale
  have hshiftedValueScale :
      (binaryTermCode (Rew.bShift valueTerm)).length <= 3 * scale := by
    have hshift := binaryTermCode_bShift_length_le_add_symbols valueTerm
    have hsymbols := termSymbolCount_le_binaryTermCode_length valueTerm
    omega
  have hshiftedValueCode :
      (binaryTermCode (Rew.bShift valueTerm)).length <= termBound := by
    simpa only [termBound] using
      (bShiftInputTermCode_le_entryTermCode valuation tableTerm widthTerm
        indexTerm valueTerm valueTerm scale hscale hvalueCoordinate)
  have hshiftedWidthCode :
      (binaryTermCode (Rew.bShift widthTerm)).length <= termBound := by
    simpa only [termBound] using
      (bShiftInputTermCode_le_entryTermCode valuation tableTerm widthTerm
        indexTerm valueTerm widthTerm scale hscale hwidthCoordinate)
  have hsizeTermCode : (binaryTermCode sizeTerm).length <= termBound := by
    simpa only [sizeTerm, size, termBound] using
      (shortSizeTermCode_le_entryTermCode valuation tableTerm widthTerm
        indexTerm valueTerm scale hscale)
  have hboundVariableCode :
      (binaryTermCode
        (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1)).length <= termBound := by
    simpa only [termBound] using boundVariableCode_le_entryTermCode scale
  have honeCode : (binaryTermCode paOneTerm).length <= termBound := by
    dsimp only [termBound]
    unfold fixedWidthOpenIndexEntryTermCodePolynomial
    omega
  let postSuccessor := paAddTerm valueTerm paOneTerm
  have hpostSuccessorRaw := paAddTerm_code_length_le valueTerm paOneTerm
  have hpostSuccessorCode :
      (binaryTermCode postSuccessor).length <= termBound := by
    dsimp only [postSuccessor]
    exact hpostSuccessorRaw.trans (by
      dsimp only [termBound]
      unfold fixedWidthOpenIndexEntryTermCodePolynomial
      omega)
  let bodyOne : LO.FirstOrder.ArithmeticSemiterm Nat 1 := ‘1’
  have hbodyOneCompare : (binaryTermCode bodyOne).length <=
      (binaryTermCode paOneTerm).length := by decide
  have hbodyOneCode : (binaryTermCode bodyOne).length <= termBound :=
    hbodyOneCompare.trans honeCode
  let bodySuccessor : LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
    ‘!!(Rew.bShift valueTerm) + 1’
  have hbodySuccessorRaw := binaryAddTerm_code_length_le_entry
    (Rew.bShift valueTerm) bodyOne
  have hbodySuccessorCode :
      (binaryTermCode bodySuccessor).length <= termBound := by
    change
      (binaryTermCode
        (LO.FirstOrder.Semiterm.func Language.Add.add
          ![Rew.bShift valueTerm, bodyOne])).length <= termBound
    exact hbodySuccessorRaw.trans (by
      dsimp only [termBound]
      unfold fixedWidthOpenIndexEntryTermCodePolynomial
      omega)
  have htermBoundSeed : termBound <= formulaSeed := by
    dsimp only [termBound, formulaSeed]
    unfold fixedWidthOpenIndexEntryFormulaSeed
    dsimp only
    omega
  have hrelationSeed : relationBound <= formulaSeed := by
    dsimp only [relationBound, formulaSeed, termBound]
    unfold fixedWidthOpenIndexEntryFormulaSeed
    dsimp only
    omega
  have hlengthSeed : lengthBound <= formulaSeed := by
    dsimp only [lengthBound, formulaSeed, termBound]
    unfold fixedWidthOpenIndexEntryFormulaSeed
    dsimp only
    omega
  have huniversalSeed : universalBound <= formulaSeed := by
    dsimp only [universalBound, formulaSeed]
    unfold fixedWidthOpenIndexEntryFormulaSeed
    dsimp only
    omega
  have hliftedUniversalSeed : liftedUniversalBound <= formulaSeed := by
    dsimp only [liftedUniversalBound, formulaSeed]
    unfold fixedWidthOpenIndexEntryFormulaSeed
    dsimp only
    omega
  have hseedFormula : 8 * formulaSeed + 64 <= formulaBound := by
    dsimp only [formulaBound]
    unfold fixedWidthOpenIndexEntryFormulaPolynomial
    omega
  have hguardRaw := lessThanSemiformula_code_le_entryRelation
    sizeTerm postSuccessor termBound hsizeTermCode hpostSuccessorCode
  have hguardSeed : (binaryFormulaCode guardFormula).length <= formulaSeed := by
    change
      (binaryFormulaCode
        (“!!sizeTerm < !!postSuccessor” : ValuationFormula)).length <=
          formulaSeed
    exact hguardRaw.trans hrelationSeed
  have hlengthRaw := embeddedLengthFormula_code_le_entry sizeTerm valueTerm
    termBound hsizeTermCode hvalueCode
  have hlengthFormulaSeed :
      (binaryFormulaCode lengthFormula).length <= formulaSeed := by
    change
      (binaryFormulaCode
        ((Rewriting.emb (ξ := Nat) lengthDef.val) ⇜
          ![sizeTerm, valueTerm])).length <= formulaSeed
    exact hlengthRaw.trans hlengthSeed
  have hsizeGuardRaw := lessOrEqualSemiformula_code_le_entryRelation
    sizeTerm widthTerm termBound hsizeTermCode hwidthCode
  have hsizeGuardSeed :
      (binaryFormulaCode sizeGuardFormula).length <= formulaSeed := by
    change
      (binaryFormulaCode
        (“!!sizeTerm ≤ !!widthTerm” : ValuationFormula)).length <= formulaSeed
    exact hsizeGuardRaw.trans hrelationSeed
  have huniversalRaw :=
    fixedWidthUniversalFormula_code_le_entryUniversalSource valuation
      tableTerm widthTerm indexTerm valueTerm scale hscale
  have huniversalFormulaSeed :
      (binaryFormulaCode universalFormula).length <= formulaSeed := by
    dsimp only [universalFormula]
    exact huniversalRaw.trans huniversalSeed
  have hinnerRaw := binaryAndSemiformula_code_length_le_entry
    sizeGuardFormula universalFormula
  have hinnerTight : (binaryFormulaCode innerFormula).length <=
      2 * formulaSeed + 8 := by
    dsimp only [innerFormula] at hinnerRaw ⊢
    omega
  have hmiddleRaw := binaryAndSemiformula_code_length_le_entry
    lengthFormula innerFormula
  have hmiddleTight : (binaryFormulaCode middleFormula).length <=
      3 * formulaSeed + 16 := by
    dsimp only [middleFormula] at hmiddleRaw ⊢
    omega
  have hpostRaw := binaryAndSemiformula_code_length_le_entry
    guardFormula middleFormula
  have hpostTight : (binaryFormulaCode postFormula).length <=
      4 * formulaSeed + 24 := by
    dsimp only [postFormula] at hpostRaw ⊢
    omega
  let bodyGuard : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
    “!!(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) < !!bodySuccessor”
  let bodyLength : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
    (Rewriting.emb (ξ := Nat) lengthDef.val) ⇜
      ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1), Rew.bShift valueTerm]
  let bodySizeGuard : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
    “!!(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) ≤
      !!(Rew.bShift widthTerm)”
  let bodyUniversal : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
    Rew.bShift ▹ universalFormula
  let bodyInner := bodySizeGuard ⋏ bodyUniversal
  let bodyMiddle := bodyLength ⋏ bodyInner
  let bodyExpanded := bodyGuard ⋏ bodyMiddle
  have hbodyDefinition : body = bodyExpanded := by
    rfl
  have hbodyGuardRaw := lessThanSemiformula_code_le_entryRelation
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) bodySuccessor termBound
      hboundVariableCode hbodySuccessorCode
  have hbodyGuardSeed :
      (binaryFormulaCode bodyGuard).length <= formulaSeed := by
    dsimp only [bodyGuard]
    exact hbodyGuardRaw.trans hrelationSeed
  have hbodyLengthRaw := embeddedLengthFormula_code_le_entry
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) (Rew.bShift valueTerm)
      termBound hboundVariableCode hshiftedValueCode
  have hbodyLengthSeed :
      (binaryFormulaCode bodyLength).length <= formulaSeed := by
    dsimp only [bodyLength]
    exact hbodyLengthRaw.trans hlengthSeed
  have hbodySizeGuardRaw := lessOrEqualSemiformula_code_le_entryRelation
    (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) (Rew.bShift widthTerm)
      termBound hboundVariableCode hshiftedWidthCode
  have hbodySizeGuardSeed :
      (binaryFormulaCode bodySizeGuard).length <= formulaSeed := by
    dsimp only [bodySizeGuard]
    exact hbodySizeGuardRaw.trans hrelationSeed
  have hbodyUniversalRaw := bShiftFormula_code_le_entryLiftedUniversal
    universalFormula scale (by
      dsimp only [universalFormula]
      exact huniversalRaw)
  have hbodyUniversalSeed :
      (binaryFormulaCode bodyUniversal).length <= formulaSeed := by
    dsimp only [bodyUniversal]
    exact hbodyUniversalRaw.trans hliftedUniversalSeed
  have hbodyInnerRaw := binaryAndSemiformula_code_length_le_entry
    bodySizeGuard bodyUniversal
  have hbodyInnerTight : (binaryFormulaCode bodyInner).length <=
      2 * formulaSeed + 8 := by
    dsimp only [bodyInner] at hbodyInnerRaw ⊢
    omega
  have hbodyMiddleRaw := binaryAndSemiformula_code_length_le_entry
    bodyLength bodyInner
  have hbodyMiddleTight : (binaryFormulaCode bodyMiddle).length <=
      3 * formulaSeed + 16 := by
    dsimp only [bodyMiddle] at hbodyMiddleRaw ⊢
    omega
  have hbodyExpandedRaw := binaryAndSemiformula_code_length_le_entry
    bodyGuard bodyMiddle
  have hbodyTight : (binaryFormulaCode body).length <=
      4 * formulaSeed + 24 := by
    rw [hbodyDefinition]
    dsimp only [bodyExpanded] at hbodyExpandedRaw ⊢
    omega
  have hexistentialRaw := binaryFormulaCode_exs_length_le body
  have hexistentialTight : (binaryFormulaCode existentialFormula).length <=
      4 * formulaSeed + 32 := by
    dsimp only [existentialFormula] at hexistentialRaw ⊢
    omega
  have hguardFormula : (binaryFormulaCode guardFormula).length <=
      formulaBound := hguardSeed.trans (by omega)
  have hlengthFormula : (binaryFormulaCode lengthFormula).length <=
      formulaBound := hlengthFormulaSeed.trans (by omega)
  have hsizeGuardFormula : (binaryFormulaCode sizeGuardFormula).length <=
      formulaBound := hsizeGuardSeed.trans (by omega)
  have huniversalFormula : (binaryFormulaCode universalFormula).length <=
      formulaBound := huniversalFormulaSeed.trans (by omega)
  have hinnerFormula : (binaryFormulaCode innerFormula).length <=
      formulaBound := hinnerTight.trans (by omega)
  have hmiddleFormula : (binaryFormulaCode middleFormula).length <=
      formulaBound := hmiddleTight.trans (by omega)
  have hpostFormula : (binaryFormulaCode postFormula).length <=
      formulaBound := hpostTight.trans (by omega)
  have hbodyFormula : (binaryFormulaCode body).length <= formulaBound :=
    hbodyTight.trans (by omega)
  have hexistentialFormula :
      (binaryFormulaCode existentialFormula).length <= formulaBound :=
    hexistentialTight.trans (by omega)
  have hwitnessFormula : (binaryTermCode witness).length <= formulaBound := by
    have hwitnessTerm : (binaryTermCode witness).length <= termBound := by
      simpa only [witness, sizeTerm] using hsizeTermCode
    exact hwitnessTerm.trans (htermBoundSeed.trans (by omega))
  have hinstanceEquality : body/[witness] = postFormula := by
    dsimp only [body, witness, postFormula, guardFormula, middleFormula,
      lengthFormula, innerFormula, sizeGuardFormula, universalFormula, size]
    exact compactFixedWidthEntryAtValuationWitnessBody_subst tableTerm
      widthTerm indexTerm valueTerm
        (Nat.size (termValue valuation valueTerm))
  have hinstanceFormula :
      (binaryFormulaCode (body/[witness])).length <= formulaBound := by
    rw [hinstanceEquality]
    exact hpostFormula
  have hguardClosed : guardFormula.freeVariables = ∅ := by
    have hsizeClosed : sizeTerm.freeVariables = ∅ := by
      dsimp only [sizeTerm]
      exact shortBinaryNumeralTerm_freeVariables_eq_empty size
    have honeClosed : paOneTerm.freeVariables = ∅ := by
      exact shortBinaryNumeralTerm_freeVariables_eq_empty 1
    have hsuccessorClosed : postSuccessor.freeVariables = ∅ := by
      dsimp only [postSuccessor]
      rw [paAddTerm_freeVariables_entry, hvalue, honeClosed]
      simp
    change
      (LO.FirstOrder.Semiformula.rel Language.LT.lt
        ![sizeTerm, postSuccessor]).freeVariables = ∅
    rw [binaryRelationFormula_freeVariables_entry, hsizeClosed,
      hsuccessorClosed]
    simp
  have hlengthClosed : lengthFormula.freeVariables = ∅ := by
    dsimp only [lengthFormula]
    unfold fixedWidthLengthFormula
    rw [binaryLengthAtValuationFormula_freeVariables]
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty, hvalue]
    simp
  have hsizeGuardClosed : sizeGuardFormula.freeVariables = ∅ := by
    have hsizeClosed : sizeTerm.freeVariables = ∅ := by
      dsimp only [sizeTerm]
      exact shortBinaryNumeralTerm_freeVariables_eq_empty size
    dsimp only [sizeGuardFormula]
    unfold fixedWidthSizeGuard
    rw [LO.FirstOrder.Semiformula.Operator.le_def]
    let equalityFormula : ValuationFormula :=
      LO.FirstOrder.Semiformula.rel Language.Eq.eq ![sizeTerm, widthTerm]
    let strictFormula : ValuationFormula :=
      LO.FirstOrder.Semiformula.rel Language.LT.lt ![sizeTerm, widthTerm]
    have hequalityClosed : equalityFormula.freeVariables = ∅ := by
      dsimp only [equalityFormula]
      rw [binaryRelationFormula_freeVariables_entry, hsizeClosed, hwidth]
      simp
    have hstrictClosed : strictFormula.freeVariables = ∅ := by
      dsimp only [strictFormula]
      rw [binaryRelationFormula_freeVariables_entry, hsizeClosed, hwidth]
      simp
    change (equalityFormula ⋎ strictFormula).freeVariables = ∅
    simp only [LO.FirstOrder.Semiformula.freeVariables_or, hequalityClosed,
      hstrictClosed, Finset.empty_union]
  have huniversalVariables : universalFormula.freeVariables ⊆ {0} := by
    dsimp only [universalFormula]
    unfold fixedWidthUniversalFormula
    exact
      fixedWidthUniversalOuterFormula_freeVariables_subset_singleton_of_openIndex
        tableTerm widthTerm indexTerm valueTerm htable hwidth hindex hvalue
  have hinnerVariables : innerFormula.freeVariables ⊆ {0} := by
    simpa only [innerFormula, LO.FirstOrder.Semiformula.freeVariables_and,
      hsizeGuardClosed, Finset.empty_union] using huniversalVariables
  have hmiddleVariables : middleFormula.freeVariables ⊆ {0} := by
    simpa only [middleFormula, LO.FirstOrder.Semiformula.freeVariables_and,
      hlengthClosed, Finset.empty_union] using hinnerVariables
  have hpostVariables : postFormula.freeVariables ⊆ {0} := by
    simpa only [postFormula, LO.FirstOrder.Semiformula.freeVariables_and,
      hguardClosed, Finset.empty_union] using hmiddleVariables
  have hentryVariables :
      (compactFixedWidthEntryAtValuationFormula tableTerm widthTerm indexTerm
        valueTerm).freeVariables ⊆ {0} := by
    intro candidate hcandidate
    unfold compactFixedWidthEntryAtValuationFormula at hcandidate
    have hsource := embeddedSubstitution_freeVariables_subset
      compactFixedWidthEntryDef.val
        ![tableTerm, widthTerm, indexTerm, valueTerm] hcandidate
    rcases Finset.mem_biUnion.mp hsource with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero =>
        have hfalse : False := by simpa [htable] using hcoordinate
        exact hfalse.elim
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            have hfalse : False := by simpa [hwidth] using hcoordinate
            exact hfalse.elim
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero =>
                have hmember : candidate ∈ indexTerm.freeVariables := by
                  simpa using hcoordinate
                exact hindex hmember
            | succ coordinate =>
                cases coordinate using Fin.cases with
                | zero =>
                    have hfalse : False := by
                      simpa [hvalue] using hcoordinate
                    exact hfalse.elim
                | succ coordinate => exact Fin.elim0 coordinate
  have hexistentialVariables : existentialFormula.freeVariables ⊆ {0} := by
    dsimp only [existentialFormula, body]
    rw [← compactFixedWidthEntryAtValuationFormula_alignment]
    exact hentryVariables
  rcases conjunctionShellCosts_le_entryLocal valuation sizeGuardFormula
      universalFormula scale hinnerVariables hzero hsizeGuardFormula
      huniversalFormula hinnerFormula with
    ⟨hweakSizeGuard, hweakUniversal, hconjunctionInner⟩
  rcases conjunctionShellCosts_le_entryLocal valuation lengthFormula
      innerFormula scale hmiddleVariables hzero hlengthFormula hinnerFormula
      hmiddleFormula with
    ⟨hweakLength, hweakInner, hconjunctionMiddle⟩
  rcases conjunctionShellCosts_le_entryLocal valuation guardFormula
      middleFormula scale hpostVariables hzero hguardFormula hmiddleFormula
      hpostFormula with
    ⟨hweakGuard, hweakMiddle, hconjunctionPost⟩
  rcases existsShellCosts_le_entryLocal valuation body witness scale
      hexistentialVariables hzero hbodyFormula hwitnessFormula
      hinstanceFormula hexistentialFormula with
    ⟨hweakInstance, hexistsIntro⟩
  let guardResource :=
    fixedWidthWitnessGuardStructuralPayloadPolynomial valuation valueTerm
  let lengthResource :=
    fixedWidthLengthStructuralPayloadPolynomial valuation valueTerm
  let sizeGuardResource :=
    fixedWidthSizeGuardStructuralPayloadPolynomial valuation widthTerm
      valueTerm
  let universalResource :=
    fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial valuation
      tableTerm widthTerm indexTerm valueTerm
  have hatomicTerm : fixedWidthOpenIndexTopAtomicTermCodePolynomial scale <=
      termBound := by
    dsimp only [termBound]
    unfold fixedWidthOpenIndexEntryTermCodePolynomial
    omega
  have hguardResource : guardResource <=
      compilePositiveRelationFixedPayloadPolynomial scale termBound := by
    exact fixedWidthWitnessGuardResource_le_fixed_of_eq valuation tableTerm
      widthTerm indexTerm valueTerm guardResource
        (compilePositiveRelationFixedPayloadPolynomial scale termBound) scale
          termBound rfl rfl hscale hatomicTerm hvalue
  have hlengthResource : lengthResource <=
      compileBinaryLengthAtValuationFixedPayloadPolynomial scale termBound := by
    exact fixedWidthLengthResource_le_fixed_of_eq valuation tableTerm widthTerm
      indexTerm valueTerm lengthResource
        (compileBinaryLengthAtValuationFixedPayloadPolynomial scale termBound)
          scale termBound rfl rfl hscale hatomicTerm hvalue
  have hsizeGuardResource : sizeGuardResource <=
      fixedWidthOpenIndexSizeGuardFixedPayloadPolynomial scale termBound := by
    exact fixedWidthSizeGuardResource_le_fixed_of_eq valuation tableTerm
      widthTerm indexTerm valueTerm sizeGuardResource
        (fixedWidthOpenIndexSizeGuardFixedPayloadPolynomial scale termBound)
          scale termBound rfl rfl hscale hatomicTerm hwidth
  have huniversalResource : universalResource <=
      fixedWidthOpenIndexUniversalFullyFixedPayloadPolynomial scale := by
    dsimp only [universalResource]
    exact
      fixedWidthUniversalOpenIndexEqualityExposedPayloadPolynomial_le_fullyFixed
        valuation tableTerm widthTerm indexTerm valueTerm scale hscale htable
          hwidth hindex hvalue
  change hybridExistsWitnessStructuralPayloadEnvelope valuation body size
      (hybridConjunctionStructuralPayloadEnvelope valuation guardFormula
        middleFormula guardResource
        (hybridConjunctionStructuralPayloadEnvelope valuation lengthFormula
          innerFormula lengthResource
          (hybridConjunctionStructuralPayloadEnvelope valuation
            sizeGuardFormula universalFormula sizeGuardResource
              universalResource))) <=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial scale
  unfold hybridExistsWitnessStructuralPayloadEnvelope
    hybridConjunctionStructuralPayloadEnvelope
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
  dsimp only [existentialFormula, postFormula, body, witness, size,
    guardFormula, middleFormula, lengthFormula, innerFormula,
    sizeGuardFormula, universalFormula, guardResource, lengthResource,
    sizeGuardResource, universalResource, termBound, localBound]
  simp only [size, guardFormula, middleFormula, lengthFormula, innerFormula,
    sizeGuardFormula, universalFormula, body, witness, termBound, localBound,
    guardResource, lengthResource, sizeGuardResource, universalResource] at hweakSizeGuard hweakUniversal hconjunctionInner
  simp only [size, guardFormula, middleFormula, lengthFormula, innerFormula,
    sizeGuardFormula, universalFormula, body, witness, termBound, localBound,
    guardResource, lengthResource, sizeGuardResource, universalResource] at hweakLength hweakInner hconjunctionMiddle
  simp only [size, guardFormula, middleFormula, lengthFormula, innerFormula,
    sizeGuardFormula, universalFormula, body, witness, termBound, localBound,
    guardResource, lengthResource, sizeGuardResource, universalResource] at hweakGuard hweakMiddle hconjunctionPost
  simp only [size, guardFormula, middleFormula, lengthFormula, innerFormula,
    sizeGuardFormula, universalFormula, body, witness, termBound, localBound,
    guardResource, lengthResource, sizeGuardResource, universalResource] at hweakInstance hexistsIntro hguardResource hlengthResource hsizeGuardResource huniversalResource
  omega

theorem
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
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
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation tableTerm widthTerm indexTerm valueTerm <=
      compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
        scale :=
  (compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_equalityExposed
    valuation tableTerm widthTerm indexTerm valueTerm).trans
      (compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial_le_fullyFixed
        valuation tableTerm widthTerm indexTerm valueTerm scale hscale htable
          hwidth hindex hvalue)

#print axioms embeddedLengthFormula_code_le_entry
#print axioms fixedWidthUniversalFormula_code_le_entryUniversalSource
#print axioms bShiftFormula_code_le_entryLiftedUniversal
#print axioms conjunctionShellCosts_le_entryLocal
#print axioms existsShellCosts_le_entryLocal
#print axioms
  compactFixedWidthEntryAtValuationOpenIndexEqualityExposedPayloadPolynomial_le_fullyFixed
#print axioms
  compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed

end FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
