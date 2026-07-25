import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
import integration.FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds
import integration.FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Fixed bounds for the uniform direct additive structured-list layout

This layer removes the concrete body-start witness and the concrete header
coordinates from the public payload resource.  The guard, list header, direct
boundary table, two conjunction shells, and existential introduction are all
charged to the common numeric and bit-width coordinates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAQuantitativeOrderBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveListHeaderPublicBounds
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedCompiler
open FoundationCompactNumericListedDirectAdditiveBoundaryTableUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

private abbrev layoutFixedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

private theorem layoutBinaryRelationFormula_freeVariables
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) :
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

private theorem layoutArithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
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

private theorem layoutTermValueArithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  change termValue valuation
      (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]) = _
  exact termValue_add valuation ![left, right]

theorem shortNumeralRewritingFormula_code_length_le_uniform
    {arity : Nat} (formula : LO.FirstOrder.ArithmeticSemisentence arity)
    (values : Fin arity -> Nat) (bitBound : Nat)
    (hsizes : forall coordinate, Nat.size (values coordinate) <= bitBound) :
    (binaryFormulaCode
      ((Rewriting.emb (ξ := Nat) formula) ⇜
        (fun coordinate => shortBinaryNumeralTerm (values coordinate)))).length <=
      uniformRewritingFormulaCodeEnvelope
        (binaryNumeralTermCodeEnvelope bitBound)
        (binaryFormulaCode (Rewriting.emb (ξ := Nat) formula)).length := by
  let rewriting : Rew ℒₒᵣ Nat arity Nat 0 := Rew.subst
    (fun coordinate => shortBinaryNumeralTerm (values coordinate))
  have hrewriting : RewritingImageCodeBound rewriting
      (binaryNumeralTermCodeEnvelope bitBound) := by
    constructor
    · intro coordinate
      dsimp only [rewriting]
      rw [Rew.subst_bvar]
      exact binaryNumeralTerm_code_length_le_envelope
        (values coordinate) bitBound (hsizes coordinate)
    · intro coordinate
      dsimp only [rewriting]
      simp
  have hraw := binaryFormulaCode_rewriting_length_le_uniform rewriting
    (binaryNumeralTermCodeEnvelope bitBound) hrewriting
    (Rewriting.emb (ξ := Nat) formula)
  simpa only [rewriting] using hraw

def structuredListHeaderLeTermCodePolynomial (bitBound : Nat) : Nat :=
  let numeralCode := binaryNumeralTermCodeEnvelope bitBound
  2 * numeralCode + binaryFunctionTermCodeOverhead Language.Add.add + 1

def structuredListHeaderLeFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * orderAtomicFormulaCodeEnvelope
      (structuredListHeaderLeTermCodePolynomial bitBound) + 8

def structuredListHeaderLeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  let termCode := structuredListHeaderLeTermCodePolynomial bitBound
  let formulaCode := structuredListHeaderLeFormulaCodePolynomial bitBound
  2 * compilePositiveRelationFixedPayloadPolynomial 0 termCode +
    3 * smallContextAssemblyEnvelope formulaCode + 1

private theorem structuredListHeaderLeftTerm_code_length_le_fixed
    (bodyStart count bitBound : Nat)
    (hbodyStartSize : Nat.size bodyStart <= bitBound)
    (hcountSize : Nat.size count <= bitBound) :
    (binaryTermCode
      (‘!!(shortBinaryNumeralTerm bodyStart) +
        !!(shortBinaryNumeralTerm count)’ : ValuationTerm)).length <=
      structuredListHeaderLeTermCodePolynomial bitBound := by
  let leftTerm := shortBinaryNumeralTerm bodyStart
  let rightTerm := shortBinaryNumeralTerm count
  have hleft := binaryNumeralTerm_code_length_le_envelope bodyStart bitBound
    hbodyStartSize
  have hright := binaryNumeralTerm_code_length_le_envelope count bitBound
    hcountSize
  have hadd := arithmeticAddTerm_code_length_le leftTerm rightTerm
  change (binaryTermCode (‘!!leftTerm + !!rightTerm’ : ValuationTerm)).length <= _
  unfold structuredListHeaderLeTermCodePolynomial
  dsimp only [leftTerm, rightTerm] at *
  omega

theorem parseValuationLeStructuralPayloadPolynomial_le_fixed
    (bodyStart count tokenCount bitBound : Nat)
    (hbodyStartSize : Nat.size bodyStart <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound) :
    parseValuationLeStructuralPayloadPolynomial
        (‘!!(shortBinaryNumeralTerm bodyStart) +
          !!(shortBinaryNumeralTerm count)’ : ValuationTerm)
        (shortBinaryNumeralTerm tokenCount) <=
      structuredListHeaderLeFixedPayloadPolynomial bitBound := by
  let leftTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bodyStart) +
      !!(shortBinaryNumeralTerm count)’
  let rightTerm := shortBinaryNumeralTerm tokenCount
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula := LO.FirstOrder.Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables
    layoutFixedZeroValuation
  let termCode := structuredListHeaderLeTermCodePolynomial bitBound
  let atomicCode := orderAtomicFormulaCodeEnvelope termCode
  let formulaCode := structuredListHeaderLeFormulaCodePolynomial bitBound
  have hleftClosed : leftTerm.freeVariables = ∅ := by
    dsimp only [leftTerm]
    rw [layoutArithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hrightClosed : rightTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hleftCode : (binaryTermCode leftTerm).length <= termCode := by
    simpa only [leftTerm, termCode] using
      structuredListHeaderLeftTerm_code_length_le_fixed bodyStart count bitBound
        hbodyStartSize hcountSize
  have hrightCode : (binaryTermCode rightTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
      htokenCountSize
    have hlarge : binaryNumeralTermCodeEnvelope bitBound <= termCode := by
      unfold termCode structuredListHeaderLeTermCodePolynomial
      dsimp only
      omega
    exact hraw.trans hlarge
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change leftTerm.freeVariables ⊆ {0}
    rw [hleftClosed]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change rightTerm.freeVariables ⊆ {0}
    rw [hrightClosed]
    simp
  have hequalityResource :=
    compilePositiveRelationPayloadPolynomial_le_fixed layoutFixedZeroValuation
      Language.Eq.eq args 0 termCode hfirst hsecond (by rfl) hleftCode
      hrightCode
  have hstrictResource :=
    compilePositiveRelationPayloadPolynomial_le_fixed layoutFixedZeroValuation
      Language.ORing.Rel.lt args 0 termCode hfirst hsecond (by rfl) hleftCode
      hrightCode
  have hequalityCode : (binaryFormulaCode equalityFormula).length <=
      atomicCode := by
    simpa only [equalityFormula, args, binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.Eq.eq leftTerm
        rightTerm termCode hleftCode hrightCode)
  have hstrictCode : (binaryFormulaCode strictFormula).length <=
      atomicCode := by
    simpa only [strictFormula, args, binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.LT.lt leftTerm
        rightTerm termCode hleftCode hrightCode)
  have hatomicFormula : atomicCode <= formulaCode := by
    unfold formulaCode structuredListHeaderLeFormulaCodePolynomial
    dsimp only [atomicCode, termCode]
    omega
  have hequalityFormula := hequalityCode.trans hatomicFormula
  have hstrictFormula := hstrictCode.trans hatomicFormula
  have htargetCode : (binaryFormulaCode targetFormula).length <=
      formulaCode := by
    have htag : (binaryNatCode 5).length <= 8 := by decide
    dsimp only [targetFormula]
    simp only [binaryFormulaCode, List.length_append]
    unfold formulaCode structuredListHeaderLeFormulaCodePolynomial
    dsimp only [atomicCode, termCode] at *
    omega
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    have hequalityClosed : equalityFormula.freeVariables = ∅ := by
      dsimp only [equalityFormula, args]
      rw [layoutBinaryRelationFormula_freeVariables]
      simp [hleftClosed, hrightClosed]
    have hstrictClosed : strictFormula.freeVariables = ∅ := by
      dsimp only [strictFormula, args]
      rw [layoutBinaryRelationFormula_freeVariables]
      simp [hleftClosed, hrightClosed]
    dsimp only [targetFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hequalityClosed,
      hstrictClosed]
    simp
  have hGammaEmpty : Gamma = ∅ := by
    unfold Gamma valuationContext
    rw [htargetClosed]
    simp
  have hGammaCard : Gamma.card <= 4 := by
    rw [hGammaEmpty]
    simp
  have hcontext : FormulaCodeBound Gamma formulaCode := by
    rw [hGammaEmpty]
    intro formula hformula
    simp at hformula
  have hequalityContext : FormulaCodeBound (insert equalityFormula Gamma)
      formulaCode := hcontext.insert hequalityFormula
  have hstrictContext : FormulaCodeBound (insert strictFormula Gamma)
      formulaCode := hcontext.insert hstrictFormula
  have hequalityCard : (insert equalityFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le equalityFormula Gamma
    omega
  have hstrictCard : (insert strictFormula Gamma).card <= 8 := by
    have hstep := Finset.card_insert_le strictFormula Gamma
    omega
  have hweakEquality := weakeningFullAssemblyCost_le_small
    (insert equalityFormula Gamma) formulaCode hequalityCard hequalityContext
  have hweakStrict := weakeningFullAssemblyCost_le_small
    (insert strictFormula Gamma) formulaCode hstrictCard hstrictContext
  have hdisjunction := disjunctionFullAssemblyCost_le_small Gamma
    equalityFormula strictFormula formulaCode hGammaCard hcontext
    hequalityFormula hstrictFormula htargetCode
  change
    compilePositiveRelationPayloadPolynomial layoutFixedZeroValuation
          Language.Eq.eq args +
        compilePositiveRelationPayloadPolynomial layoutFixedZeroValuation
          Language.ORing.Rel.lt args +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert equalityFormula Gamma) +
        FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
          (insert strictFormula Gamma) +
        CertifiedPAContextProof.disjunctionFullAssemblyCost Gamma
          equalityFormula strictFormula <=
      structuredListHeaderLeFixedPayloadPolynomial bitBound
  unfold structuredListHeaderLeFixedPayloadPolynomial
  dsimp only [termCode, formulaCode] at *
  omega

theorem structuredListHeaderLeFormula_code_length_le_fixed
    (bodyStart count tokenCount bitBound : Nat)
    (hbodyStartSize : Nat.size bodyStart <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound) :
    (binaryFormulaCode
      (“!!(‘!!(shortBinaryNumeralTerm bodyStart) +
          !!(shortBinaryNumeralTerm count)’ : ValuationTerm) ≤
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula)).length <=
      structuredListHeaderLeFormulaCodePolynomial bitBound := by
  let leftTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bodyStart) +
      !!(shortBinaryNumeralTerm count)’
  let rightTerm := shortBinaryNumeralTerm tokenCount
  let equalityFormula : ValuationFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq ![leftTerm, rightTerm]
  let strictFormula : ValuationFormula :=
    LO.FirstOrder.Semiformula.rel Language.LT.lt ![leftTerm, rightTerm]
  let termCode := structuredListHeaderLeTermCodePolynomial bitBound
  let atomicCode := orderAtomicFormulaCodeEnvelope termCode
  have hleftCode : (binaryTermCode leftTerm).length <= termCode := by
    simpa only [leftTerm, termCode] using
      structuredListHeaderLeftTerm_code_length_le_fixed bodyStart count bitBound
        hbodyStartSize hcountSize
  have hrightCode : (binaryTermCode rightTerm).length <= termCode := by
    have hraw := binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
      htokenCountSize
    exact hraw.trans (by
      unfold termCode structuredListHeaderLeTermCodePolynomial
      dsimp only
      omega)
  have hequalityCode : (binaryFormulaCode equalityFormula).length <=
      atomicCode := by
    simpa only [equalityFormula, binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.Eq.eq leftTerm
        rightTerm termCode hleftCode hrightCode)
  have hstrictCode : (binaryFormulaCode strictFormula).length <=
      atomicCode := by
    simpa only [strictFormula, binaryRelationFormula] using
      (binaryRelationFormula_code_le_orderAtomic Language.LT.lt leftTerm
        rightTerm termCode hleftCode hrightCode)
  change (binaryFormulaCode (equalityFormula ⋎ strictFormula)).length <= _
  calc
    (binaryFormulaCode (equalityFormula ⋎ strictFormula)).length <=
        2 * atomicCode + 8 := by
      have htag : (binaryNatCode 5).length <= 8 := by decide
      simp only [binaryFormulaCode, List.length_append]
      omega
    _ = structuredListHeaderLeFormulaCodePolynomial bitBound := by
      rfl

def structuredListHeaderCellFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * additiveTokenCellAtomicFormulaCodeEnvelope bitBound +
    additiveTokenCellEntryFormulaCodeEnvelope bitBound +
    2 * (binaryNatCode 4).length + 1

def structuredListHeaderAssemblySyntaxPolynomial (bitBound : Nat) : Nat :=
  structuredListHeaderCellFormulaCodePolynomial bitBound +
    structuredListHeaderLeFormulaCodePolynomial bitBound +
    (binaryNatCode 4).length + 1

def compactAdditiveListHeaderUniformFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  additiveTokenCellFullyUniformPayloadPolynomial numericBound bitBound +
    structuredListHeaderLeFixedPayloadPolynomial bitBound +
    3 * generalContextAssemblyEnvelope
      (structuredListHeaderAssemblySyntaxPolynomial bitBound)

theorem compactAdditiveTokenCellClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount cursor value next bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcursorSize : Nat.size cursor <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hnextSize : Nat.size next <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveTokenCellClosedFormula tokenTable width tokenCount cursor
        value next)).length <=
      structuredListHeaderCellFormulaCodePolynomial bitBound := by
  let cursorFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm cursor) <
      !!(shortBinaryNumeralTerm tokenCount)”
  let successorFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm next) =
      !!(shortBinaryNumeralTerm cursor) + 1”
  let entryFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm cursor) (shortBinaryNumeralTerm value)
  have hcursorCode := additiveTokenCellCursorFormula_code_length_le_uniform
    cursor tokenCount bitBound hcursorSize htokenCountSize
  have hsuccessorCode :=
    additiveTokenCellSuccessorFormula_code_length_le_uniform cursor next bitBound
      hcursorSize hnextSize
  have hentryCode := additiveTokenCellEntryFormula_code_length_le_uniform
    tokenTable width cursor value bitBound htableSize hwidthSize hcursorSize
    hvalueSize
  rw [compactAdditiveTokenCellClosedFormula_alignment]
  change (binaryFormulaCode
    (cursorFormula ⋏ (successorFormula ⋏ entryFormula))).length <= _
  simp only [binaryFormulaCode, List.length_append]
  unfold structuredListHeaderCellFormulaCodePolynomial
  dsimp only [cursorFormula, successorFormula, entryFormula] at *
  omega

theorem compactAdditiveListHeaderClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount start count bodyStart bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbodyStartSize : Nat.size bodyStart <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveListHeaderClosedFormula tokenTable width tokenCount start
        count bodyStart)).length <=
      structuredListHeaderAssemblySyntaxPolynomial bitBound := by
  let cellFormula := compactAdditiveTokenCellClosedFormula tokenTable width
    tokenCount start count bodyStart
  let leftTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bodyStart) +
      !!(shortBinaryNumeralTerm count)’
  let boundFormula : ValuationFormula :=
    “!!leftTerm ≤ !!(shortBinaryNumeralTerm tokenCount)”
  have hcellCode : (binaryFormulaCode cellFormula).length <=
      structuredListHeaderCellFormulaCodePolynomial bitBound := by
    simpa only [cellFormula] using
      compactAdditiveTokenCellClosedFormula_code_length_le_fixed tokenTable width
        tokenCount start count bodyStart bitBound htableSize hwidthSize
        htokenCountSize hstartSize hcountSize hbodyStartSize
  have hboundCode : (binaryFormulaCode boundFormula).length <=
      structuredListHeaderLeFormulaCodePolynomial bitBound := by
    simpa only [boundFormula, leftTerm] using
      structuredListHeaderLeFormula_code_length_le_fixed bodyStart count
        tokenCount bitBound hbodyStartSize hcountSize htokenCountSize
  rw [compactAdditiveListHeaderClosedFormula_alignment]
  change (binaryFormulaCode (cellFormula ⋏ boundFormula)).length <= _
  simp only [binaryFormulaCode, List.length_append]
  unfold structuredListHeaderAssemblySyntaxPolynomial
  omega

theorem
    compactAdditiveListHeaderExplicitHybridCertificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount start count bodyStart numericBound bitBound : Nat)
    (hwidthBound : width <= numericBound)
    (hstartBound : start <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hstartSize : Nat.size start <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbodyStartSize : Nat.size bodyStart <= bitBound)
    (hheader : CompactAdditiveListHeader tokenTable width tokenCount start count
      bodyStart) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveListHeaderExplicitHybridCertificate tokenTable width
          tokenCount start count bodyStart hheader) <=
      compactAdditiveListHeaderUniformFixedPayloadPolynomial numericBound
        bitBound := by
  let leftTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bodyStart) +
      !!(shortBinaryNumeralTerm count)’
  let cellFormula := compactAdditiveTokenCellClosedFormula tokenTable width
    tokenCount start count bodyStart
  let boundFormula : ValuationFormula :=
    “!!leftTerm ≤ !!(shortBinaryNumeralTerm tokenCount)”
  let cellCertificate := compactAdditiveTokenCellExplicitHybridCertificate
    tokenTable width tokenCount start count bodyStart hheader.1
  let boundCertificate := valuationLeCertificate leftTerm
    (shortBinaryNumeralTerm tokenCount) (by
      simpa [leftTerm, termValue_shortBinaryNumeralTerm,
        layoutTermValueArithmeticAdd]
        using hheader.2)
  let cellResource := additiveTokenCellFullyUniformPayloadPolynomial numericBound
    bitBound
  let boundResource := structuredListHeaderLeFixedPayloadPolynomial bitBound
  let syntaxResource := structuredListHeaderAssemblySyntaxPolynomial bitBound
  have hcell : hybridFormulaStructuralPayloadBound cellCertificate <=
      cellResource := by
    change hybridFormulaStructuralPayloadBound
      (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
        (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm start)
        (shortBinaryNumeralTerm count) (shortBinaryNumeralTerm bodyStart) (by
          simpa only [termValue_shortBinaryNumeralTerm] using hheader.1)) <= _
    exact
      compactAdditiveTokenCellShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount start count bodyStart numericBound bitBound
        hwidthBound hstartBound htableSize hwidthSize htokenCountSize hstartSize
        hcountSize hbodyStartSize hheader.1
  have hboundPublic := valuationLeCertificate_structuralPayloadBound_le_public
    leftTerm (shortBinaryNumeralTerm tokenCount) (by
      dsimp only [leftTerm]
      rw [layoutArithmeticAddTerm_freeVariables,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        shortBinaryNumeralTerm_freeVariables_eq_empty]
      simp)
    (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount) (by
      simpa [leftTerm, termValue_shortBinaryNumeralTerm,
        layoutTermValueArithmeticAdd]
        using hheader.2)
  have hboundFixed := parseValuationLeStructuralPayloadPolynomial_le_fixed
    bodyStart count tokenCount bitBound hbodyStartSize hcountSize htokenCountSize
  have hbound : hybridFormulaStructuralPayloadBound boundCertificate <=
      boundResource := by
    simpa only [boundCertificate, boundResource, leftTerm] using
      hboundPublic.trans hboundFixed
  have hparts := hybridConjunctionStructuralPayloadBound_le_envelope
    cellCertificate boundCertificate cellResource boundResource hcell hbound
  have hcellClosed : cellFormula.freeVariables = ∅ := by
    dsimp only [cellFormula]
    unfold compactAdditiveTokenCellClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      apply shortBinaryNumeralTerm_freeVariables_eq_empty
  have hboundClosed : boundFormula.freeVariables = ∅ := by
    have hleftClosed : leftTerm.freeVariables = ∅ := by
      dsimp only [leftTerm]
      rw [layoutArithmeticAddTerm_freeVariables,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        shortBinaryNumeralTerm_freeVariables_eq_empty]
      simp
    have hrightClosed :
        (shortBinaryNumeralTerm tokenCount).freeVariables = ∅ :=
      shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
    change
      (LO.FirstOrder.Semiformula.rel Language.Eq.eq
            ![leftTerm, shortBinaryNumeralTerm tokenCount] ⋎
        LO.FirstOrder.Semiformula.rel Language.LT.lt
            ![leftTerm, shortBinaryNumeralTerm tokenCount]).freeVariables = ∅
    rw [LO.FirstOrder.Semiformula.freeVariables_or,
      layoutBinaryRelationFormula_freeVariables,
      layoutBinaryRelationFormula_freeVariables]
    simp [hleftClosed, hrightClosed]
  have hcellCodeTight : (binaryFormulaCode cellFormula).length <=
      structuredListHeaderCellFormulaCodePolynomial bitBound := by
    simpa only [cellFormula] using
      compactAdditiveTokenCellClosedFormula_code_length_le_fixed tokenTable width
        tokenCount start count bodyStart bitBound htableSize hwidthSize
        htokenCountSize hstartSize hcountSize hbodyStartSize
  have hboundCodeTight : (binaryFormulaCode boundFormula).length <=
      structuredListHeaderLeFormulaCodePolynomial bitBound := by
    simpa only [boundFormula, leftTerm] using
      structuredListHeaderLeFormula_code_length_le_fixed bodyStart count
        tokenCount bitBound hbodyStartSize hcountSize htokenCountSize
  have hcellCode : (binaryFormulaCode cellFormula).length <= syntaxResource :=
    hcellCodeTight.trans (by
      unfold syntaxResource structuredListHeaderAssemblySyntaxPolynomial
      omega)
  have hboundCode : (binaryFormulaCode boundFormula).length <= syntaxResource :=
    hboundCodeTight.trans (by
      unfold syntaxResource structuredListHeaderAssemblySyntaxPolynomial
      omega)
  have hconjunctionCode : (binaryFormulaCode
      (cellFormula ⋏ boundFormula)).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append]
    unfold syntaxResource structuredListHeaderAssemblySyntaxPolynomial
    omega
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource structuredListHeaderAssemblySyntaxPolynomial
    exact Nat.le_add_left 1 _
  have hgeneral := hybridConjunctionStructuralPayloadEnvelope_le_general
    layoutFixedZeroValuation cellFormula boundFormula cellResource boundResource
    syntaxResource hpositive (by
      have hclosed : (cellFormula ⋏ boundFormula).freeVariables = ∅ := by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hcellClosed,
          hboundClosed]
        simp
      rw [hclosed]
      simp [valuationContext, formulaCodeSum]) hcellCode hboundCode
      hconjunctionCode
  have htotal := hparts.trans hgeneral
  have htotalFixed : hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        cellCertificate boundCertificate) <=
      compactAdditiveListHeaderUniformFixedPayloadPolynomial numericBound
        bitBound := by
    simpa only [compactAdditiveListHeaderUniformFixedPayloadPolynomial,
      hybridConjunctionGeneralPayloadEnvelope, cellResource, boundResource,
      syntaxResource] using htotal
  simpa only [compactAdditiveListHeaderExplicitHybridCertificate,
    hybridFormulaStructuralPayloadBound, leftTerm, cellCertificate,
    boundCertificate] using htotalFixed

#print axioms shortNumeralRewritingFormula_code_length_le_uniform
#print axioms parseValuationLeStructuralPayloadPolynomial_le_fixed
#print axioms compactAdditiveListHeaderClosedFormula_code_length_le_fixed
#print axioms
  compactAdditiveListHeaderExplicitHybridCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectFixedBounds
