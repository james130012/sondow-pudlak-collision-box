import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

private def closedSuccessorTerm (value : Nat) : ValuationTerm :=
  ‘!!(shortBinaryNumeralTerm value) + 1’

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left * !!right’ =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private noncomputable def valuationLeCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hle : termValue zeroValuation leftTerm ≤
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm ≤ !!rightTerm” := by
  if heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue zeroValuation leftTerm <
        termValue zeroValuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

private noncomputable def boundedWitnessGuardCertificate
    (value bound : Nat) (hvalue : value ≤ bound) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm value) <
        !!(shortBinaryNumeralTerm bound) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm value, rightTerm] (by
        change termValue zeroValuation (shortBinaryNumeralTerm value) <
          termValue zeroValuation rightTerm
        simp only [rightTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne]
        omega)
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

private def compactAdditiveTokenCellAtValuationFormula
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
    ![tokenTableTerm, widthTerm, tokenCountTerm, cursorTerm, valueTerm,
      nextTerm]

private def compactAdditiveTokenCellAtValuationPartsFormula
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm) : ValuationFormula :=
  “!!cursorTerm < !!tokenCountTerm” ⋏
    (“!!nextTerm = !!cursorTerm + 1” ⋏
      compactFixedWidthEntryAtValuationFormula
        tokenTableTerm widthTerm cursorTerm valueTerm)

private theorem compactAdditiveTokenCellAtValuationFormula_alignment
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm) :
    compactAdditiveTokenCellAtValuationFormula
        tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm =
      compactAdditiveTokenCellAtValuationPartsFormula
        tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm
          nextTerm := by
  unfold compactAdditiveTokenCellAtValuationFormula
  unfold compactAdditiveTokenCellAtValuationPartsFormula
  unfold compactAdditiveTokenCellDef
  unfold compactFixedWidthEntryAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

private noncomputable def
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm)
    (hcell : CompactAdditiveTokenCell
      (termValue zeroValuation tokenTableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation tokenCountTerm)
      (termValue zeroValuation cursorTerm)
      (termValue zeroValuation valueTerm)
      (termValue zeroValuation nextTerm)) :
    HybridCertificate
      (compactAdditiveTokenCellAtValuationFormula
        tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm
          nextTerm) := by
  let successorTerm : ValuationTerm := ‘!!cursorTerm + 1’
  let cursorLt :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![cursorTerm, tokenCountTerm] hcell.1
  let successor :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![nextTerm, successorTerm] (by
        change termValue zeroValuation nextTerm =
          termValue zeroValuation successorTerm
        simpa [successorTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne] using hcell.2.1)
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (.cast (Semiformula.Operator.lt_def _ _).symm cursorLt)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (.cast (Semiformula.Operator.eq_def _ _).symm successor)
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation tokenTableTerm widthTerm cursorTerm valueTerm
          hcell.2.2))
  exact .cast
    (compactAdditiveTokenCellAtValuationFormula_alignment
      tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm
        nextTerm).symm parts

private def compactAdditiveListHeaderAtValuationFormula
    (tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm :
      ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val) ⇜
    ![tokenTableTerm, widthTerm, tokenCountTerm, startTerm, countTerm,
      bodyStartTerm]

private def compactAdditiveListHeaderAtValuationPartsFormula
    (tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm :
      ValuationTerm) : ValuationFormula :=
  compactAdditiveTokenCellAtValuationFormula
      tokenTableTerm widthTerm tokenCountTerm startTerm countTerm
        bodyStartTerm ⋏
    “!!bodyStartTerm + !!countTerm ≤ !!tokenCountTerm”

private theorem compactAdditiveListHeaderAtValuationFormula_alignment
    (tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm :
      ValuationTerm) :
    compactAdditiveListHeaderAtValuationFormula
        tokenTableTerm widthTerm tokenCountTerm startTerm countTerm
          bodyStartTerm =
      compactAdditiveListHeaderAtValuationPartsFormula
        tokenTableTerm widthTerm tokenCountTerm startTerm countTerm
          bodyStartTerm := by
  unfold compactAdditiveListHeaderAtValuationFormula
  unfold compactAdditiveListHeaderAtValuationPartsFormula
  unfold compactAdditiveListHeaderDef
  unfold compactAdditiveTokenCellAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

private noncomputable def
    compactAdditiveListHeaderAtValuationExplicitHybridCertificate
    (tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm :
      ValuationTerm)
    (hheader : CompactAdditiveListHeader
      (termValue zeroValuation tokenTableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation tokenCountTerm)
      (termValue zeroValuation startTerm)
      (termValue zeroValuation countTerm)
      (termValue zeroValuation bodyStartTerm)) :
    HybridCertificate
      (compactAdditiveListHeaderAtValuationFormula
        tokenTableTerm widthTerm tokenCountTerm startTerm countTerm
          bodyStartTerm) := by
  let leftTerm : ValuationTerm := ‘!!bodyStartTerm + !!countTerm’
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      tokenTableTerm widthTerm tokenCountTerm startTerm countTerm
        bodyStartTerm hheader.1)
    (valuationLeCertificate leftTerm tokenCountTerm (by
      simpa [leftTerm, termValue_arithmeticAdd] using hheader.2))
  exact .cast
    (compactAdditiveListHeaderAtValuationFormula_alignment
      tokenTableTerm widthTerm tokenCountTerm startTerm countTerm
        bodyStartTerm).symm parts

/-- The original seventeen-coordinate task core closed by short numerals. -/
def compactNumericVerifierTaskCoreClosedFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierTaskCoreGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.tag,
      shortBinaryNumeralTerm coordinates.gammaFinish,
      shortBinaryNumeralTerm coordinates.gammaCount,
      shortBinaryNumeralTerm coordinates.gammaBoundary,
      shortBinaryNumeralTerm coordinates.firstFinish,
      shortBinaryNumeralTerm coordinates.firstCount,
      shortBinaryNumeralTerm coordinates.secondFinish,
      shortBinaryNumeralTerm coordinates.secondCount,
      shortBinaryNumeralTerm coordinates.witnessFinish,
      shortBinaryNumeralTerm coordinates.witnessCount,
      shortBinaryNumeralTerm coordinates.suffixCount,
      shortBinaryNumeralTerm sizeWitness.gammaBoundarySize]

/-- The tag cell with the original substituted `start + 1` endpoint term. -/
def compactNumericVerifierTaskCoreTagCellFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.tag,
      closedSuccessorTerm coordinates.start]

/-- The gamma layout with the same substituted successor term as the source. -/
def compactNumericVerifierTaskCoreGammaLayoutFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveStructuredListLayoutDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      closedSuccessorTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.gammaCount,
      shortBinaryNumeralTerm coordinates.gammaFinish,
      shortBinaryNumeralTerm coordinates.gammaBoundary]

private def compactNumericVerifierTaskCoreGammaLayoutWitnessBody
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates) :
    ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) + 1” ⋏
    (((Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val) ⇜
      ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
        Rew.bShift (shortBinaryNumeralTerm width),
        Rew.bShift (shortBinaryNumeralTerm tokenCount),
        Rew.bShift (closedSuccessorTerm coordinates.start),
        Rew.bShift (shortBinaryNumeralTerm coordinates.gammaCount),
        (#0 : ArithmeticSemiterm Nat 1)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveBoundaryTableDef.val) ⇜
        ![Rew.bShift (shortBinaryNumeralTerm tokenCount),
          Rew.bShift (shortBinaryNumeralTerm coordinates.gammaCount),
          (#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift (shortBinaryNumeralTerm coordinates.gammaFinish),
          Rew.bShift (shortBinaryNumeralTerm coordinates.gammaBoundary)]))

private theorem compactNumericVerifierTaskCoreGammaLayoutFormula_alignment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates) :
    compactNumericVerifierTaskCoreGammaLayoutFormula
        tokenTable width tokenCount coordinates =
      ∃⁰ compactNumericVerifierTaskCoreGammaLayoutWitnessBody
        tokenTable width tokenCount coordinates := by
  unfold compactNumericVerifierTaskCoreGammaLayoutFormula
  unfold compactNumericVerifierTaskCoreGammaLayoutWitnessBody
  unfold compactAdditiveStructuredListLayoutDef
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  · congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private noncomputable def compactAdditiveBoundaryTableRowDataOfBoundary
    (tokenCount count bodyStart finish boundaryTable : Nat)
    (hboundary : CompactAdditiveBoundaryTable
      tokenCount count bodyStart finish boundaryTable)
    (index : Fin count) :
    CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index := by
  let leftExists := hboundary.2.2.2.2 index index.isLt
  let left := Classical.choose leftExists
  have hleft := Classical.choose_spec leftExists
  let rightExists := hleft.2
  let right := Classical.choose rightExists
  have hright := Classical.choose_spec rightExists
  exact
    { left := left
      right := right
      left_le := hleft.1
      right_le := hright.1
      left_entry := hright.2.1
      right_entry := hright.2.2.1
      left_lt_right := hright.2.2.2 }

private noncomputable def
    compactNumericVerifierTaskCoreGammaLayoutExplicitHybridCertificate
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount (coordinates.start + 1)
        coordinates.gammaCount coordinates.gammaFinish
        coordinates.gammaBoundary) :
    HybridCertificate
      (compactNumericVerifierTaskCoreGammaLayoutFormula
        tokenTable width tokenCount coordinates) := by
  let bodyStart := Classical.choose hlayout
  have hbody := Classical.choose_spec hlayout
  have hbodyStart : bodyStart ≤ tokenCount := hbody.1
  have hheader : CompactAdditiveListHeader
      tokenTable width tokenCount (coordinates.start + 1)
        coordinates.gammaCount bodyStart := hbody.2.1
  have hboundary : CompactAdditiveBoundaryTable
      tokenCount coordinates.gammaCount bodyStart coordinates.gammaFinish
        coordinates.gammaBoundary := hbody.2.2
  rw [compactNumericVerifierTaskCoreGammaLayoutFormula_alignment]
  refine .existsWitness
    (compactNumericVerifierTaskCoreGammaLayoutWitnessBody
      tokenTable width tokenCount coordinates) bodyStart ?_
  have hheaderAtTerms : CompactAdditiveListHeader
      (termValue zeroValuation (shortBinaryNumeralTerm tokenTable))
      (termValue zeroValuation (shortBinaryNumeralTerm width))
      (termValue zeroValuation (shortBinaryNumeralTerm tokenCount))
      (termValue zeroValuation (closedSuccessorTerm coordinates.start))
      (termValue zeroValuation
        (shortBinaryNumeralTerm coordinates.gammaCount))
      (termValue zeroValuation (shortBinaryNumeralTerm bodyStart)) := by
    simpa [closedSuccessorTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticOne] using hheader
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (boundedWitnessGuardCertificate bodyStart tokenCount hbodyStart)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveListHeaderAtValuationExplicitHybridCertificate
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (closedSuccessorTerm coordinates.start)
        (shortBinaryNumeralTerm coordinates.gammaCount)
        (shortBinaryNumeralTerm bodyStart) hheaderAtTerms)
      (compactAdditiveBoundaryTableExplicitHybridCertificate
        tokenCount coordinates.gammaCount bodyStart
          coordinates.gammaFinish coordinates.gammaBoundary
          hboundary.1 hboundary.2.1 hboundary.2.2.1
          hboundary.2.2.2.1
          (compactAdditiveBoundaryTableRowDataOfBoundary
            tokenCount coordinates.gammaCount bodyStart
              coordinates.gammaFinish coordinates.gammaBoundary
              hboundary)))
  exact .cast (by
    simp [compactNumericVerifierTaskCoreGammaLayoutWitnessBody,
      compactAdditiveListHeaderAtValuationFormula,
      compactAdditiveBoundaryTableClosedFormula,
      ← TransitiveRewriting.comp_app]
    constructor
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate) post

/-- The exact nine immediate conjuncts of the closed task core. -/
def compactNumericVerifierTaskCorePartsFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    ValuationFormula :=
  compactNumericVerifierTaskCoreTagCellFormula
      tokenTable width tokenCount coordinates ⋏
    (compactNumericVerifierTaskCoreGammaLayoutFormula
        tokenTable width tokenCount coordinates ⋏
      (compactAdditiveNatListListRowsClosedFormula
          tokenTable width tokenCount coordinates.gammaBoundary
            coordinates.gammaCount ⋏
        (binaryLengthAtValuationFormula
            (shortBinaryNumeralTerm sizeWitness.gammaBoundarySize)
            (shortBinaryNumeralTerm coordinates.gammaBoundary) ⋏
          (“!!(shortBinaryNumeralTerm sizeWitness.gammaBoundarySize) ≤
              (!!(shortBinaryNumeralTerm coordinates.gammaCount) + 1) *
                !!(shortBinaryNumeralTerm tokenCount)” ⋏
            (compactAdditiveNatListSliceClosedFormula
                tokenTable width tokenCount coordinates.gammaFinish
                  coordinates.firstCount coordinates.firstFinish ⋏
              (compactAdditiveNatListSliceClosedFormula
                  tokenTable width tokenCount coordinates.firstFinish
                    coordinates.secondCount coordinates.secondFinish ⋏
                (compactAdditiveNatListSliceClosedFormula
                    tokenTable width tokenCount coordinates.secondFinish
                      coordinates.witnessCount coordinates.witnessFinish ⋏
                  compactAdditiveNatListSliceClosedFormula
                    tokenTable width tokenCount coordinates.witnessFinish
                      coordinates.suffixCount coordinates.finish)))))))

/-- Exact syntactic alignment of the closed core with its nine conjuncts. -/
theorem compactNumericVerifierTaskCoreClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    compactNumericVerifierTaskCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness =
      compactNumericVerifierTaskCorePartsFormula
        tokenTable width tokenCount coordinates sizeWitness := by
  rcases coordinates with
    ⟨start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
      firstFinish, firstCount, secondFinish, secondCount,
      witnessFinish, witnessCount, suffixCount⟩
  rcases sizeWitness with ⟨gammaBoundarySize⟩
  unfold compactNumericVerifierTaskCoreClosedFormula
  unfold compactNumericVerifierTaskCorePartsFormula
  unfold compactNumericVerifierTaskCoreTagCellFormula
  unfold compactNumericVerifierTaskCoreGammaLayoutFormula
  unfold compactNumericVerifierTaskCoreGraphDef
  simp [closedSuccessorTerm,
    compactAdditiveNatListListRowsClosedFormula,
    compactNatSizeDef, binaryLengthAtValuationFormula,
    compactAdditiveNatListSliceClosedFormula,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

/-- Build the genuine explicit certificate from the nine fields of `hcore`. -/
noncomputable def compactNumericVerifierTaskCoreExplicitHybridCertificate
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hcore : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    HybridCertificate
      (compactNumericVerifierTaskCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness) := by
  rw [compactNumericVerifierTaskCoreClosedFormula_alignment]
  rcases hcore with
    ⟨htagCell, hgammaLayout, hgammaRows, hsizeEq, hsizeBound,
      hfirstSlice, hsecondSlice, hwitnessSlice, hsuffixSlice⟩
  have htagCellAtTerms : CompactAdditiveTokenCell
      (termValue zeroValuation (shortBinaryNumeralTerm tokenTable))
      (termValue zeroValuation (shortBinaryNumeralTerm width))
      (termValue zeroValuation (shortBinaryNumeralTerm tokenCount))
      (termValue zeroValuation
        (shortBinaryNumeralTerm coordinates.start))
      (termValue zeroValuation
        (shortBinaryNumeralTerm coordinates.tag))
      (termValue zeroValuation
        (closedSuccessorTerm coordinates.start)) := by
    simpa [closedSuccessorTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticOne] using htagCell
  let tagCell :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm coordinates.start)
      (shortBinaryNumeralTerm coordinates.tag)
      (closedSuccessorTerm coordinates.start) htagCellAtTerms
  have tagCell' : HybridCertificate
      (compactNumericVerifierTaskCoreTagCellFormula
        tokenTable width tokenCount coordinates) := by
    simpa only [compactNumericVerifierTaskCoreTagCellFormula,
      compactAdditiveTokenCellAtValuationFormula] using tagCell
  let sizeBoundTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm coordinates.gammaCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    tagCell'
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactNumericVerifierTaskCoreGammaLayoutExplicitHybridCertificate
        tokenTable width tokenCount coordinates hgammaLayout)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListListRowsExplicitHybridCertificate
          tokenTable width tokenCount coordinates.gammaBoundary
            coordinates.gammaCount hgammaRows)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (.binaryLength zeroValuation
            (shortBinaryNumeralTerm sizeWitness.gammaBoundarySize)
            (shortBinaryNumeralTerm coordinates.gammaBoundary) (by
              simpa [termValue_shortBinaryNumeralTerm] using hsizeEq))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (valuationLeCertificate
              (shortBinaryNumeralTerm sizeWitness.gammaBoundarySize)
              sizeBoundTerm (by
                simpa [sizeBoundTerm, termValue_shortBinaryNumeralTerm,
                  termValue_arithmeticAdd, termValue_arithmeticMul,
                  termValue_arithmeticOne] using hsizeBound))
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListSliceExplicitHybridCertificateOfSlice
                tokenTable width tokenCount coordinates.gammaFinish
                  coordinates.firstCount coordinates.firstFinish
                  hfirstSlice)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListSliceExplicitHybridCertificateOfSlice
                  tokenTable width tokenCount coordinates.firstFinish
                    coordinates.secondCount coordinates.secondFinish
                    hsecondSlice)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (compactAdditiveNatListSliceExplicitHybridCertificateOfSlice
                    tokenTable width tokenCount coordinates.secondFinish
                      coordinates.witnessCount coordinates.witnessFinish
                      hwitnessSlice)
                  (compactAdditiveNatListSliceExplicitHybridCertificateOfSlice
                    tokenTable width tokenCount coordinates.witnessFinish
                      coordinates.suffixCount coordinates.finish
                      hsuffixSlice))))))))
  simpa only [compactNumericVerifierTaskCorePartsFormula,
    sizeBoundTerm] using parts

#print axioms compactNumericVerifierTaskCoreClosedFormula_alignment
#print axioms compactNumericVerifierTaskCoreExplicitHybridCertificate

end FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate
