import integration.FoundationCompactNumericListedDirectTokenSliceClosedTermWitnessFormulaCodeBounds
import integration.FoundationCompactPAHybridSixConjunctionClosedGeneralBounds
import integration.FoundationCompactPAExplicitBoundedWitnessHybridPublicFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactPAFreeFormulaVariableTransport

/-!
# Fully fixed token-slice payload over arbitrary closed endpoint terms

All six post-witness leaves, five conjunction assemblies, and the existential
witness shell are bounded by explicit functions of the public numeric,
term-code, and bit-width coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectTokenSliceClosedTermFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAFreeFormulaVariableTransport
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceClosedTermLeafFixedBounds
open FoundationCompactNumericListedDirectTokenSlicePostWitnessClosedTermAtomicFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalEndpointFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalFixedBounds
open FoundationCompactNumericListedDirectTokenSliceClosedTermWitnessFormulaCodeBounds
open FoundationCompactPAHybridSixConjunctionClosedGeneralBounds

private theorem tokenSliceClosedTermBinaryFunction_freeVariables
    {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (LO.FirstOrder.Semiterm.func functionSymbol ![left, right]).freeVariables =
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

private theorem tokenSliceClosedTermAdd_freeVariables
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity) :
    (‘!!left + !!right’ :
      LO.FirstOrder.ArithmeticSemiterm Nat arity).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact tokenSliceClosedTermBinaryFunction_freeVariables Language.Add.add
    left right

private theorem tokenSliceClosedTermOne_freeVariables
    {arity : Nat} :
    (‘1’ : LO.FirstOrder.ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem tokenSliceClosedTermAdd_closed
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (‘!!left + !!right’ :
      LO.FirstOrder.ArithmeticSemiterm Nat arity).freeVariables = ∅ := by
  rw [tokenSliceClosedTermAdd_freeVariables, hleft, hright]
  simp

private theorem tokenSliceClosedTermBinaryRelation_closed
    {arity : Nat}
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right] :
      LO.FirstOrder.ArithmeticSemiformula Nat arity).freeVariables = ∅ := by
  ext candidate
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  simp [hleft, hright]

private theorem tokenSliceClosedTermLe_closed
    {arity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat arity)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (“!!left ≤ !!right” :
      LO.FirstOrder.ArithmeticSemiformula Nat arity).freeVariables = ∅ := by
  change
    ((LO.FirstOrder.Semiformula.rel Language.Eq.eq ![left, right]) ⋎
      LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
        ![left, right] :
          LO.FirstOrder.ArithmeticSemiformula Nat arity).freeVariables = ∅
  rw [LO.FirstOrder.Semiformula.freeVariables_or,
    tokenSliceClosedTermBinaryRelation_closed Language.Eq.eq left right
      hleft hright,
    tokenSliceClosedTermBinaryRelation_closed Language.ORing.Rel.lt left right
      hleft hright]
  simp

def tokenSliceClosedTermPostWitnessFullyFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  hybridSixConjunctionGeneralPayloadEnvelope
    (tokenSliceClosedTermPostWitnessFormulaCodePolynomial termCode)
    (tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
      termCode)
    (tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
      termCode)
    (tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
      termCode)
    (tokenSlicePostWitnessClosedTermLeFixedPayloadPolynomial termCode)
    (tokenSlicePostWitnessClosedTermLeFixedPayloadPolynomial termCode)
    (tokenSliceClosedTermOffsetUniversalFullyFixedPayloadPolynomial
      numericBound termCode bitBound)

theorem
    tokenSliceClosedTermPostWitnessLeafFixedPayloadPolynomial_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width count numericBound termCode bitBound : Nat)
    (tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm : ValuationTerm)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hcountCode :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <= termCode)
    (htokenCountCode : (binaryTermCode tokenCountTerm).length <= termCode)
    (hsourceStartCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (hsourceFinishCode : (binaryTermCode sourceFinishTerm).length <= termCode)
    (htargetStartCode : (binaryTermCode targetStartTerm).length <= termCode)
    (htargetFinishCode : (binaryTermCode targetFinishTerm).length <= termCode)
    (htokenCountClosed : tokenCountTerm.freeVariables = ∅)
    (hsourceStartClosed : sourceStartTerm.freeVariables = ∅)
    (hsourceFinishClosed : sourceFinishTerm.freeVariables = ∅)
    (htargetStartClosed : targetStartTerm.freeVariables = ∅)
    (htargetFinishClosed : targetFinishTerm.freeVariables = ∅) :
    tokenSliceClosedTermPostWitnessLeafFixedPayloadPolynomial valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) tokenCountTerm sourceStartTerm
        sourceFinishTerm targetStartTerm targetFinishTerm count numericBound
        termCode bitBound <=
      tokenSliceClosedTermPostWitnessFullyFixedPayloadPolynomial numericBound
        termCode bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let countTerm := shortBinaryNumeralTerm count
  let countFormula : ValuationFormula :=
    “!!countTerm < !!tokenCountTerm + 1”
  let sourceEndpointFormula : ValuationFormula :=
    “!!sourceFinishTerm = !!sourceStartTerm + !!countTerm”
  let targetEndpointFormula : ValuationFormula :=
    “!!targetFinishTerm = !!targetStartTerm + !!countTerm”
  let sourceFinishFormula : ValuationFormula :=
    “!!sourceFinishTerm ≤ !!tokenCountTerm”
  let targetFinishFormula : ValuationFormula :=
    “!!targetFinishTerm ≤ !!tokenCountTerm”
  let offsetFormula := tokenSliceAtValuationOffsetUniversalFormula tableTerm
    widthTerm sourceStartTerm targetStartTerm count
  let syntaxResource :=
    tokenSliceClosedTermPostWitnessFormulaCodePolynomial termCode
  let atomicResource :=
    tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
      termCode
  let leResource :=
    tokenSlicePostWitnessClosedTermLeFixedPayloadPolynomial termCode
  let offsetResource :=
    tokenSliceClosedTermOffsetUniversalFullyFixedPayloadPolynomial
      numericBound termCode bitBound
  have hcountTermClosed : countTerm.freeVariables = ∅ := by
    dsimp only [countTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty count
  have htableClosed : tableTerm.freeVariables = ∅ := by
    dsimp only [tableTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidthClosed : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hcountFormulaClosed : countFormula.freeVariables = ∅ := by
    dsimp only [countFormula]
    exact tokenSliceClosedTermBinaryRelation_closed
      Language.ORing.Rel.lt countTerm
      (‘!!tokenCountTerm + 1’ : ValuationTerm) hcountTermClosed
      (tokenSliceClosedTermAdd_closed tokenCountTerm (‘1’ : ValuationTerm)
        htokenCountClosed tokenSliceClosedTermOne_freeVariables)
  have hsourceEndpointClosed : sourceEndpointFormula.freeVariables = ∅ := by
    dsimp only [sourceEndpointFormula]
    exact tokenSliceClosedTermBinaryRelation_closed Language.Eq.eq
      sourceFinishTerm (‘!!sourceStartTerm + !!countTerm’ : ValuationTerm)
      hsourceFinishClosed
      (tokenSliceClosedTermAdd_closed sourceStartTerm countTerm
        hsourceStartClosed hcountTermClosed)
  have htargetEndpointClosed : targetEndpointFormula.freeVariables = ∅ := by
    dsimp only [targetEndpointFormula]
    exact tokenSliceClosedTermBinaryRelation_closed Language.Eq.eq
      targetFinishTerm (‘!!targetStartTerm + !!countTerm’ : ValuationTerm)
      htargetFinishClosed
      (tokenSliceClosedTermAdd_closed targetStartTerm countTerm
        htargetStartClosed hcountTermClosed)
  have hsourceFinishClosedFormula :
      sourceFinishFormula.freeVariables = ∅ := by
    dsimp only [sourceFinishFormula]
    exact tokenSliceClosedTermLe_closed sourceFinishTerm tokenCountTerm
      hsourceFinishClosed htokenCountClosed
  have htargetFinishClosedFormula :
      targetFinishFormula.freeVariables = ∅ := by
    dsimp only [targetFinishFormula]
    exact tokenSliceClosedTermLe_closed targetFinishTerm tokenCountTerm
      htargetFinishClosed htokenCountClosed
  have hoffsetClosed : offsetFormula.freeVariables = ∅ := by
    dsimp only [offsetFormula]
    unfold tokenSliceAtValuationOffsetUniversalFormula
    exact tokenSliceAtValuationOffsetUniversal_freeVariables_eq_empty_closed
      tokenTable width count sourceStartTerm targetStartTerm
      hsourceStartClosed htargetStartClosed
  have hpostCode :=
    tokenSliceAtValuationPostWitnessFormula_code_length_le_closedFixed
      tableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm count termCode htableCode hwidthCode
      htokenCountCode hsourceStartCode hsourceFinishCode htargetStartCode
      htargetFinishCode hcountCode
  rw [tokenSliceAtValuationPostWitnessFormula_alignment] at hpostCode
  have hpositive : 1 <= syntaxResource := by
    have htag : 1 <= (binaryNatCode 4).length := by decide
    have hnonempty :
        1 <=
          (binaryFormulaCode
            (tokenSliceAtValuationDecomposedPostWitnessFormula tableTerm
              widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
              targetStartTerm targetFinishTerm count)).length := by
      simp [tokenSliceAtValuationDecomposedPostWitnessFormula,
        binaryFormulaCode]
      exact htag.trans (by omega)
    exact hnonempty.trans (by simpa only [syntaxResource] using hpostCode)
  have hassembly :=
    transparentHybridSixConjunctionPayloadEnvelope_le_closedGeneral valuation
      countFormula sourceEndpointFormula targetEndpointFormula
      sourceFinishFormula targetFinishFormula offsetFormula atomicResource
      atomicResource atomicResource leResource leResource offsetResource
      syntaxResource hpositive hcountFormulaClosed hsourceEndpointClosed
      htargetEndpointClosed hsourceFinishClosedFormula
      htargetFinishClosedFormula hoffsetClosed (by
        simpa only [countFormula, sourceEndpointFormula,
          targetEndpointFormula, sourceFinishFormula, targetFinishFormula,
          offsetFormula, tableTerm, widthTerm, countTerm, syntaxResource,
          tokenSliceAtValuationDecomposedPostWitnessFormula] using hpostCode)
  unfold tokenSliceClosedTermPostWitnessLeafFixedPayloadPolynomial
    tokenSliceClosedTermPostWitnessFullyFixedPayloadPolynomial
  simpa only [countFormula, sourceEndpointFormula, targetEndpointFormula,
    sourceFinishFormula, targetFinishFormula, offsetFormula, tableTerm,
    widthTerm, countTerm, syntaxResource, atomicResource, leResource,
    offsetResource] using hassembly

def tokenSliceClosedTermExistentialAssemblySyntaxPolynomial
    (termCode : Nat) : Nat :=
  tokenSliceClosedTermWitnessBodyCodePolynomial termCode +
    tokenSliceClosedTermPostWitnessFormulaCodePolynomial termCode +
    tokenSliceClosedTermExistentialFormulaCodePolynomial termCode +
    termCode + 1

def compactFixedWidthTokenSlicesEqAtValuationClosedTermFullyFixedPayloadPolynomial
    (numericBound termCode bitBound : Nat) : Nat :=
  hybridExistsWitnessGeneralPayloadEnvelope
    (tokenSliceClosedTermExistentialAssemblySyntaxPolynomial termCode)
    (tokenSliceClosedTermPostWitnessFullyFixedPayloadPolynomial numericBound
      termCode bitBound)

private theorem tokenSliceAtValuationExistential_freeVariables_eq_empty_closed
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (htableClosed : tokenTableTerm.freeVariables = ∅)
    (hwidthClosed : widthTerm.freeVariables = ∅)
    (htokenCountClosed : tokenCountTerm.freeVariables = ∅)
    (hsourceStartClosed : sourceStartTerm.freeVariables = ∅)
    (hsourceFinishClosed : sourceFinishTerm.freeVariables = ∅)
    (htargetStartClosed : targetStartTerm.freeVariables = ∅)
    (htargetFinishClosed : targetFinishTerm.freeVariables = ∅) :
    (∃⁰ tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm
      tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm : ValuationFormula).freeVariables = ∅ := by
  rw [← compactFixedWidthTokenSlicesEqAtValuationFormula_alignment]
  unfold compactFixedWidthTokenSlicesEqAtValuationFormula
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate
  · exact htableClosed
  · exact hwidthClosed
  · exact htokenCountClosed
  · exact hsourceStartClosed
  · exact hsourceFinishClosed
  · exact htargetStartClosed
  · exact htargetFinishClosed

theorem
    compactFixedWidthTokenSlicesEqAtValuationClosedTermLeafFixedPayloadPolynomial_le_fullyFixed
    (valuation : Nat -> Nat)
    (tokenTable width count numericBound termCode bitBound : Nat)
    (tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm : ValuationTerm)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hcountCode :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <= termCode)
    (htokenCountCode : (binaryTermCode tokenCountTerm).length <= termCode)
    (hsourceStartCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (hsourceFinishCode : (binaryTermCode sourceFinishTerm).length <= termCode)
    (htargetStartCode : (binaryTermCode targetStartTerm).length <= termCode)
    (htargetFinishCode : (binaryTermCode targetFinishTerm).length <= termCode)
    (htokenCountClosed : tokenCountTerm.freeVariables = ∅)
    (hsourceStartClosed : sourceStartTerm.freeVariables = ∅)
    (hsourceFinishClosed : sourceFinishTerm.freeVariables = ∅)
    (htargetStartClosed : targetStartTerm.freeVariables = ∅)
    (htargetFinishClosed : targetFinishTerm.freeVariables = ∅) :
    compactFixedWidthTokenSlicesEqAtValuationClosedTermLeafFixedPayloadPolynomial
        valuation (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) tokenCountTerm sourceStartTerm
        sourceFinishTerm targetStartTerm targetFinishTerm count numericBound
        termCode bitBound <=
      compactFixedWidthTokenSlicesEqAtValuationClosedTermFullyFixedPayloadPolynomial
        numericBound termCode bitBound := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let body := tokenSliceAtValuationWitnessBody tableTerm widthTerm
    tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
    targetFinishTerm
  let syntaxResource :=
    tokenSliceClosedTermExistentialAssemblySyntaxPolynomial termCode
  let bodyResource :=
    tokenSliceClosedTermPostWitnessFullyFixedPayloadPolynomial numericBound
      termCode bitBound
  have hpost :=
    tokenSliceClosedTermPostWitnessLeafFixedPayloadPolynomial_le_fullyFixed
      valuation tokenTable width count numericBound termCode bitBound
      tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm htableCode hwidthCode hcountCode htokenCountCode
      hsourceStartCode hsourceFinishCode htargetStartCode htargetFinishCode
      htokenCountClosed hsourceStartClosed hsourceFinishClosed
      htargetStartClosed htargetFinishClosed
  have htableClosed : tableTerm.freeVariables = ∅ := by
    dsimp only [tableTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  have hwidthClosed : widthTerm.freeVariables = ∅ := by
    dsimp only [widthTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  have hexistsClosed :=
    tokenSliceAtValuationExistential_freeVariables_eq_empty_closed tableTerm
      widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm htableClosed hwidthClosed htokenCountClosed
      hsourceStartClosed hsourceFinishClosed htargetStartClosed
      htargetFinishClosed
  have hcontext : formulaCodeSum
      (valuationContext
        (∃⁰ body : ValuationFormula).freeVariables valuation) <=
        syntaxResource := by
    rw [show (∃⁰ body : ValuationFormula).freeVariables = ∅ by
      simpa only [body] using hexistsClosed]
    simp [valuationContext, formulaCodeSum]
  have hbodyCode :=
    tokenSliceAtValuationWitnessBody_code_length_le_closedFixed tableTerm
      widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm termCode htableCode hwidthCode htokenCountCode
      hsourceStartCode hsourceFinishCode htargetStartCode htargetFinishCode
  have hpostCode :=
    tokenSliceAtValuationPostWitnessFormula_code_length_le_closedFixed tableTerm
      widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm count termCode htableCode hwidthCode htokenCountCode
      hsourceStartCode hsourceFinishCode htargetStartCode htargetFinishCode
      hcountCode
  have hexistsCode :=
    tokenSliceAtValuationExistentialFormula_code_length_le_closedFixed tableTerm
      widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm termCode htableCode hwidthCode htokenCountCode
      hsourceStartCode hsourceFinishCode htargetStartCode htargetFinishCode
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource
    unfold tokenSliceClosedTermExistentialAssemblySyntaxPolynomial
    omega
  have hbodySyntax : (binaryFormulaCode body).length <= syntaxResource := by
    dsimp only [body, syntaxResource]
    unfold tokenSliceClosedTermExistentialAssemblySyntaxPolynomial
    omega
  have hwitnessSyntax :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <=
        syntaxResource := by
    dsimp only [syntaxResource]
    unfold tokenSliceClosedTermExistentialAssemblySyntaxPolynomial
    omega
  have hinstantiatedSyntax :
      (binaryFormulaCode (body/[shortBinaryNumeralTerm count])).length <=
        syntaxResource := by
    have halign :
        body/[shortBinaryNumeralTerm count] =
          tokenSliceAtValuationPostWitnessFormula tableTerm widthTerm
            tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
            targetFinishTerm count := by
      rfl
    rw [halign]
    dsimp only [syntaxResource]
    unfold tokenSliceClosedTermExistentialAssemblySyntaxPolynomial
    omega
  have hexistsSyntax :
      (binaryFormulaCode (∃⁰ body : ValuationFormula)).length <=
        syntaxResource := by
    dsimp only [body, syntaxResource]
    unfold tokenSliceClosedTermExistentialAssemblySyntaxPolynomial
    omega
  have hexistsAssembly :=
    hybridExistsWitnessStructuralPayloadEnvelope_le_general valuation body
      count bodyResource syntaxResource hpositive hcontext hbodySyntax
      hwitnessSyntax hinstantiatedSyntax hexistsSyntax
  have hmono :
      hybridExistsWitnessStructuralPayloadEnvelope valuation body count
          (tokenSliceClosedTermPostWitnessLeafFixedPayloadPolynomial valuation
            tableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
            targetStartTerm targetFinishTerm count numericBound termCode
            bitBound) <=
        hybridExistsWitnessStructuralPayloadEnvelope valuation body count
          bodyResource := by
    unfold hybridExistsWitnessStructuralPayloadEnvelope
    dsimp only [bodyResource, tableTerm, widthTerm] at hpost ⊢
    omega
  unfold
    compactFixedWidthTokenSlicesEqAtValuationClosedTermLeafFixedPayloadPolynomial
    compactFixedWidthTokenSlicesEqAtValuationClosedTermFullyFixedPayloadPolynomial
  simpa only [tableTerm, widthTerm, body, syntaxResource, bodyResource] using
    hmono.trans hexistsAssembly

theorem compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedFixed
    (valuation : Nat -> Nat)
    (tokenTable width count numericBound termCode bitBound : Nat)
    (tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm : ValuationTerm)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hcountCode :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <= termCode)
    (htokenCountCode : (binaryTermCode tokenCountTerm).length <= termCode)
    (hsourceStartCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (hsourceFinishCode : (binaryTermCode sourceFinishTerm).length <= termCode)
    (htargetStartCode : (binaryTermCode targetStartTerm).length <= termCode)
    (htargetFinishCode : (binaryTermCode targetFinishTerm).length <= termCode)
    (htokenCountClosed : tokenCountTerm.freeVariables = ∅)
    (hsourceStartClosed : sourceStartTerm.freeVariables = ∅)
    (hsourceFinishClosed : sourceFinishTerm.freeVariables = ∅)
    (htargetStartClosed : targetStartTerm.freeVariables = ∅)
    (htargetFinishClosed : targetFinishTerm.freeVariables = ∅)
    (hwidth : width <= numericBound)
    (hsourceStart : termValue valuation sourceStartTerm <= numericBound)
    (htargetStart : termValue valuation targetStartTerm <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) tokenCountTerm sourceStartTerm
        sourceFinishTerm targetStartTerm targetFinishTerm count <=
      compactFixedWidthTokenSlicesEqAtValuationClosedTermFullyFixedPayloadPolynomial
        numericBound termCode bitBound := by
  exact
    (compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedLeafFixed
      valuation tokenTable width count numericBound termCode bitBound
      tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm htableCode hwidthCode hcountCode htokenCountCode
      hsourceStartCode hsourceFinishCode htargetStartCode htargetFinishCode
      htokenCountClosed hsourceStartClosed hsourceFinishClosed
      htargetStartClosed htargetFinishClosed hwidth hsourceStart htargetStart
      hcount htableSize hwidthSize hnumericSize).trans
        (compactFixedWidthTokenSlicesEqAtValuationClosedTermLeafFixedPayloadPolynomial_le_fullyFixed
          valuation tokenTable width count numericBound termCode bitBound
          tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
          targetFinishTerm htableCode hwidthCode hcountCode htokenCountCode
          hsourceStartCode hsourceFinishCode htargetStartCode htargetFinishCode
          htokenCountClosed hsourceStartClosed hsourceFinishClosed
          htargetStartClosed htargetFinishClosed)

#print axioms
  tokenSliceClosedTermPostWitnessLeafFixedPayloadPolynomial_le_fullyFixed
#print axioms
  compactFixedWidthTokenSlicesEqAtValuationClosedTermLeafFixedPayloadPolynomial_le_fullyFixed
#print axioms
  compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedFixed

end FoundationCompactNumericListedDirectTokenSliceClosedTermFullyFixedBounds
