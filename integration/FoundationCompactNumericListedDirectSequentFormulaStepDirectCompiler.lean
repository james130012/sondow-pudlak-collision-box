import integration.FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
import integration.FoundationCompactNumericListedDirectNatListWitnessRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds

/-!
# Direct PA compiler for one original sequent-formula step

Every one of the twenty-one right-nested conjuncts of the original
twenty-six-coordinate formula is compiled in the empty context.  The parser
child is the exact composite-state proof with the task-constant PA transport;
all remaining children use explicit hybrid certificates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListWitnessRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

structure EmptyContextBoundedProof (formula : ValuationFormula) where
  resource : Nat
  proof : CertifiedPAContextProof ∅ formula
  payloadLength_le : proof.payloadLength ≤ resource

namespace EmptyContextBoundedProof

noncomputable def conjunction
    {left right : ValuationFormula}
    (leftBound : EmptyContextBoundedProof left)
    (rightBound : EmptyContextBoundedProof right) :
    EmptyContextBoundedProof (left ⋏ right) := by
  let proof := CertifiedPAContextProof.conjunction
    leftBound.proof rightBound.proof
  let resource :=
    leftBound.resource + rightBound.resource +
      CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ left right
  refine { resource := resource, proof := proof, payloadLength_le := ?_ }
  have hassembly :=
    CertifiedPAContextProof.conjunction_payloadLength_le
      leftBound.proof rightBound.proof
  have hleft := leftBound.payloadLength_le
  have hright := rightBound.payloadLength_le
  exact hassembly.trans (by
    dsimp only [proof, resource]
    omega)

end EmptyContextBoundedProof

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol
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

private theorem arithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func,
    binaryFunctionTerm_freeVariables]

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticTwoTerm_freeVariables_eq_empty :
    (‘2’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

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

private noncomputable def valuationEqCertificate
    (leftTerm rightTerm : ValuationTerm)
    (heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm = !!rightTerm” :=
  CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq

private noncomputable def closeHybridCertificate
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (certificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula)
    (hclosed : formula.freeVariables = ∅) :
    CertifiedPAContextProof ∅ formula := by
  have hcontext :
      valuationContext formula.freeVariables valuation = ∅ := by
    rw [hclosed]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext certificate.compile

private noncomputable def boundedClosedHybridCertificate
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (certificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula)
    (hclosed : formula.freeVariables = ∅) :
    EmptyContextBoundedProof formula := by
  let proof := closeHybridCertificate certificate hclosed
  let resource :=
    CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
      certificate
  refine { resource := resource, proof := proof, payloadLength_le := ?_ }
  have hcompile :=
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      certificate
  change (closeHybridCertificate certificate hclosed).payloadLength ≤ resource
  unfold closeHybridCertificate
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact hcompile

private noncomputable def boundedClosedHybridCertificateWithPublicBound
    {valuation : Nat -> Nat} {formula : ValuationFormula}
    (certificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula)
    (hclosed : formula.freeVariables = ∅)
    (publicResource : Nat)
    (hpublic :
      CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
          certificate <=
        publicResource) :
    EmptyContextBoundedProof formula := by
  let structural := boundedClosedHybridCertificate certificate hclosed
  exact
    { resource := publicResource
      proof := structural.proof
      payloadLength_le := structural.payloadLength_le.trans hpublic }

private noncomputable def boundedParserProof
    {formula : ValuationFormula} {resource : Nat}
    (bound : ParserSyntaxExactBoundedClosedDirectBound formula resource) :
    EmptyContextBoundedProof formula where
  resource := resource
  proof := bound.proof
  payloadLength_le := bound.payloadLength_le

private theorem binaryRelationFormula_freeVariables_eq_empty
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (LO.FirstOrder.Semiformula.rel relationSymbol
      ![left, right]).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro candidate hcandidate
  rcases Finset.mem_biUnion.mp hcandidate with
    ⟨coordinate, _, hcoordinate⟩
  fin_cases coordinate <;>
    simp [hleft, hright] at hcoordinate

private theorem closedLeFormula_freeVariables_eq_empty
    (left right : Nat) :
    (“!!(shortBinaryNumeralTerm left) ≤
      !!(shortBinaryNumeralTerm right)” :
      ValuationFormula).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.Operator.le_def,
    LO.FirstOrder.Semiformula.freeVariables_or]
  have hequality :=
    binaryRelationFormula_freeVariables_eq_empty
      Language.Eq.eq (shortBinaryNumeralTerm left)
      (shortBinaryNumeralTerm right)
      (shortBinaryNumeralTerm_freeVariables_eq_empty left)
      (shortBinaryNumeralTerm_freeVariables_eq_empty right)
  have hstrict :=
    binaryRelationFormula_freeVariables_eq_empty
      Language.ORing.Rel.lt (shortBinaryNumeralTerm left)
      (shortBinaryNumeralTerm right)
      (shortBinaryNumeralTerm_freeVariables_eq_empty left)
      (shortBinaryNumeralTerm_freeVariables_eq_empty right)
  change
    (LO.FirstOrder.Semiformula.rel Language.Eq.eq
        ![shortBinaryNumeralTerm left,
          shortBinaryNumeralTerm right]).freeVariables ∪
      (LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm left,
          shortBinaryNumeralTerm right]).freeVariables = ∅
  rw [hequality, hstrict]
  simp

private noncomputable def compileClosedLe
    (left right : Nat) (hle : left ≤ right) :
    CertifiedPAContextProof ∅
      (“!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” : ValuationFormula) := by
  let certificate := valuationLeCertificate
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right) (by
      simpa [termValue_shortBinaryNumeralTerm] using hle)
  exact closeHybridCertificate certificate
    (closedLeFormula_freeVariables_eq_empty left right)

private noncomputable def boundedCompileClosedLe
    (left right : Nat) (hle : left ≤ right) :
    EmptyContextBoundedProof
      (“!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” : ValuationFormula) := by
  let certificate := valuationLeCertificate
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right) (by
      simpa [termValue_shortBinaryNumeralTerm] using hle)
  exact boundedClosedHybridCertificate certificate
    (closedLeFormula_freeVariables_eq_empty left right)

private noncomputable def boundedCompileClosedLePublic
    (left right : Nat) (hle : left ≤ right) :
    EmptyContextBoundedProof
      (“!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” : ValuationFormula) := by
  let leftTerm := shortBinaryNumeralTerm left
  let rightTerm := shortBinaryNumeralTerm right
  let certificate :=
    compactAdditiveNatListWitnessRowsLeCertificate leftTerm rightTerm (by
      simpa [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm] using hle)
  let publicResource :=
    witnessRowsValuationLeStructuralPayloadPolynomial leftTerm rightTerm
  have hpublic :=
    compactAdditiveNatListWitnessRowsLeCertificate_structuralPayloadBound_le_public
      leftTerm rightTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty left)
      (shortBinaryNumeralTerm_freeVariables_eq_empty right) (by
        simpa [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm] using hle)
  exact boundedClosedHybridCertificateWithPublicBound certificate
    (closedLeFormula_freeVariables_eq_empty left right) publicResource hpublic

private theorem fixedWidthEntryAtClosedTerms_freeVariables_eq_empty
    (table width value : Nat) (indexTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅) :
    (compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      indexTerm (shortBinaryNumeralTerm value)).freeVariables = ∅ := by
  unfold compactFixedWidthEntryAtValuationFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty table
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  · exact hindexClosed
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value

private noncomputable def compileFixedWidthEntryAtClosedTerms
    (table width index value : Nat) (indexTerm : ValuationTerm)
    (hindexValue : termValue zeroValuation indexTerm = index)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry table width index value) :
    CertifiedPAContextProof ∅
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        indexTerm (shortBinaryNumeralTerm value)) := by
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      indexTerm (shortBinaryNumeralTerm value) (by
        simpa [termValue_shortBinaryNumeralTerm, hindexValue] using hentry)
  exact closeHybridCertificate certificate
    (fixedWidthEntryAtClosedTerms_freeVariables_eq_empty table width value
      indexTerm hindexClosed)

private noncomputable def boundedCompileFixedWidthEntryAtClosedTerms
    (table width index value : Nat) (indexTerm : ValuationTerm)
    (hindexValue : termValue zeroValuation indexTerm = index)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry table width index value) :
    EmptyContextBoundedProof
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        indexTerm (shortBinaryNumeralTerm value)) := by
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
      (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
      indexTerm (shortBinaryNumeralTerm value) (by
        simpa [termValue_shortBinaryNumeralTerm, hindexValue] using hentry)
  exact boundedClosedHybridCertificate certificate
    (fixedWidthEntryAtClosedTerms_freeVariables_eq_empty table width value
      indexTerm hindexClosed)

private noncomputable def boundedCompileFixedWidthEntryAtClosedTermsPublic
    (table width index value : Nat) (indexTerm : ValuationTerm)
    (hindexValue : termValue zeroValuation indexTerm = index)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hentry : CompactFixedWidthEntry table width index value) :
    EmptyContextBoundedProof
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width)
        indexTerm (shortBinaryNumeralTerm value)) := by
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
      tableTerm widthTerm indexTerm valueTerm (by
        simpa [tableTerm, widthTerm, valueTerm,
          termValue_shortBinaryNumeralTerm, hindexValue] using hentry)
  let publicResource :=
    compactFixedWidthEntryAtValuationStructuralPayloadPolynomial zeroValuation
      tableTerm widthTerm indexTerm valueTerm
  have hpublic :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      zeroValuation tableTerm widthTerm indexTerm valueTerm
      (shortBinaryNumeralTerm_freeVariables_eq_empty table)
      (shortBinaryNumeralTerm_freeVariables_eq_empty width)
      hindexClosed
      (shortBinaryNumeralTerm_freeVariables_eq_empty value) (by
        simpa [tableTerm, widthTerm, valueTerm,
          termValue_shortBinaryNumeralTerm, hindexValue] using hentry)
  exact boundedClosedHybridCertificateWithPublicBound certificate
    (fixedWidthEntryAtClosedTerms_freeVariables_eq_empty table width value
      indexTerm hindexClosed) publicResource hpublic

private theorem natListWitnessRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat) :
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
      start count finish boundaryTable boundarySize).freeVariables = ∅ := by
  unfold compactAdditiveNatListWitnessRowsClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

private noncomputable def compileNatListWitnessRows
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat)
    (hrows : CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      start count finish boundaryTable boundarySize) :
    CertifiedPAContextProof ∅
      (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
        tokenCount start count finish boundaryTable boundarySize) := by
  let certificate :=
    compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start count finish boundaryTable boundarySize
      hrows
  exact closeHybridCertificate certificate
    (natListWitnessRowsClosedFormula_freeVariables_eq_empty tokenTable width
      tokenCount start count finish boundaryTable boundarySize)

private noncomputable def boundedCompileNatListWitnessRows
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat)
    (hrows : CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      start count finish boundaryTable boundarySize) :
    EmptyContextBoundedProof
      (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
        tokenCount start count finish boundaryTable boundarySize) := by
  let certificate :=
    compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start count finish boundaryTable boundarySize
      hrows
  exact boundedClosedHybridCertificate certificate
    (natListWitnessRowsClosedFormula_freeVariables_eq_empty tokenTable width
      tokenCount start count finish boundaryTable boundarySize)

private noncomputable def boundedCompileNatListWitnessRowsPublic
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat)
    (hrows : CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      start count finish boundaryTable boundarySize) :
    EmptyContextBoundedProof
      (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
        tokenCount start count finish boundaryTable boundarySize) := by
  let certificate :=
    compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start count finish boundaryTable boundarySize
      hrows
  let publicResource :=
    compactAdditiveNatListWitnessRowsPublicFinitePayloadEnvelope tokenTable
      width tokenCount start count finish boundaryTable boundarySize
  have hpublic :=
    compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount start count finish boundaryTable boundarySize
      hrows
  exact boundedClosedHybridCertificateWithPublicBound certificate
    (natListWitnessRowsClosedFormula_freeVariables_eq_empty tokenTable width
      tokenCount start count finish boundaryTable boundarySize)
    publicResource hpublic

private theorem natListAppendSlicesClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) :
    (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount).freeVariables = ∅ := by
  unfold compactAdditiveNatListAppendSlicesClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

private noncomputable def compileNatListAppendSlices
    (tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount) :
    CertifiedPAContextProof ∅
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount) := by
  let certificate :=
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount leftStart leftFinish leftCount rightStart
      rightFinish rightCount targetStart targetFinish targetCount hgraph
  exact closeHybridCertificate certificate
    (natListAppendSlicesClosedFormula_freeVariables_eq_empty tokenTable width
      tokenCount leftStart leftFinish leftCount rightStart rightFinish
      rightCount targetStart targetFinish targetCount)

private noncomputable def boundedCompileNatListAppendSlices
    (tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount) :
    EmptyContextBoundedProof
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount) := by
  let certificate :=
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount leftStart leftFinish leftCount rightStart
      rightFinish rightCount targetStart targetFinish targetCount hgraph
  exact boundedClosedHybridCertificate certificate
    (natListAppendSlicesClosedFormula_freeVariables_eq_empty tokenTable width
      tokenCount leftStart leftFinish leftCount rightStart rightFinish
      rightCount targetStart targetFinish targetCount)

private noncomputable def boundedCompileNatListAppendSlicesPublic
    (tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount) :
    EmptyContextBoundedProof
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount) := by
  let certificate :=
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph
      tokenTable width tokenCount leftStart leftFinish leftCount rightStart
      rightFinish rightCount targetStart targetFinish targetCount hgraph
  let publicResource :=
    compactAdditiveNatListAppendSlicesPublicFinitePayloadEnvelope tokenTable
      width tokenCount leftStart leftFinish leftCount rightStart rightFinish
      rightCount targetStart targetFinish targetCount
  have hpublic :=
    compactAdditiveNatListAppendSlicesExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
      tokenTable width tokenCount leftStart leftFinish leftCount rightStart
      rightFinish rightCount targetStart targetFinish targetCount hgraph
  exact boundedClosedHybridCertificateWithPublicBound certificate
    (natListAppendSlicesClosedFormula_freeVariables_eq_empty tokenTable width
      tokenCount leftStart leftFinish leftCount rightStart rightFinish
      rightCount targetStart targetFinish targetCount)
    publicResource hpublic

private theorem successorCountEquality_freeVariables_eq_empty
    (suffixCount valueCount : Nat) :
    (“!!(shortBinaryNumeralTerm suffixCount) =
      !!(shortBinaryNumeralTerm valueCount) + 1” :
      ValuationFormula).freeVariables = ∅ := by
  have hright :
      (‘!!(shortBinaryNumeralTerm valueCount) + 1’ :
        ValuationTerm).freeVariables = ∅ := by
    rw [arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  rw [LO.FirstOrder.Semiformula.Operator.eq_def]
  exact binaryRelationFormula_freeVariables_eq_empty Language.Eq.eq
    (shortBinaryNumeralTerm suffixCount)
    (‘!!(shortBinaryNumeralTerm valueCount) + 1’ : ValuationTerm)
    (shortBinaryNumeralTerm_freeVariables_eq_empty suffixCount) hright

private noncomputable def compileSuccessorCountEquality
    (suffixCount valueCount : Nat)
    (hequality : suffixCount = valueCount + 1) :
    CertifiedPAContextProof ∅
      (“!!(shortBinaryNumeralTerm suffixCount) =
        !!(shortBinaryNumeralTerm valueCount) + 1” :
        ValuationFormula) := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm valueCount) + 1’
  let certificate := valuationEqCertificate
    (shortBinaryNumeralTerm suffixCount) rightTerm (by
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne] using hequality)
  exact closeHybridCertificate certificate
    (successorCountEquality_freeVariables_eq_empty suffixCount valueCount)

private noncomputable def boundedCompileSuccessorCountEquality
    (suffixCount valueCount : Nat)
    (hequality : suffixCount = valueCount + 1) :
    EmptyContextBoundedProof
      (“!!(shortBinaryNumeralTerm suffixCount) =
        !!(shortBinaryNumeralTerm valueCount) + 1” :
        ValuationFormula) := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm valueCount) + 1’
  let certificate := valuationEqCertificate
    (shortBinaryNumeralTerm suffixCount) rightTerm (by
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne] using hequality)
  exact boundedClosedHybridCertificate certificate
    (successorCountEquality_freeVariables_eq_empty suffixCount valueCount)

private noncomputable def boundedCompileSuccessorCountEqualityPublic
    (suffixCount valueCount : Nat)
    (hequality : suffixCount = valueCount + 1) :
    EmptyContextBoundedProof
      (“!!(shortBinaryNumeralTerm suffixCount) =
        !!(shortBinaryNumeralTerm valueCount) + 1” :
        ValuationFormula) := by
  let leftTerm := shortBinaryNumeralTerm suffixCount
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm valueCount) + 1’
  let certificate := valuationEqCertificate leftTerm rightTerm (by
    simpa [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticOne] using hequality)
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let publicResource :=
    compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq args
  have hleft : leftTerm.freeVariables ⊆ {0} := by
    rw [show leftTerm = shortBinaryNumeralTerm suffixCount by rfl,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hrightClosed : rightTerm.freeVariables = ∅ := by
    rw [show rightTerm =
      (‘!!(shortBinaryNumeralTerm valueCount) + 1’ : ValuationTerm) by rfl]
    rw [arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hright : rightTerm.freeVariables ⊆ {0} := by
    rw [hrightClosed]
    simp
  have hpublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial zeroValuation
      Language.Eq.eq args hleft hright
  exact boundedClosedHybridCertificateWithPublicBound certificate
    (successorCountEquality_freeVariables_eq_empty suffixCount valueCount)
    publicResource (by
      change
        FoundationCompactPAValuationAtomicCompilerBounds.compilePositiveRelationPayloadResource
            zeroValuation Language.Eq.eq args <=
          publicResource
      exact hpublic)

def rightNestedConjunctionFormula :
    List ValuationFormula -> ValuationFormula
  | [] => ⊤
  | formula :: [] => formula
  | formula :: next :: rest =>
      formula ⋏ rightNestedConjunctionFormula (next :: rest)

def rightNestedEmptyContextPayloadEnvelope :
    List (ValuationFormula × Nat) -> Nat
  | [] => 0
  | (_, resource) :: [] => resource
  | (formula, resource) :: (next, nextResource) :: rest =>
      resource +
        rightNestedEmptyContextPayloadEnvelope
          ((next, nextResource) :: rest) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ formula
          (rightNestedConjunctionFormula
            (((next, nextResource) :: rest).map Prod.fst))

def compactSequentFormulaStepDirectPublicConjuncts
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    List (ValuationFormula × Nat) :=
  let indexTerm := shortBinaryNumeralTerm index
  let successorIndexTerm :=
    compactSequentFormulaStepIndexSuccessorTerm index
  let secondSuccessorIndexTerm :=
    compactSequentFormulaStepIndexSecondSuccessorTerm index
  let parserStateCount :=
    compactParserSyntaxExactFuel row.current.count + 1
  let successorCountTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm valueCount) + 1’
  [
    ((“!!(shortBinaryNumeralTerm row.current.start) ≤
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula),
      witnessRowsValuationLeStructuralPayloadPolynomial
        (shortBinaryNumeralTerm row.current.start)
        (shortBinaryNumeralTerm tokenCount)),
    ((“!!(shortBinaryNumeralTerm row.current.finish) ≤
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula),
      witnessRowsValuationLeStructuralPayloadPolynomial
        (shortBinaryNumeralTerm row.current.finish)
        (shortBinaryNumeralTerm tokenCount)),
    ((“!!(shortBinaryNumeralTerm row.current.count) ≤
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula),
      witnessRowsValuationLeStructuralPayloadPolynomial
        (shortBinaryNumeralTerm row.current.count)
        (shortBinaryNumeralTerm tokenCount)),
    ((“!!(shortBinaryNumeralTerm row.next.start) ≤
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula),
      witnessRowsValuationLeStructuralPayloadPolynomial
        (shortBinaryNumeralTerm row.next.start)
        (shortBinaryNumeralTerm tokenCount)),
    ((“!!(shortBinaryNumeralTerm row.next.finish) ≤
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula),
      witnessRowsValuationLeStructuralPayloadPolynomial
        (shortBinaryNumeralTerm row.next.finish)
        (shortBinaryNumeralTerm tokenCount)),
    ((“!!(shortBinaryNumeralTerm row.next.count) ≤
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula),
      witnessRowsValuationLeStructuralPayloadPolynomial
        (shortBinaryNumeralTerm row.next.count)
        (shortBinaryNumeralTerm tokenCount)),
    ((“!!(shortBinaryNumeralTerm row.value.start) ≤
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula),
      witnessRowsValuationLeStructuralPayloadPolynomial
        (shortBinaryNumeralTerm row.value.start)
        (shortBinaryNumeralTerm tokenCount)),
    ((“!!(shortBinaryNumeralTerm row.value.finish) ≤
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula),
      witnessRowsValuationLeStructuralPayloadPolynomial
        (shortBinaryNumeralTerm row.value.finish)
        (shortBinaryNumeralTerm tokenCount)),
    ((“!!(shortBinaryNumeralTerm row.value.count) ≤
        !!(shortBinaryNumeralTerm tokenCount)” : ValuationFormula),
      witnessRowsValuationLeStructuralPayloadPolynomial
        (shortBinaryNumeralTerm row.value.count)
        (shortBinaryNumeralTerm tokenCount)),
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm suffixBoundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm row.current.start),
      compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation (shortBinaryNumeralTerm suffixBoundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm row.current.start)),
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm suffixBoundary)
        (shortBinaryNumeralTerm tokenCount) successorIndexTerm
        (shortBinaryNumeralTerm row.current.finish),
      compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation (shortBinaryNumeralTerm suffixBoundary)
        (shortBinaryNumeralTerm tokenCount) successorIndexTerm
        (shortBinaryNumeralTerm row.current.finish)),
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm suffixBoundary)
        (shortBinaryNumeralTerm tokenCount) successorIndexTerm
        (shortBinaryNumeralTerm row.next.start),
      compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation (shortBinaryNumeralTerm suffixBoundary)
        (shortBinaryNumeralTerm tokenCount) successorIndexTerm
        (shortBinaryNumeralTerm row.next.start)),
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm suffixBoundary)
        (shortBinaryNumeralTerm tokenCount) secondSuccessorIndexTerm
        (shortBinaryNumeralTerm row.next.finish),
      compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation (shortBinaryNumeralTerm suffixBoundary)
        (shortBinaryNumeralTerm tokenCount) secondSuccessorIndexTerm
        (shortBinaryNumeralTerm row.next.finish)),
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm valueBoundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm row.value.start),
      compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation (shortBinaryNumeralTerm valueBoundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm row.value.start)),
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm valueBoundary)
        (shortBinaryNumeralTerm tokenCount) successorIndexTerm
        (shortBinaryNumeralTerm row.value.finish),
      compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation (shortBinaryNumeralTerm valueBoundary)
        (shortBinaryNumeralTerm tokenCount) successorIndexTerm
        (shortBinaryNumeralTerm row.value.finish)),
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
        row.current.start row.current.count row.current.finish
        row.current.boundary row.current.boundarySize,
      compactAdditiveNatListWitnessRowsPublicFinitePayloadEnvelope tokenTable
        width tokenCount row.current.start row.current.count
        row.current.finish row.current.boundary row.current.boundarySize),
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
        row.next.start row.next.count row.next.finish row.next.boundary
        row.next.boundarySize,
      compactAdditiveNatListWitnessRowsPublicFinitePayloadEnvelope tokenTable
        width tokenCount row.next.start row.next.count row.next.finish
        row.next.boundary row.next.boundarySize),
    (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width tokenCount
        row.value.start row.value.count row.value.finish row.value.boundary
        row.value.boundarySize,
      compactAdditiveNatListWitnessRowsPublicFinitePayloadEnvelope tokenTable
        width tokenCount row.value.start row.value.count row.value.finish
        row.value.boundary row.value.boundarySize),
    (compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
        row.parserStateBoundary row.current.boundary row.current.count
        row.next.boundary row.next.count row.parserTableWidth
        row.parserValueBound,
      compactSequentFormulaStepParserClosedDirectPayloadEnvelope tokenTable
        width tokenCount row.parserStateBoundary parserStateCount
        row.current.boundary row.current.count row.next.boundary row.next.count
        row.parserTableWidth row.parserValueBound),
    (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width tokenCount
        row.value.start row.value.finish row.value.count
        row.next.start row.next.finish row.next.count
        row.current.start row.current.finish row.current.count,
      compactAdditiveNatListAppendSlicesPublicFinitePayloadEnvelope tokenTable
        width tokenCount row.value.start row.value.finish row.value.count
        row.next.start row.next.finish row.next.count
        row.current.start row.current.finish row.current.count),
    ((“!!(shortBinaryNumeralTerm suffixCount) =
        !!(shortBinaryNumeralTerm valueCount) + 1” : ValuationFormula),
      compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq
        ![shortBinaryNumeralTerm suffixCount, successorCountTerm])
  ]

def compactSequentFormulaStepDirectPublicPayloadEnvelope
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  rightNestedEmptyContextPayloadEnvelope
    (compactSequentFormulaStepDirectPublicConjuncts tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount index row)

theorem compactSequentFormulaStepDirectPublicConjuncts_length
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    (compactSequentFormulaStepDirectPublicConjuncts tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount index row).length =
        21 := by
  rfl

theorem compactSequentFormulaStepDirectPublicConjuncts_formula_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    rightNestedConjunctionFormula
        ((compactSequentFormulaStepDirectPublicConjuncts tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount index
          row).map Prod.fst) =
      compactSequentFormulaStepDirectPartsFormula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount index row := by
  rfl

noncomputable def compactSequentFormulaStepDirectStructuralBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount index row) :
    EmptyContextBoundedProof
      (compactSequentFormulaStepDirectClosedFormula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount index row) := by
  rcases hgraph with
    ⟨hcurrentStart, hcurrentFinish, hcurrentCount,
      hnextStart, hnextFinish, hnextCount,
      hvalueStart, hvalueFinish, hvalueCount,
      hcurrentStartEntry, hcurrentFinishEntry,
      hnextStartEntry, hnextFinishEntry,
      hvalueStartEntry, hvalueFinishEntry,
      hcurrentRows, hnextRows, hvalueRows,
      hparser, happend, hcount⟩
  let proof01 :=
    boundedCompileClosedLePublic row.current.start tokenCount hcurrentStart
  let proof02 :=
    boundedCompileClosedLePublic row.current.finish tokenCount hcurrentFinish
  let proof03 :=
    boundedCompileClosedLePublic row.current.count tokenCount hcurrentCount
  let proof04 :=
    boundedCompileClosedLePublic row.next.start tokenCount hnextStart
  let proof05 :=
    boundedCompileClosedLePublic row.next.finish tokenCount hnextFinish
  let proof06 :=
    boundedCompileClosedLePublic row.next.count tokenCount hnextCount
  let proof07 :=
    boundedCompileClosedLePublic row.value.start tokenCount hvalueStart
  let proof08 :=
    boundedCompileClosedLePublic row.value.finish tokenCount hvalueFinish
  let proof09 :=
    boundedCompileClosedLePublic row.value.count tokenCount hvalueCount
  let indexTerm := shortBinaryNumeralTerm index
  let successorIndexTerm :=
    compactSequentFormulaStepIndexSuccessorTerm index
  let secondSuccessorIndexTerm :=
    compactSequentFormulaStepIndexSecondSuccessorTerm index
  have hindexValue : termValue zeroValuation indexTerm = index := by
    simp [indexTerm, termValue_shortBinaryNumeralTerm]
  have hsuccessorIndexValue :
      termValue zeroValuation successorIndexTerm = index + 1 := by
    simp [successorIndexTerm, compactSequentFormulaStepIndexSuccessorTerm,
      termValue_arithmeticAdd, termValue_arithmeticOne,
      termValue_shortBinaryNumeralTerm]
  have hsecondSuccessorIndexValue :
      termValue zeroValuation secondSuccessorIndexTerm = index + 2 := by
    simp [secondSuccessorIndexTerm,
      compactSequentFormulaStepIndexSecondSuccessorTerm,
      termValue_arithmeticAdd, termValue_arithmeticTwo,
      termValue_shortBinaryNumeralTerm]
  have hindexClosed : indexTerm.freeVariables = ∅ := by
    exact shortBinaryNumeralTerm_freeVariables_eq_empty index
  have hsuccessorIndexClosed : successorIndexTerm.freeVariables = ∅ := by
    rw [show successorIndexTerm =
        (‘!!(shortBinaryNumeralTerm index) + 1’ : ValuationTerm) by rfl]
    rw [arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticOneTerm_freeVariables_eq_empty]
    simp
  have hsecondSuccessorIndexClosed :
      secondSuccessorIndexTerm.freeVariables = ∅ := by
    rw [show secondSuccessorIndexTerm =
        (‘!!(shortBinaryNumeralTerm index) + 2’ : ValuationTerm) by rfl]
    rw [arithmeticAddTerm_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticTwoTerm_freeVariables_eq_empty]
    simp
  let proof10 := boundedCompileFixedWidthEntryAtClosedTermsPublic
    suffixBoundary tokenCount
    index row.current.start indexTerm hindexValue hindexClosed
    hcurrentStartEntry
  let proof11 := boundedCompileFixedWidthEntryAtClosedTermsPublic
    suffixBoundary tokenCount
    (index + 1) row.current.finish successorIndexTerm hsuccessorIndexValue
    hsuccessorIndexClosed hcurrentFinishEntry
  let proof12 := boundedCompileFixedWidthEntryAtClosedTermsPublic
    suffixBoundary tokenCount
    (index + 1) row.next.start successorIndexTerm hsuccessorIndexValue
    hsuccessorIndexClosed hnextStartEntry
  let proof13 := boundedCompileFixedWidthEntryAtClosedTermsPublic
    suffixBoundary tokenCount
    (index + 2) row.next.finish secondSuccessorIndexTerm
    hsecondSuccessorIndexValue hsecondSuccessorIndexClosed hnextFinishEntry
  let proof14 := boundedCompileFixedWidthEntryAtClosedTermsPublic
    valueBoundary tokenCount
    index row.value.start indexTerm hindexValue hindexClosed hvalueStartEntry
  let proof15 := boundedCompileFixedWidthEntryAtClosedTermsPublic
    valueBoundary tokenCount
    (index + 1) row.value.finish successorIndexTerm hsuccessorIndexValue
    hsuccessorIndexClosed hvalueFinishEntry
  let proof16 := boundedCompileNatListWitnessRowsPublic tokenTable width tokenCount
    row.current.start row.current.count row.current.finish
    row.current.boundary row.current.boundarySize hcurrentRows
  let proof17 := boundedCompileNatListWitnessRowsPublic tokenTable width tokenCount
    row.next.start row.next.count row.next.finish row.next.boundary
    row.next.boundarySize hnextRows
  let proof18 := boundedCompileNatListWitnessRowsPublic tokenTable width tokenCount
    row.value.start row.value.count row.value.finish row.value.boundary
    row.value.boundarySize hvalueRows
  let parserStateCount := compactParserSyntaxExactFuel row.current.count + 1
  have hparser' : CompactParserSyntaxExactBoundedGraph tokenTable width
      tokenCount row.parserStateBoundary parserStateCount
      row.current.boundary row.current.count row.next.boundary row.next.count
      1 0 0 row.parserTableWidth row.parserValueBound := by
    simpa [parserStateCount, compactParserSyntaxExactFuel] using hparser
  let parserBound := compactSequentFormulaStepParserClosedDirectBoundOfGraph
    tokenTable width tokenCount row.parserStateBoundary parserStateCount
    row.current.boundary row.current.count row.next.boundary row.next.count
    row.parserTableWidth row.parserValueBound hparser'
  let proof19 := boundedParserProof parserBound
  let proof20 :=
    boundedCompileNatListAppendSlicesPublic tokenTable width tokenCount
    row.value.start row.value.finish row.value.count
    row.next.start row.next.finish row.next.count
    row.current.start row.current.finish row.current.count happend
  let proof21 :=
    boundedCompileSuccessorCountEqualityPublic suffixCount valueCount hcount
  let tail20 := EmptyContextBoundedProof.conjunction proof20 proof21
  let tail19 := EmptyContextBoundedProof.conjunction proof19 tail20
  let tail18 := EmptyContextBoundedProof.conjunction proof18 tail19
  let tail17 := EmptyContextBoundedProof.conjunction proof17 tail18
  let tail16 := EmptyContextBoundedProof.conjunction proof16 tail17
  let tail15 := EmptyContextBoundedProof.conjunction proof15 tail16
  let tail14 := EmptyContextBoundedProof.conjunction proof14 tail15
  let tail13 := EmptyContextBoundedProof.conjunction proof13 tail14
  let tail12 := EmptyContextBoundedProof.conjunction proof12 tail13
  let tail11 := EmptyContextBoundedProof.conjunction proof11 tail12
  let tail10 := EmptyContextBoundedProof.conjunction proof10 tail11
  let tail09 := EmptyContextBoundedProof.conjunction proof09 tail10
  let tail08 := EmptyContextBoundedProof.conjunction proof08 tail09
  let tail07 := EmptyContextBoundedProof.conjunction proof07 tail08
  let tail06 := EmptyContextBoundedProof.conjunction proof06 tail07
  let tail05 := EmptyContextBoundedProof.conjunction proof05 tail06
  let tail04 := EmptyContextBoundedProof.conjunction proof04 tail05
  let tail03 := EmptyContextBoundedProof.conjunction proof03 tail04
  let tail02 := EmptyContextBoundedProof.conjunction proof02 tail03
  let assembled := EmptyContextBoundedProof.conjunction proof01 tail02
  let finalProof := CertifiedPAContextProof.cast
    (compactSequentFormulaStepDirectClosedFormula_alignment tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount index
      row).symm
    assembled.proof
  refine
    { resource :=
        compactSequentFormulaStepDirectPublicPayloadEnvelope tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount index
          row
      proof := finalProof
      payloadLength_le := ?_ }
  have hassembled := assembled.payloadLength_le
  change finalProof.payloadLength <= _
  rw [show finalProof.payloadLength = assembled.proof.payloadLength by
    exact CertifiedPAContextProof.cast_payloadLength _ _]
  simpa only [
    assembled, tail02, tail03, tail04, tail05, tail06, tail07, tail08,
    tail09, tail10, tail11, tail12, tail13, tail14, tail15, tail16, tail17,
    tail18, tail19, tail20, EmptyContextBoundedProof.conjunction,
    compactSequentFormulaStepDirectPublicPayloadEnvelope,
    compactSequentFormulaStepDirectPublicConjuncts,
    rightNestedEmptyContextPayloadEnvelope, rightNestedConjunctionFormula,
    List.map, Prod.fst,
    proof01, proof02, proof03, proof04, proof05, proof06, proof07, proof08,
    proof09, proof10, proof11, proof12, proof13, proof14, proof15, proof16,
    proof17, proof18, proof19, proof20, proof21,
    boundedCompileClosedLePublic,
    boundedCompileFixedWidthEntryAtClosedTermsPublic,
    boundedCompileNatListWitnessRowsPublic, boundedParserProof,
    boundedCompileNatListAppendSlicesPublic,
    boundedCompileSuccessorCountEqualityPublic,
    boundedClosedHybridCertificateWithPublicBound,
    indexTerm, successorIndexTerm, secondSuccessorIndexTerm,
    parserStateCount] using hassembled

noncomputable def compactSequentFormulaStepDirectProofOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount index row) :
    CertifiedPAContextProof ∅
      (compactSequentFormulaStepDirectClosedFormula tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount index row) :=
  (compactSequentFormulaStepDirectStructuralBoundOfGraph tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount index row
    hgraph).proof

theorem compactSequentFormulaStepDirectStructuralBoundOfGraph_resource_eq_public
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount index row) :
    (compactSequentFormulaStepDirectStructuralBoundOfGraph tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount index
        row hgraph).resource =
      compactSequentFormulaStepDirectPublicPayloadEnvelope tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount index
        row := by
  rcases hgraph with
    ⟨hcurrentStart, hcurrentFinish, hcurrentCount,
      hnextStart, hnextFinish, hnextCount,
      hvalueStart, hvalueFinish, hvalueCount,
      hcurrentStartEntry, hcurrentFinishEntry,
      hnextStartEntry, hnextFinishEntry,
      hvalueStartEntry, hvalueFinishEntry,
      hcurrentRows, hnextRows, hvalueRows,
      hparser, happend, hcount⟩
  simp only [compactSequentFormulaStepDirectStructuralBoundOfGraph]

theorem compactSequentFormulaStepDirectProofOfGraph_payloadLength_le_public
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount index row) :
    (compactSequentFormulaStepDirectProofOfGraph tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount index row
        hgraph).payloadLength <=
      compactSequentFormulaStepDirectPublicPayloadEnvelope tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount index
        row := by
  have hbound :=
    (compactSequentFormulaStepDirectStructuralBoundOfGraph tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount index row
    hgraph).payloadLength_le
  rw [
    compactSequentFormulaStepDirectStructuralBoundOfGraph_resource_eq_public
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount index row hgraph] at hbound
  exact hbound

/-! Public leaf bounds reused by the open-index row compiler. -/

noncomputable def compactSequentFormulaStepClosedLePublicBound
    (left right : Nat) (hle : left ≤ right) :
    EmptyContextBoundedProof
      (“!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” : ValuationFormula) :=
  boundedCompileClosedLePublic left right hle

noncomputable def compactSequentFormulaStepNatListWitnessRowsPublicBound
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat)
    (hrows : CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      start count finish boundaryTable boundarySize) :
    EmptyContextBoundedProof
      (compactAdditiveNatListWitnessRowsClosedFormula tokenTable width
        tokenCount start count finish boundaryTable boundarySize) :=
  boundedCompileNatListWitnessRowsPublic tokenTable width tokenCount start
    count finish boundaryTable boundarySize hrows

noncomputable def compactSequentFormulaStepNatListAppendSlicesPublicBound
    (tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount) :
    EmptyContextBoundedProof
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount) :=
  boundedCompileNatListAppendSlicesPublic tokenTable width tokenCount
    leftStart leftFinish leftCount rightStart rightFinish rightCount
    targetStart targetFinish targetCount hgraph

noncomputable def compactSequentFormulaStepSuccessorCountPublicBound
    (suffixCount valueCount : Nat)
    (hequality : suffixCount = valueCount + 1) :
    EmptyContextBoundedProof
      (“!!(shortBinaryNumeralTerm suffixCount) =
        !!(shortBinaryNumeralTerm valueCount) + 1” :
        ValuationFormula) :=
  boundedCompileSuccessorCountEqualityPublic suffixCount valueCount hequality

#print axioms compactSequentFormulaStepDirectPublicConjuncts_length
#print axioms compactSequentFormulaStepDirectPublicConjuncts_formula_alignment
#print axioms compactSequentFormulaStepDirectStructuralBoundOfGraph
#print axioms compactSequentFormulaStepDirectProofOfGraph
#print axioms
  compactSequentFormulaStepDirectStructuralBoundOfGraph_resource_eq_public
#print axioms
  compactSequentFormulaStepDirectProofOfGraph_payloadLength_le_public
#print axioms compactSequentFormulaStepClosedLePublicBound
#print axioms compactSequentFormulaStepNatListWitnessRowsPublicBound
#print axioms compactSequentFormulaStepNatListAppendSlicesPublicBound
#print axioms compactSequentFormulaStepSuccessorCountPublicBound

end FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
