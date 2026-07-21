import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds

/-!
# Public structural resources for binary-Nat status terminals

The first endpoint closes the running terminal by instantiating the public
additive-token-cell compiler at closed short numerals.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTokenCellValuationPublicBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation

private theorem arithmeticZeroTerm_freeVariables_eq_empty :
    (‘0’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_zero,
    LO.FirstOrder.Semiterm.Operator.Zero.term_eq]

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem binaryFunctionTerm_freeVariables
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
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

private theorem arithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]).freeVariables =
      left.freeVariables ∪ right.freeVariables
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem termValue_arithmeticZero :
    termValue zeroValuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero zeroValuation ![]

private theorem termValue_arithmeticOne :
    termValue zeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one zeroValuation ![]

def boundedWitnessGuardStructuralPayloadPolynomial
    (value bound : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial zeroValuation
    Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm value,
      (‘!!(shortBinaryNumeralTerm bound) + 1’ : ValuationTerm)]

theorem boundedWitnessGuardCertificate_structuralPayloadBound_le_public
    (value bound : Nat) (hvalue : value ≤ bound) :
    hybridFormulaStructuralPayloadBound
        (boundedWitnessGuardCertificate value bound hvalue) ≤
      boundedWitnessGuardStructuralPayloadPolynomial value bound := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  let args : Fin 2 -> ValuationTerm :=
    ![shortBinaryNumeralTerm value, rightTerm]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm value).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change rightTerm.freeVariables ⊆ {0}
    rw [show rightTerm.freeVariables = ∅ by
      dsimp only [rightTerm]
      rw [arithmeticAddTerm_freeVariables,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        arithmeticOneTerm_freeVariables_eq_empty]
      simp]
    simp
  have hpublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      zeroValuation Language.ORing.Rel.lt args hfirst hsecond
  change compilePositiveRelationPayloadResource zeroValuation
      Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm value,
        (‘!!(shortBinaryNumeralTerm bound) + 1’ : ValuationTerm)] ≤ _
  unfold boundedWitnessGuardStructuralPayloadPolynomial
  dsimp only [args, rightTerm] at hpublic ⊢
  exact hpublic

def closedLtStructuralPayloadPolynomial (left right : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial zeroValuation
    Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right]

theorem closedLtCertificate_structuralPayloadBound_le_public
    (left right : Nat) (hlt : left < right) :
    hybridFormulaStructuralPayloadBound
        (FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.closedLtCertificate
          left right hlt) ≤
      closedLtStructuralPayloadPolynomial left right := by
  have hfirst : (shortBinaryNumeralTerm left).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (shortBinaryNumeralTerm right).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right]
      hfirst hsecond
  change compilePositiveRelationPayloadResource zeroValuation
      Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] ≤ _
  unfold closedLtStructuralPayloadPolynomial
  exact hpublic

def successorEqualityStructuralPayloadPolynomial
    (left right : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm right,
      (‘!!(shortBinaryNumeralTerm left) + 1’ : ValuationTerm)]

theorem successorEqualityCertificate_structuralPayloadBound_le_public
    (left right : Nat) (hsuccessor : right = left + 1) :
    hybridFormulaStructuralPayloadBound
        (successorEqualityCertificate left right hsuccessor) ≤
      successorEqualityStructuralPayloadPolynomial left right := by
  let successorTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm left) + 1’
  let args : Fin 2 -> ValuationTerm :=
    ![shortBinaryNumeralTerm right, successorTerm]
  have hfirst : (args 0).freeVariables ⊆ {0} := by
    change (shortBinaryNumeralTerm right).freeVariables ⊆ {0}
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hsecond : (args 1).freeVariables ⊆ {0} := by
    change successorTerm.freeVariables ⊆ {0}
    rw [show successorTerm.freeVariables = ∅ by
      dsimp only [successorTerm]
      rw [arithmeticAddTerm_freeVariables,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        arithmeticOneTerm_freeVariables_eq_empty]
      simp]
    simp
  have hpublic :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      zeroValuation Language.Eq.eq args hfirst hsecond
  change compilePositiveRelationPayloadResource zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm right,
        (‘!!(shortBinaryNumeralTerm left) + 1’ : ValuationTerm)] ≤ _
  unfold successorEqualityStructuralPayloadPolynomial
  dsimp only [args, successorTerm] at hpublic ⊢
  exact hpublic

def sevenLeafRightConjunctionStructuralPayloadEnvelope
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 formula4 formula5 formula6 formula7 :
      ValuationFormula)
    (resource1 resource2 resource3 resource4 resource5 resource6 resource7 :
      Nat) : Nat :=
  let resource67 := hybridConjunctionStructuralPayloadEnvelope valuation
    formula6 formula7 resource6 resource7
  let resource567 := hybridConjunctionStructuralPayloadEnvelope valuation
    formula5 (formula6 ⋏ formula7) resource5 resource67
  let resource4567 := hybridConjunctionStructuralPayloadEnvelope valuation
    formula4 (formula5 ⋏ (formula6 ⋏ formula7)) resource4 resource567
  let resource34567 := hybridConjunctionStructuralPayloadEnvelope valuation
    formula3 (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7)))
    resource3 resource4567
  let resource234567 := hybridConjunctionStructuralPayloadEnvelope valuation
    formula2
    (formula3 ⋏ (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))))
    resource2 resource34567
  hybridConjunctionStructuralPayloadEnvelope valuation formula1
    (formula2 ⋏
      (formula3 ⋏ (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7)))))
    resource1 resource234567

theorem sevenLeafRightConjunctionStructuralPayloadBound_le_envelope
    {valuation : Nat -> Nat}
    {formula1 formula2 formula3 formula4 formula5 formula6 formula7 :
      ValuationFormula}
    (certificate1 : CheckedHybridValuationBoundedFormulaCertificate
      valuation formula1)
    (certificate2 : CheckedHybridValuationBoundedFormulaCertificate
      valuation formula2)
    (certificate3 : CheckedHybridValuationBoundedFormulaCertificate
      valuation formula3)
    (certificate4 : CheckedHybridValuationBoundedFormulaCertificate
      valuation formula4)
    (certificate5 : CheckedHybridValuationBoundedFormulaCertificate
      valuation formula5)
    (certificate6 : CheckedHybridValuationBoundedFormulaCertificate
      valuation formula6)
    (certificate7 : CheckedHybridValuationBoundedFormulaCertificate
      valuation formula7)
    (resource1 resource2 resource3 resource4 resource5 resource6 resource7 :
      Nat)
    (hresource1 : hybridFormulaStructuralPayloadBound certificate1 ≤ resource1)
    (hresource2 : hybridFormulaStructuralPayloadBound certificate2 ≤ resource2)
    (hresource3 : hybridFormulaStructuralPayloadBound certificate3 ≤ resource3)
    (hresource4 : hybridFormulaStructuralPayloadBound certificate4 ≤ resource4)
    (hresource5 : hybridFormulaStructuralPayloadBound certificate5 ≤ resource5)
    (hresource6 : hybridFormulaStructuralPayloadBound certificate6 ≤ resource6)
    (hresource7 : hybridFormulaStructuralPayloadBound certificate7 ≤ resource7) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          certificate1
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            certificate2
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              certificate3
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                certificate4
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  certificate5
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    certificate6 certificate7)))))) ≤
      sevenLeafRightConjunctionStructuralPayloadEnvelope valuation
        formula1 formula2 formula3 formula4 formula5 formula6 formula7
        resource1 resource2 resource3 resource4 resource5 resource6 resource7 := by
  have h67 := hybridConjunctionStructuralPayloadBound_le_envelope
    certificate6 certificate7 resource6 resource7 hresource6 hresource7
  have h567 := hybridConjunctionStructuralPayloadBound_le_envelope
    certificate5
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      certificate6 certificate7)
    resource5
    (hybridConjunctionStructuralPayloadEnvelope valuation
      formula6 formula7 resource6 resource7)
    hresource5 h67
  have h4567 := hybridConjunctionStructuralPayloadBound_le_envelope
    certificate4
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      certificate5
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        certificate6 certificate7))
    resource4
    (hybridConjunctionStructuralPayloadEnvelope valuation formula5
      (formula6 ⋏ formula7) resource5
      (hybridConjunctionStructuralPayloadEnvelope valuation
        formula6 formula7 resource6 resource7))
    hresource4 h567
  have h34567 := hybridConjunctionStructuralPayloadBound_le_envelope
    certificate3
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      certificate4
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        certificate5
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          certificate6 certificate7)))
    resource3
    (hybridConjunctionStructuralPayloadEnvelope valuation formula4
      (formula5 ⋏ (formula6 ⋏ formula7)) resource4
      (hybridConjunctionStructuralPayloadEnvelope valuation formula5
        (formula6 ⋏ formula7) resource5
        (hybridConjunctionStructuralPayloadEnvelope valuation
          formula6 formula7 resource6 resource7)))
    hresource3 h4567
  have h234567 := hybridConjunctionStructuralPayloadBound_le_envelope
    certificate2
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      certificate3
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        certificate4
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          certificate5
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            certificate6 certificate7))))
    resource2
    (hybridConjunctionStructuralPayloadEnvelope valuation formula3
      (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))) resource3
      (hybridConjunctionStructuralPayloadEnvelope valuation formula4
        (formula5 ⋏ (formula6 ⋏ formula7)) resource4
        (hybridConjunctionStructuralPayloadEnvelope valuation formula5
          (formula6 ⋏ formula7) resource5
          (hybridConjunctionStructuralPayloadEnvelope valuation
            formula6 formula7 resource6 resource7))))
    hresource2 h34567
  have h1234567 := hybridConjunctionStructuralPayloadBound_le_envelope
    certificate1
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      certificate2
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        certificate3
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          certificate4
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            certificate5
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              certificate6 certificate7)))))
    resource1
    (hybridConjunctionStructuralPayloadEnvelope valuation formula2
      (formula3 ⋏ (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))))
      resource2
      (hybridConjunctionStructuralPayloadEnvelope valuation formula3
        (formula4 ⋏ (formula5 ⋏ (formula6 ⋏ formula7))) resource3
        (hybridConjunctionStructuralPayloadEnvelope valuation formula4
          (formula5 ⋏ (formula6 ⋏ formula7)) resource4
          (hybridConjunctionStructuralPayloadEnvelope valuation formula5
            (formula6 ⋏ formula7) resource5
            (hybridConjunctionStructuralPayloadEnvelope valuation
              formula6 formula7 resource6 resource7)))))
    hresource1 h234567
  unfold sevenLeafRightConjunctionStructuralPayloadEnvelope
  dsimp only
  exact h1234567

def compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial
    (tokenTable width tokenCount start finish : Nat) : Nat :=
  compactAdditiveTokenCellAtValuationStructuralPayloadPolynomial
    (shortBinaryNumeralTerm tokenTable)
    (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (shortBinaryNumeralTerm start)
    (‘0’ : ValuationTerm)
    (shortBinaryNumeralTerm finish)

theorem
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount start finish : Nat)
    (hgraph : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start finish hgraph) ≤
      compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial
        tokenTable width tokenCount start finish := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let countTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm start
  let valueTerm : ValuationTerm := ‘0’
  let finishTerm := shortBinaryNumeralTerm finish
  have hclosedShort (value : Nat) :
      (shortBinaryNumeralTerm value).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty value
  have hcell : CompactAdditiveTokenCell
      (termValue zeroValuation tableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation countTerm)
      (termValue zeroValuation startTerm)
      (termValue zeroValuation valueTerm)
      (termValue zeroValuation finishTerm) := by
    dsimp only [tableTerm, widthTerm, countTerm, startTerm, valueTerm,
      finishTerm]
    simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticZero,
      CompactBinaryNatRunningStatusSlice, zeroValuation] using hgraph
  have hpublic :=
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      tableTerm widthTerm countTerm startTerm valueTerm finishTerm
      (hclosedShort tokenTable) (hclosedShort width)
      (hclosedShort tokenCount) (hclosedShort start)
      arithmeticZeroTerm_freeVariables_eq_empty (hclosedShort finish) hcell
  change hybridFormulaStructuralPayloadBound
      (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
        tableTerm widthTerm countTerm startTerm valueTerm finishTerm hcell) ≤ _
  unfold compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial
  dsimp only [tableTerm, widthTerm, countTerm, startTerm, valueTerm,
    finishTerm] at hpublic ⊢
  exact hpublic

def compactBinaryNatDoubleStatusPostWitnessStructuralPayloadPolynomial
    (tokenTable width tokenCount start endpoint innerStart : Nat)
    (lastValueTerm : ValuationTerm) : Nat :=
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let countTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm start
  let endpointTerm := shortBinaryNumeralTerm endpoint
  let innerTerm := shortBinaryNumeralTerm innerStart
  let oneTerm : ValuationTerm := ‘1’
  let guardFormula : ValuationFormula :=
    “!!innerTerm < !!countTerm + 1”
  let startLtFormula : ValuationFormula :=
    “!!startTerm < !!countTerm”
  let firstSuccessorFormula : ValuationFormula :=
    “!!innerTerm = !!startTerm + 1”
  let firstEntryFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm startTerm oneTerm
  let innerLtFormula : ValuationFormula :=
    “!!innerTerm < !!countTerm”
  let secondSuccessorFormula : ValuationFormula :=
    “!!endpointTerm = !!innerTerm + 1”
  let secondEntryFormula := compactFixedWidthEntryAtValuationFormula
    tableTerm widthTerm innerTerm lastValueTerm
  sevenLeafRightConjunctionStructuralPayloadEnvelope zeroValuation
    guardFormula startLtFormula firstSuccessorFormula firstEntryFormula
    innerLtFormula secondSuccessorFormula secondEntryFormula
    (boundedWitnessGuardStructuralPayloadPolynomial innerStart tokenCount)
    (closedLtStructuralPayloadPolynomial start tokenCount)
    (successorEqualityStructuralPayloadPolynomial start innerStart)
    (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
      zeroValuation tableTerm widthTerm startTerm oneTerm)
    (closedLtStructuralPayloadPolynomial innerStart tokenCount)
    (successorEqualityStructuralPayloadPolynomial innerStart endpoint)
    (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
      zeroValuation tableTerm widthTerm innerTerm lastValueTerm)

def compactBinaryNatFailedStatusSlicePostWitnessStructuralPayloadPolynomial
    (tokenTable width tokenCount start finish innerStart : Nat) : Nat :=
  compactBinaryNatDoubleStatusPostWitnessStructuralPayloadPolynomial
    tokenTable width tokenCount start finish innerStart
    (‘0’ : ValuationTerm)

theorem
    compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount start finish innerStart : Nat)
    (hinner : innerStart ≤ tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 0 finish) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate
          tokenTable width tokenCount start finish innerStart hinner) ≤
      compactBinaryNatFailedStatusSlicePostWitnessStructuralPayloadPolynomial
        tokenTable width tokenCount start finish innerStart := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let countTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm start
  let finishTerm := shortBinaryNumeralTerm finish
  let innerTerm := shortBinaryNumeralTerm innerStart
  let oneTerm : ValuationTerm := ‘1’
  let zeroTerm : ValuationTerm := ‘0’
  let guardCertificate :=
    boundedWitnessGuardCertificate innerStart tokenCount hinner.1
  let startLtCertificate :=
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.closedLtCertificate
      start tokenCount hinner.2.1.1
  let firstSuccessorCertificate :=
    successorEqualityCertificate start innerStart hinner.2.1.2.1
  have hfirstEntry : CompactFixedWidthEntry
      (termValue zeroValuation tableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation startTerm)
      (termValue zeroValuation oneTerm) := by
    dsimp only [tableTerm, widthTerm, startTerm, oneTerm]
    simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticOne,
      zeroValuation] using hinner.2.1.2.2
  let firstEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
      tableTerm widthTerm startTerm oneTerm hfirstEntry
  let innerLtCertificate :=
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.closedLtCertificate
      innerStart tokenCount hinner.2.2.1
  let secondSuccessorCertificate :=
    successorEqualityCertificate innerStart finish hinner.2.2.2.1
  have hsecondEntry : CompactFixedWidthEntry
      (termValue zeroValuation tableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation innerTerm)
      (termValue zeroValuation zeroTerm) := by
    dsimp only [tableTerm, widthTerm, innerTerm, zeroTerm]
    simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticZero,
      zeroValuation] using hinner.2.2.2.2
  let secondEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
      tableTerm widthTerm innerTerm zeroTerm hsecondEntry
  have hclosedShort (value : Nat) :
      (shortBinaryNumeralTerm value).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty value
  have hguard :=
    boundedWitnessGuardCertificate_structuralPayloadBound_le_public
      innerStart tokenCount hinner.1
  have hstartLt := closedLtCertificate_structuralPayloadBound_le_public
    start tokenCount hinner.2.1.1
  have hfirstSuccessor :=
    successorEqualityCertificate_structuralPayloadBound_le_public
      start innerStart hinner.2.1.2.1
  have hfirstEntryPublic :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      zeroValuation tableTerm widthTerm startTerm oneTerm
      (hclosedShort tokenTable) (hclosedShort width) (hclosedShort start)
      arithmeticOneTerm_freeVariables_eq_empty hfirstEntry
  have hinnerLt := closedLtCertificate_structuralPayloadBound_le_public
    innerStart tokenCount hinner.2.2.1
  have hsecondSuccessor :=
    successorEqualityCertificate_structuralPayloadBound_le_public
      innerStart finish hinner.2.2.2.1
  have hsecondEntryPublic :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      zeroValuation tableTerm widthTerm innerTerm zeroTerm
      (hclosedShort tokenTable) (hclosedShort width) (hclosedShort innerStart)
      arithmeticZeroTerm_freeVariables_eq_empty hsecondEntry
  have hseven :=
    sevenLeafRightConjunctionStructuralPayloadBound_le_envelope
      guardCertificate startLtCertificate firstSuccessorCertificate
      firstEntryCertificate innerLtCertificate secondSuccessorCertificate
      secondEntryCertificate
      (boundedWitnessGuardStructuralPayloadPolynomial innerStart tokenCount)
      (closedLtStructuralPayloadPolynomial start tokenCount)
      (successorEqualityStructuralPayloadPolynomial start innerStart)
      (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation tableTerm widthTerm startTerm oneTerm)
      (closedLtStructuralPayloadPolynomial innerStart tokenCount)
      (successorEqualityStructuralPayloadPolynomial innerStart finish)
      (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation tableTerm widthTerm innerTerm zeroTerm)
      hguard hstartLt hfirstSuccessor hfirstEntryPublic hinnerLt
      hsecondSuccessor hsecondEntryPublic
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        guardCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          startLtCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            firstSuccessorCertificate
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              firstEntryCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                innerLtCertificate
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  secondSuccessorCertificate secondEntryCertificate)))))) ≤ _
  unfold compactBinaryNatFailedStatusSlicePostWitnessStructuralPayloadPolynomial
    compactBinaryNatDoubleStatusPostWitnessStructuralPayloadPolynomial
  dsimp only [tableTerm, widthTerm, countTerm, startTerm, finishTerm,
    innerTerm, oneTerm, zeroTerm]
  exact hseven

def compactBinaryNatCompletedStatusPrefixPostWitnessStructuralPayloadPolynomial
    (tokenTable width tokenCount start outputStart innerStart : Nat) : Nat :=
  compactBinaryNatDoubleStatusPostWitnessStructuralPayloadPolynomial
    tokenTable width tokenCount start outputStart innerStart
    (‘1’ : ValuationTerm)

theorem
    compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount start outputStart innerStart : Nat)
    (hinner : innerStart ≤ tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 1 outputStart) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate
          tokenTable width tokenCount start outputStart innerStart hinner) ≤
      compactBinaryNatCompletedStatusPrefixPostWitnessStructuralPayloadPolynomial
        tokenTable width tokenCount start outputStart innerStart := by
  let tableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let countTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm start
  let outputStartTerm := shortBinaryNumeralTerm outputStart
  let innerTerm := shortBinaryNumeralTerm innerStart
  let oneTerm : ValuationTerm := ‘1’
  let guardCertificate :=
    boundedWitnessGuardCertificate innerStart tokenCount hinner.1
  let startLtCertificate :=
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.closedLtCertificate
      start tokenCount hinner.2.1.1
  let firstSuccessorCertificate :=
    successorEqualityCertificate start innerStart hinner.2.1.2.1
  have hfirstEntry : CompactFixedWidthEntry
      (termValue zeroValuation tableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation startTerm)
      (termValue zeroValuation oneTerm) := by
    dsimp only [tableTerm, widthTerm, startTerm, oneTerm]
    simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticOne,
      zeroValuation] using hinner.2.1.2.2
  let firstEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
      tableTerm widthTerm startTerm oneTerm hfirstEntry
  let innerLtCertificate :=
    FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.closedLtCertificate
      innerStart tokenCount hinner.2.2.1
  let secondSuccessorCertificate :=
    successorEqualityCertificate innerStart outputStart hinner.2.2.2.1
  have hsecondEntry : CompactFixedWidthEntry
      (termValue zeroValuation tableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation innerTerm)
      (termValue zeroValuation oneTerm) := by
    dsimp only [tableTerm, widthTerm, innerTerm, oneTerm]
    simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticOne,
      zeroValuation] using hinner.2.2.2.2
  let secondEntryCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate zeroValuation
      tableTerm widthTerm innerTerm oneTerm hsecondEntry
  have hclosedShort (value : Nat) :
      (shortBinaryNumeralTerm value).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty value
  have hguard :=
    boundedWitnessGuardCertificate_structuralPayloadBound_le_public
      innerStart tokenCount hinner.1
  have hstartLt := closedLtCertificate_structuralPayloadBound_le_public
    start tokenCount hinner.2.1.1
  have hfirstSuccessor :=
    successorEqualityCertificate_structuralPayloadBound_le_public
      start innerStart hinner.2.1.2.1
  have hfirstEntryPublic :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      zeroValuation tableTerm widthTerm startTerm oneTerm
      (hclosedShort tokenTable) (hclosedShort width) (hclosedShort start)
      arithmeticOneTerm_freeVariables_eq_empty hfirstEntry
  have hinnerLt := closedLtCertificate_structuralPayloadBound_le_public
    innerStart tokenCount hinner.2.2.1
  have hsecondSuccessor :=
    successorEqualityCertificate_structuralPayloadBound_le_public
      innerStart outputStart hinner.2.2.2.1
  have hsecondEntryPublic :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_public
      zeroValuation tableTerm widthTerm innerTerm oneTerm
      (hclosedShort tokenTable) (hclosedShort width) (hclosedShort innerStart)
      arithmeticOneTerm_freeVariables_eq_empty hsecondEntry
  have hseven :=
    sevenLeafRightConjunctionStructuralPayloadBound_le_envelope
      guardCertificate startLtCertificate firstSuccessorCertificate
      firstEntryCertificate innerLtCertificate secondSuccessorCertificate
      secondEntryCertificate
      (boundedWitnessGuardStructuralPayloadPolynomial innerStart tokenCount)
      (closedLtStructuralPayloadPolynomial start tokenCount)
      (successorEqualityStructuralPayloadPolynomial start innerStart)
      (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation tableTerm widthTerm startTerm oneTerm)
      (closedLtStructuralPayloadPolynomial innerStart tokenCount)
      (successorEqualityStructuralPayloadPolynomial innerStart outputStart)
      (compactFixedWidthEntryAtValuationStructuralPayloadPolynomial
        zeroValuation tableTerm widthTerm innerTerm oneTerm)
      hguard hstartLt hfirstSuccessor hfirstEntryPublic hinnerLt
      hsecondSuccessor hsecondEntryPublic
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        guardCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          startLtCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            firstSuccessorCertificate
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              firstEntryCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                innerLtCertificate
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  secondSuccessorCertificate secondEntryCertificate)))))) ≤ _
  unfold
    compactBinaryNatCompletedStatusPrefixPostWitnessStructuralPayloadPolynomial
    compactBinaryNatDoubleStatusPostWitnessStructuralPayloadPolynomial
  dsimp only [tableTerm, widthTerm, countTerm, startTerm, outputStartTerm,
    innerTerm, oneTerm]
  exact hseven

def compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial
    (tokenTable width tokenCount start finish : Nat) : Nat :=
  let innerStart := start + 1
  hybridExistsWitnessStructuralPayloadEnvelope zeroValuation
    (compactBinaryNatFailedStatusSliceWitnessBody
      tokenTable width tokenCount start finish)
    innerStart
    (compactBinaryNatFailedStatusSlicePostWitnessStructuralPayloadPolynomial
      tokenTable width tokenCount start finish innerStart)

theorem
    compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount start finish : Nat)
    (hgraph : CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount start finish) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start finish hgraph) ≤
      compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial
        tokenTable width tokenCount start finish := by
  let innerStart := start + 1
  have hinner : innerStart ≤ tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 0 finish := by
    simpa only [innerStart] using
      compactBinaryNatFailedStatusSlice_deterministicWitness
        tokenTable width tokenCount start finish hgraph
  let post :=
    compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate
      tokenTable width tokenCount start finish innerStart hinner
  let instantiated := CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactBinaryNatFailedStatusSliceWitnessBody_substitution_alignment
      tokenTable width tokenCount start finish innerStart).symm post
  have hpost :=
    compactBinaryNatFailedStatusSlicePostWitnessExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount start finish innerStart hinner
  have hinstantiated : hybridFormulaStructuralPayloadBound instantiated ≤
      compactBinaryNatFailedStatusSlicePostWitnessStructuralPayloadPolynomial
        tokenTable width tokenCount start finish innerStart := by
    simpa only [instantiated, hybridFormulaStructuralPayloadBound] using hpost
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
    (compactBinaryNatFailedStatusSliceWitnessBody
      tokenTable width tokenCount start finish)
    innerStart instantiated
    (compactBinaryNatFailedStatusSlicePostWitnessStructuralPayloadPolynomial
      tokenTable width tokenCount start finish innerStart)
    hinstantiated
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.existsWitness
        (compactBinaryNatFailedStatusSliceWitnessBody
          tokenTable width tokenCount start finish)
        innerStart instantiated) ≤ _
  unfold compactBinaryNatFailedStatusSliceStructuralPayloadPolynomial
  dsimp only [innerStart]
  exact hexists

def compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial
    (tokenTable width tokenCount start outputStart : Nat) : Nat :=
  let innerStart := start + 1
  hybridExistsWitnessStructuralPayloadEnvelope zeroValuation
    (compactBinaryNatCompletedStatusPrefixWitnessBody
      tokenTable width tokenCount start outputStart)
    innerStart
    (compactBinaryNatCompletedStatusPrefixPostWitnessStructuralPayloadPolynomial
      tokenTable width tokenCount start outputStart innerStart)

theorem
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount start outputStart : Nat)
    (hgraph : CompactBinaryNatCompletedStatusPrefix
      tokenTable width tokenCount start outputStart) :
    hybridFormulaStructuralPayloadBound
        (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount start outputStart hgraph) ≤
      compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial
        tokenTable width tokenCount start outputStart := by
  let innerStart := start + 1
  have hinner : innerStart ≤ tokenCount ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount start 1 innerStart ∧
      CompactAdditiveTokenCell
        tokenTable width tokenCount innerStart 1 outputStart := by
    simpa only [innerStart] using
      compactBinaryNatCompletedStatusPrefix_deterministicWitness
        tokenTable width tokenCount start outputStart hgraph
  let post :=
    compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate
      tokenTable width tokenCount start outputStart innerStart hinner
  let instantiated := CheckedHybridValuationBoundedFormulaCertificate.cast
    (compactBinaryNatCompletedStatusPrefixWitnessBody_substitution_alignment
      tokenTable width tokenCount start outputStart innerStart).symm post
  have hpost :=
    compactBinaryNatCompletedStatusPrefixPostWitnessExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount start outputStart innerStart hinner
  have hinstantiated : hybridFormulaStructuralPayloadBound instantiated ≤
      compactBinaryNatCompletedStatusPrefixPostWitnessStructuralPayloadPolynomial
        tokenTable width tokenCount start outputStart innerStart := by
    simpa only [instantiated, hybridFormulaStructuralPayloadBound] using hpost
  have hexists := hybridExistsWitnessStructuralPayloadBound_le_envelope
    (compactBinaryNatCompletedStatusPrefixWitnessBody
      tokenTable width tokenCount start outputStart)
    innerStart instantiated
    (compactBinaryNatCompletedStatusPrefixPostWitnessStructuralPayloadPolynomial
      tokenTable width tokenCount start outputStart innerStart)
    hinstantiated
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.existsWitness
        (compactBinaryNatCompletedStatusPrefixWitnessBody
          tokenTable width tokenCount start outputStart)
        innerStart instantiated) ≤ _
  unfold compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial
  dsimp only [innerStart]
  exact hexists

#print axioms
  compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
#print axioms
  compactBinaryNatFailedStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
#print axioms
  compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
