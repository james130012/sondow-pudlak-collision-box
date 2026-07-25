import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPABinaryNumeralAdditionBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Fixed atomic resources for the syntax-formula parser

The parser dispatch tag is compared only with the literals `0, ..., 7`.
Consequently its equality and disequality certificates admit bounds depending
only on the common bit bound for the tag, rather than on a proof-dependent
public envelope.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds

private abbrev parserFormulaAtomicZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation

def parserFormulaAtomicTermCodePolynomial (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        0)).length +
    (binaryTermCode
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        1)).length +
    (binaryTermCode
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        2)).length +
    (binaryTermCode
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        3)).length +
    (binaryTermCode
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        4)).length +
    (binaryTermCode
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        5)).length +
    (binaryTermCode
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        6)).length +
    (binaryTermCode
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        7)).length + 1

def parserFormulaPositiveAtomicFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (parserFormulaAtomicTermCodePolynomial bitBound)

def parserFormulaNegativeAtomicFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  compileNegativeRelationFixedPayloadPolynomial 0
    (parserFormulaAtomicTermCodePolynomial bitBound)

def parserFormulaAtomicLeafFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * parserFormulaAtomicTermCodePolynomial bitBound +
    2 * (binaryNatCode 0).length +
    (binaryNatCode 2).length + 128

def parserFormulaAtomicFormulaCodePolynomial (bitBound : Nat) : Nat :=
  2 * parserFormulaAtomicLeafFormulaCodePolynomial bitBound +
    (binaryNatCode 5).length + 1

def parserFormulaEqEitherFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (parserFormulaAtomicFormulaCodePolynomial bitBound)
    (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)

def parserFormulaTermLeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  2 * parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound +
    3 * generalContextAssemblyEnvelope
      (parserFormulaAtomicFormulaCodePolynomial bitBound)

theorem parserFormulaShortNumeralCode_le
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      parserFormulaAtomicTermCodePolynomial bitBound := by
  have hraw :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  unfold parserFormulaAtomicTermCodePolynomial
  omega

theorem parserFormulaFixedTagCode_le
    (expected bitBound : Nat) (hexpected : expected <= 7) :
    (binaryTermCode
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        expected)).length <=
      parserFormulaAtomicTermCodePolynomial bitBound := by
  have hcases :
      expected = 0 ∨ expected = 1 ∨ expected = 2 ∨ expected = 3 ∨
        expected = 4 ∨ expected = 5 ∨ expected = 6 ∨ expected = 7 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold parserFormulaAtomicTermCodePolynomial <;> omega

private theorem parserFormulaFixedNumeral_closed (expected : Nat) :
    (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
      expected).freeVariables = ∅ := by
  unfold
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem parserFormulaBinaryRelation_closed
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (LO.FirstOrder.Semiformula.rel relationSymbol
      ![left, right]).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_rel]
  ext candidate
  constructor
  · intro hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero =>
        change candidate ∈ left.freeVariables at hcoordinate
        rw [hleft] at hcoordinate
        simp at hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            change candidate ∈ right.freeVariables at hcoordinate
            rw [hright] at hcoordinate
            simp at hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · simp

private theorem parserFormulaBinaryRelationCode_le
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) (bitBound : Nat)
    (hleft :
      (binaryTermCode left).length <=
        parserFormulaAtomicTermCodePolynomial bitBound)
    (hright :
      (binaryTermCode right).length <=
        parserFormulaAtomicTermCodePolynomial bitBound) :
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right])).length <=
      parserFormulaAtomicLeafFormulaCodePolynomial bitBound := by
  simp [binaryFormulaCode, Matrix.fun_eq_vec_two]
  have hrelationTag :
      (binaryNatCode (Encodable.encode relationSymbol)).length <= 128 := by
    cases relationSymbol <;> decide
  unfold parserFormulaAtomicLeafFormulaCodePolynomial
  omega

theorem parserFormulaFixedNumeral_freeVariables_eq_empty
    (expected : Nat) :
    (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
      expected).freeVariables = ∅ :=
  parserFormulaFixedNumeral_closed expected

theorem parserFormulaBinaryRelation_freeVariables_eq_empty
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (LO.FirstOrder.Semiformula.rel relationSymbol
      ![left, right]).freeVariables = ∅ :=
  parserFormulaBinaryRelation_closed relationSymbol left right hleft hright

theorem parserFormulaBinaryRelationCode_le_fixed
    (relationSymbol : LO.FirstOrder.Language.Rel ℒₒᵣ 2)
    (left right : ValuationTerm) (bitBound : Nat)
    (hleft :
      (binaryTermCode left).length <=
        parserFormulaAtomicTermCodePolynomial bitBound)
    (hright :
      (binaryTermCode right).length <=
        parserFormulaAtomicTermCodePolynomial bitBound) :
    (binaryFormulaCode
      (LO.FirstOrder.Semiformula.rel relationSymbol ![left, right])).length <=
      parserFormulaAtomicLeafFormulaCodePolynomial bitBound :=
  parserFormulaBinaryRelationCode_le relationSymbol left right bitBound hleft
    hright

private theorem parserFormulaBinaryDisjunctionCode_le
    (left right : ValuationFormula) (bitBound : Nat)
    (hleft :
      (binaryFormulaCode left).length <=
        parserFormulaAtomicLeafFormulaCodePolynomial bitBound)
    (hright :
      (binaryFormulaCode right).length <=
        parserFormulaAtomicLeafFormulaCodePolynomial bitBound) :
    (binaryFormulaCode (left ⋎ right)).length <=
      parserFormulaAtomicFormulaCodePolynomial bitBound := by
  simp [binaryFormulaCode] at *
  unfold parserFormulaAtomicFormulaCodePolynomial
  omega

private theorem parserFormulaAtomicLeafFormulaCodePolynomial_le
    (bitBound : Nat) :
    parserFormulaAtomicLeafFormulaCodePolynomial bitBound <=
      parserFormulaAtomicFormulaCodePolynomial bitBound := by
  unfold parserFormulaAtomicFormulaCodePolynomial
  omega

theorem nativeEqFormula_code_length_le_fixed
    (value expected bitBound : Nat)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 7) :
    (binaryFormulaCode (nativeEqFormula value expected)).length <=
      parserFormulaAtomicLeafFormulaCodePolynomial bitBound := by
  unfold nativeEqFormula
  exact parserFormulaBinaryRelationCode_le Language.Eq.eq
    (shortBinaryNumeralTerm value)
    (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
      expected)
    bitBound
    (parserFormulaShortNumeralCode_le value bitBound hvalueSize)
    (parserFormulaFixedTagCode_le expected bitBound hexpected)

@[simp] theorem nativeEqFormula_freeVariables_eq_empty_fixed
    (value expected : Nat) :
    (nativeEqFormula value expected).freeVariables = ∅ := by
  unfold nativeEqFormula
  exact parserFormulaBinaryRelation_closed Language.Eq.eq
    (shortBinaryNumeralTerm value)
    (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
      expected)
    (shortBinaryNumeralTerm_freeVariables_eq_empty value)
    (parserFormulaFixedNumeral_closed expected)

theorem nativeEqEitherFormula_code_length_le_fixed
    (value left right bitBound : Nat)
    (hvalueSize : Nat.size value <= bitBound)
    (hleft : left <= 7)
    (hright : right <= 7) :
    (binaryFormulaCode
      (nativeEqFormula value left ⋎ nativeEqFormula value right)).length <=
      parserFormulaAtomicFormulaCodePolynomial bitBound := by
  exact parserFormulaBinaryDisjunctionCode_le
    (nativeEqFormula value left) (nativeEqFormula value right) bitBound
    (nativeEqFormula_code_length_le_fixed value left bitBound hvalueSize hleft)
    (nativeEqFormula_code_length_le_fixed value right bitBound hvalueSize hright)

@[simp] theorem nativeEqEitherFormula_freeVariables_eq_empty_fixed
    (value left right : Nat) :
    (nativeEqFormula value left ⋎
      nativeEqFormula value right).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_or,
    nativeEqFormula_freeVariables_eq_empty_fixed,
    nativeEqFormula_freeVariables_eq_empty_fixed]
  simp

theorem nativeNeFormula_code_length_le_fixed
    (value expected bitBound : Nat)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 7) :
    (binaryFormulaCode (nativeNeFormula value expected)).length <=
      parserFormulaAtomicFormulaCodePolynomial bitBound := by
  have heq := nativeEqFormula_code_length_le_fixed value expected bitBound
    hvalueSize hexpected
  have hneg := binaryFormulaCode_neg_length_le
    (nativeEqFormula value expected)
  unfold nativeNeFormula parserFormulaAtomicFormulaCodePolynomial
  omega

@[simp] theorem nativeNeFormula_freeVariables_eq_empty_fixed
    (value expected : Nat) :
    (nativeNeFormula value expected).freeVariables = ∅ := by
  unfold nativeNeFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_not,
    nativeEqFormula_freeVariables_eq_empty_fixed]

theorem nativeEqCertificate_structuralPayloadBound_le_fixed
    (value expected bitBound : Nat)
    (heq : value = expected)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 7) :
    hybridFormulaStructuralPayloadBound
        (nativeEqCertificate value expected heq) <=
      parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound := by
  change compilePositiveRelationPayloadResource parserFormulaAtomicZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value,
        FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          expected] <= _
  unfold parserFormulaPositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    parserFormulaAtomicZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm value)
    (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
      expected)
    0 (parserFormulaAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (parserFormulaFixedNumeral_closed expected)
    (parserFormulaShortNumeralCode_le value bitBound hvalueSize)
    (parserFormulaFixedTagCode_le expected bitBound hexpected)

theorem nativeNeCertificate_structuralPayloadBound_le_fixed
    (value expected bitBound : Nat)
    (hne : value ≠ expected)
    (hvalueSize : Nat.size value <= bitBound)
    (hexpected : expected <= 7) :
    hybridFormulaStructuralPayloadBound
        (nativeNeCertificate value expected hne) <=
      parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound := by
  change compileNegativeRelationPayloadResource parserFormulaAtomicZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value,
        FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          expected] <= _
  unfold parserFormulaNegativeAtomicFixedPayloadPolynomial
  exact compileNegativeRelationPayloadResource_le_fixed_of_closed
    parserFormulaAtomicZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm value)
    (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
      expected)
    0 (parserFormulaAtomicTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    (parserFormulaFixedNumeral_closed expected)
    (parserFormulaShortNumeralCode_le value bitBound hvalueSize)
    (parserFormulaFixedTagCode_le expected bitBound hexpected)

theorem
    nativeEqEitherCertificateFromData_structuralPayloadBound_le_fixed
    (value left right bitBound : Nat)
    (data : NativeEqEitherCheckedData value left right)
    (hvalueSize : Nat.size value <= bitBound)
    (hleft : left <= 7)
    (hright : right <= 7) :
    hybridFormulaStructuralPayloadBound
        (nativeEqEitherCertificateFromData value left right data) <=
      parserFormulaEqEitherFixedPayloadPolynomial bitBound := by
  let leftFormula := nativeEqFormula value left
  let rightFormula := nativeEqFormula value right
  let formulaResource := parserFormulaAtomicFormulaCodePolynomial bitBound
  have hformulaPositive : 1 <= formulaResource := by
    dsimp only [formulaResource]
    unfold parserFormulaAtomicFormulaCodePolynomial
    omega
  have hvalueCode :
      (binaryTermCode (shortBinaryNumeralTerm value)).length <=
        parserFormulaAtomicTermCodePolynomial bitBound :=
    parserFormulaShortNumeralCode_le value bitBound hvalueSize
  have hleftCode :
      (binaryTermCode
        (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          left)).length <= parserFormulaAtomicTermCodePolynomial bitBound :=
    parserFormulaFixedTagCode_le left bitBound hleft
  have hrightCode :
      (binaryTermCode
        (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          right)).length <= parserFormulaAtomicTermCodePolynomial bitBound :=
    parserFormulaFixedTagCode_le right bitBound hright
  have hleftFormulaCodeLeaf :
      (binaryFormulaCode leftFormula).length <=
        parserFormulaAtomicLeafFormulaCodePolynomial bitBound := by
    exact parserFormulaBinaryRelationCode_le Language.Eq.eq
      (shortBinaryNumeralTerm value)
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        left)
      bitBound hvalueCode hleftCode
  have hrightFormulaCodeLeaf :
      (binaryFormulaCode rightFormula).length <=
        parserFormulaAtomicLeafFormulaCodePolynomial bitBound := by
    exact parserFormulaBinaryRelationCode_le Language.Eq.eq
      (shortBinaryNumeralTerm value)
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        right)
      bitBound hvalueCode hrightCode
  have hleftFormulaCode :
      (binaryFormulaCode leftFormula).length <= formulaResource :=
    hleftFormulaCodeLeaf.trans
      (parserFormulaAtomicLeafFormulaCodePolynomial_le bitBound)
  have hrightFormulaCode :
      (binaryFormulaCode rightFormula).length <= formulaResource :=
    hrightFormulaCodeLeaf.trans
      (parserFormulaAtomicLeafFormulaCodePolynomial_le bitBound)
  have horCode :
      (binaryFormulaCode (leftFormula ⋎ rightFormula)).length <=
        formulaResource :=
    parserFormulaBinaryDisjunctionCode_le leftFormula rightFormula bitBound
      hleftFormulaCodeLeaf hrightFormulaCodeLeaf
  have hleftClosed : leftFormula.freeVariables = ∅ := by
    exact parserFormulaBinaryRelation_closed Language.Eq.eq
      (shortBinaryNumeralTerm value)
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        left)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (parserFormulaFixedNumeral_closed left)
  have hrightClosed : rightFormula.freeVariables = ∅ := by
    exact parserFormulaBinaryRelation_closed Language.Eq.eq
      (shortBinaryNumeralTerm value)
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        right)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (parserFormulaFixedNumeral_closed right)
  have hcontext :
      formulaCodeSum
        (valuationContext (leftFormula ⋎ rightFormula).freeVariables
          parserFormulaAtomicZeroValuation) <= formulaResource := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hleftClosed, hrightClosed]
    simp [valuationContext, formulaCodeSum]
  cases data with
  | left heq =>
      have hchild :=
        nativeEqCertificate_structuralPayloadBound_le_fixed value left
          bitBound heq hvalueSize hleft
      have hpath := transparentHybridDisjunctionLeftPayloadBound_le
        (right := rightFormula) (nativeEqCertificate value left heq)
        (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound) hchild
      have hfixed :=
        transparentHybridDisjunctionLeftPayloadEnvelope_le_general
          parserFormulaAtomicZeroValuation leftFormula rightFormula
          (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
          formulaResource hformulaPositive hcontext hleftFormulaCode
          hrightFormulaCode horCode
      exact hpath.trans hfixed
  | right heq =>
      have hchild :=
        nativeEqCertificate_structuralPayloadBound_le_fixed value right
          bitBound heq hvalueSize hright
      have hpath := transparentHybridDisjunctionRightPayloadBound_le
        (left := leftFormula) (nativeEqCertificate value right heq)
        (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound) hchild
      have hfixed :=
        transparentHybridDisjunctionRightPayloadEnvelope_le_general
          parserFormulaAtomicZeroValuation leftFormula rightFormula
          (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
          formulaResource hformulaPositive hcontext hleftFormulaCode
          hrightFormulaCode horCode
      exact hpath.trans hfixed

theorem termLeCertificate_structuralPayloadBound_le_fixed
    (left right : Nat) (leftTerm rightTerm : ValuationTerm)
    (bitBound : Nat)
    (hleftClosed : leftTerm.freeVariables = ∅)
    (hrightClosed : rightTerm.freeVariables = ∅)
    (hleftCode :
      (binaryTermCode leftTerm).length <=
        parserFormulaAtomicTermCodePolynomial bitBound)
    (hrightCode :
      (binaryTermCode rightTerm).length <=
        parserFormulaAtomicTermCodePolynomial bitBound)
    (hleftValue :
      termValue parserFormulaAtomicZeroValuation leftTerm = left)
    (hrightValue :
      termValue parserFormulaAtomicZeroValuation rightTerm = right)
    (hle : left <= right) :
    hybridFormulaStructuralPayloadBound
        (termLeCertificate left right leftTerm rightTerm hleftValue
          hrightValue hle) <=
      parserFormulaTermLeFixedPayloadPolynomial bitBound := by
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula :=
    LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let formulaResource := parserFormulaAtomicFormulaCodePolynomial bitBound
  let atomResource :=
    parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound
  let Gamma := valuationContext targetFormula.freeVariables
    parserFormulaAtomicZeroValuation
  have hequalityClosed : equalityFormula.freeVariables = ∅ :=
    parserFormulaBinaryRelation_closed Language.Eq.eq leftTerm rightTerm
      hleftClosed hrightClosed
  have hstrictClosed : strictFormula.freeVariables = ∅ :=
    parserFormulaBinaryRelation_closed Language.ORing.Rel.lt leftTerm
      rightTerm hleftClosed hrightClosed
  have htargetClosed : targetFormula.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hequalityClosed,
      hstrictClosed]
    simp
  have hequalityCodeLeaf :
      (binaryFormulaCode equalityFormula).length <=
        parserFormulaAtomicLeafFormulaCodePolynomial bitBound :=
    parserFormulaBinaryRelationCode_le Language.Eq.eq leftTerm rightTerm
      bitBound hleftCode hrightCode
  have hstrictCodeLeaf :
      (binaryFormulaCode strictFormula).length <=
        parserFormulaAtomicLeafFormulaCodePolynomial bitBound :=
    parserFormulaBinaryRelationCode_le Language.ORing.Rel.lt leftTerm
      rightTerm bitBound hleftCode hrightCode
  have hequalityCode :
      (binaryFormulaCode equalityFormula).length <= formulaResource :=
    hequalityCodeLeaf.trans
      (parserFormulaAtomicLeafFormulaCodePolynomial_le bitBound)
  have hstrictCode :
      (binaryFormulaCode strictFormula).length <= formulaResource :=
    hstrictCodeLeaf.trans
      (parserFormulaAtomicLeafFormulaCodePolynomial_le bitBound)
  have htargetCode :
      (binaryFormulaCode targetFormula).length <= formulaResource :=
    parserFormulaBinaryDisjunctionCode_le equalityFormula strictFormula
      bitBound hequalityCodeLeaf hstrictCodeLeaf
  have hpositive : 1 <= formulaResource := by
    dsimp only [formulaResource]
    unfold parserFormulaAtomicFormulaCodePolynomial
    omega
  have hcontext : formulaCodeSum Gamma <= formulaResource := by
    dsimp only [Gamma]
    rw [htargetClosed]
    simp [valuationContext, formulaCodeSum]
  have hequalityResource :
      compilePositiveRelationPayloadResource parserFormulaAtomicZeroValuation
          Language.Eq.eq args <= atomResource := by
    dsimp only [atomResource, args]
    unfold parserFormulaPositiveAtomicFixedPayloadPolynomial
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed
      parserFormulaAtomicZeroValuation Language.Eq.eq leftTerm rightTerm
      0 (parserFormulaAtomicTermCodePolynomial bitBound)
      hleftClosed hrightClosed hleftCode hrightCode
  have hstrictResource :
      compilePositiveRelationPayloadResource parserFormulaAtomicZeroValuation
          Language.ORing.Rel.lt args <= atomResource := by
    dsimp only [atomResource, args]
    unfold parserFormulaPositiveAtomicFixedPayloadPolynomial
    exact compilePositiveRelationPayloadResource_le_fixed_of_closed
      parserFormulaAtomicZeroValuation Language.ORing.Rel.lt leftTerm rightTerm
      0 (parserFormulaAtomicTermCodePolynomial bitBound)
      hleftClosed hrightClosed hleftCode hrightCode
  have hequalityInsert :
      formulaCodeSum (insert equalityFormula Gamma) <=
        generalContextCoordinate formulaResource := by
    have hraw := formulaCodeSum_insert_le Gamma equalityFormula
    unfold generalContextCoordinate
    omega
  have hstrictInsert :
      formulaCodeSum (insert strictFormula Gamma) <=
        generalContextCoordinate formulaResource := by
    have hraw := formulaCodeSum_insert_le Gamma strictFormula
    unfold generalContextCoordinate
    omega
  have hweakEquality := weakeningFullAssemblyCost_le_general
    (insert equalityFormula Gamma) formulaResource hequalityInsert
  have hweakStrict := weakeningFullAssemblyCost_le_general
    (insert strictFormula Gamma) formulaResource hstrictInsert
  have hdisjunction := disjunctionFullAssemblyCost_le_general Gamma
    equalityFormula strictFormula formulaResource hpositive hcontext
    hequalityCode hstrictCode htargetCode
  by_cases heq : left = right
  · simp only [termLeCertificate, termLeFormula, id_eq]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    change
      compilePositiveRelationPayloadResource parserFormulaAtomicZeroValuation
          Language.Eq.eq args +
        weakeningFullAssemblyCost (insert equalityFormula Gamma) +
        disjunctionFullAssemblyCost Gamma equalityFormula strictFormula <= _
    unfold parserFormulaTermLeFixedPayloadPolynomial
    dsimp only [args, equalityFormula, strictFormula, targetFormula, Gamma,
      formulaResource, atomResource] at *
    omega
  · simp only [termLeCertificate, termLeFormula, id_eq]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    change
      compilePositiveRelationPayloadResource parserFormulaAtomicZeroValuation
          Language.ORing.Rel.lt args +
        weakeningFullAssemblyCost (insert strictFormula Gamma) +
        disjunctionFullAssemblyCost Gamma equalityFormula strictFormula <= _
    unfold parserFormulaTermLeFixedPayloadPolynomial
    dsimp only [args, equalityFormula, strictFormula, targetFormula, Gamma,
      formulaResource, atomResource] at *
    omega

theorem shortNativeLeCertificate_structuralPayloadBound_le_fixed
    (left right bitBound : Nat) (hle : left <= right)
    (hleftSize : Nat.size left <= bitBound)
    (hright : right <= 7) :
    hybridFormulaStructuralPayloadBound
        (shortNativeLeCertificate left right hle) <=
      parserFormulaTermLeFixedPayloadPolynomial bitBound := by
  simpa only [shortNativeLeCertificate, shortNativeLeFormula, id_eq] using
    (termLeCertificate_structuralPayloadBound_le_fixed left right
      (shortBinaryNumeralTerm left)
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        right)
      bitBound (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (parserFormulaFixedNumeral_closed right)
      (parserFormulaShortNumeralCode_le left bitBound hleftSize)
      (parserFormulaFixedTagCode_le right bitBound hright)
      (by simp [termValue_shortBinaryNumeralTerm]) (by simp) hle)

theorem nativeShortLeCertificate_structuralPayloadBound_le_fixed
    (left right bitBound : Nat) (hle : left <= right)
    (hleft : left <= 7)
    (hrightSize : Nat.size right <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (nativeShortLeCertificate left right hle) <=
      parserFormulaTermLeFixedPayloadPolynomial bitBound := by
  simpa only [nativeShortLeCertificate, nativeShortLeFormula, id_eq] using
    (termLeCertificate_structuralPayloadBound_le_fixed left right
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        left)
      (shortBinaryNumeralTerm right) bitBound
      (parserFormulaFixedNumeral_closed left)
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (parserFormulaFixedTagCode_le left bitBound hleft)
      (parserFormulaShortNumeralCode_le right bitBound hrightSize)
      (by simp) (by simp [termValue_shortBinaryNumeralTerm]) hle)

theorem shortNativeLeFormula_code_length_le_fixed
    (left right bitBound : Nat)
    (hleftSize : Nat.size left <= bitBound)
    (hright : right <= 7) :
    (binaryFormulaCode (shortNativeLeFormula left right)).length <=
      parserFormulaAtomicFormulaCodePolynomial bitBound := by
  unfold shortNativeLeFormula termLeFormula
  exact parserFormulaBinaryDisjunctionCode_le _ _ bitBound
    (parserFormulaBinaryRelationCode_le Language.Eq.eq _ _ bitBound
      (parserFormulaShortNumeralCode_le left bitBound hleftSize)
      (parserFormulaFixedTagCode_le right bitBound hright))
    (parserFormulaBinaryRelationCode_le Language.ORing.Rel.lt _ _ bitBound
      (parserFormulaShortNumeralCode_le left bitBound hleftSize)
      (parserFormulaFixedTagCode_le right bitBound hright))

@[simp] theorem shortNativeLeFormula_freeVariables_eq_empty_fixed
    (left right : Nat) :
    (shortNativeLeFormula left right).freeVariables = ∅ := by
  unfold shortNativeLeFormula termLeFormula
  rw [LO.FirstOrder.Semiformula.Operator.le_def]
  rw [LO.FirstOrder.Semiformula.freeVariables_or]
  have heq := parserFormulaBinaryRelation_closed Language.Eq.eq
    (shortBinaryNumeralTerm left)
    (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
      right)
    (shortBinaryNumeralTerm_freeVariables_eq_empty left)
    (parserFormulaFixedNumeral_closed right)
  have hlt := parserFormulaBinaryRelation_closed Language.LT.lt
    (shortBinaryNumeralTerm left)
    (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
      right)
    (shortBinaryNumeralTerm_freeVariables_eq_empty left)
    (parserFormulaFixedNumeral_closed right)
  rw [heq, hlt]
  simp

theorem nativeShortLeFormula_code_length_le_fixed
    (left right bitBound : Nat)
    (hleft : left <= 7)
    (hrightSize : Nat.size right <= bitBound) :
    (binaryFormulaCode (nativeShortLeFormula left right)).length <=
      parserFormulaAtomicFormulaCodePolynomial bitBound := by
  unfold nativeShortLeFormula termLeFormula
  exact parserFormulaBinaryDisjunctionCode_le _ _ bitBound
    (parserFormulaBinaryRelationCode_le Language.Eq.eq _ _ bitBound
      (parserFormulaFixedTagCode_le left bitBound hleft)
      (parserFormulaShortNumeralCode_le right bitBound hrightSize))
    (parserFormulaBinaryRelationCode_le Language.ORing.Rel.lt _ _ bitBound
      (parserFormulaFixedTagCode_le left bitBound hleft)
      (parserFormulaShortNumeralCode_le right bitBound hrightSize))

@[simp] theorem nativeShortLeFormula_freeVariables_eq_empty_fixed
    (left right : Nat) :
    (nativeShortLeFormula left right).freeVariables = ∅ := by
  unfold nativeShortLeFormula termLeFormula
  rw [LO.FirstOrder.Semiformula.Operator.le_def]
  rw [LO.FirstOrder.Semiformula.freeVariables_or]
  have heq := parserFormulaBinaryRelation_closed Language.Eq.eq
    (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
      left)
    (shortBinaryNumeralTerm right)
    (parserFormulaFixedNumeral_closed left)
    (shortBinaryNumeralTerm_freeVariables_eq_empty right)
  have hlt := parserFormulaBinaryRelation_closed Language.LT.lt
    (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
      left)
    (shortBinaryNumeralTerm right)
    (parserFormulaFixedNumeral_closed left)
    (shortBinaryNumeralTerm_freeVariables_eq_empty right)
  rw [heq, hlt]
  simp

#print axioms nativeEqCertificate_structuralPayloadBound_le_fixed
#print axioms nativeNeCertificate_structuralPayloadBound_le_fixed
#print axioms nativeEqFormula_code_length_le_fixed
#print axioms nativeEqFormula_freeVariables_eq_empty_fixed
#print axioms nativeEqEitherFormula_code_length_le_fixed
#print axioms nativeEqEitherFormula_freeVariables_eq_empty_fixed
#print axioms nativeNeFormula_code_length_le_fixed
#print axioms nativeNeFormula_freeVariables_eq_empty_fixed
#print axioms
  nativeEqEitherCertificateFromData_structuralPayloadBound_le_fixed
#print axioms shortNativeLeCertificate_structuralPayloadBound_le_fixed
#print axioms nativeShortLeCertificate_structuralPayloadBound_le_fixed
#print axioms shortNativeLeFormula_code_length_le_fixed
#print axioms shortNativeLeFormula_freeVariables_eq_empty_fixed
#print axioms nativeShortLeFormula_code_length_le_fixed
#print axioms nativeShortLeFormula_freeVariables_eq_empty_fixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
