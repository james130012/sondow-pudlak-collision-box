import integration.FoundationCompactNumericListedDirectArithmeticRelCodeValidSyntaxFixedBounds
import integration.FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Fully fixed arithmetic relation-code certificates

The genuine positive and negative certificates for the two accepted pairs
`(2, 0)` and `(2, 1)` are bounded using one shared bit coordinate.  No
certificate-dependent public envelope remains in the endpoints.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectArithmeticRelCodeValidFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactArithmeticSymbolCode
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticRelCodeValidSyntaxFixedBounds
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula

private def relCodeFixedZeroValuation : Nat -> Nat := fun _ => 0

def arithmeticRelCodePositiveAtomicFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  compilePositiveRelationFixedPayloadPolynomial 0
    (arithmeticRelCodeTermCodePolynomial bitBound)

def arithmeticRelCodeNegativeAtomicFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  compileNegativeRelationFixedPayloadPolynomial 0
    (arithmeticRelCodeTermCodePolynomial bitBound)

def arithmeticRelCodeValidPairFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (arithmeticRelCodeValidFormulaCodePolynomial bitBound)
    (arithmeticRelCodePositiveAtomicFixedPayloadPolynomial bitBound)
    (arithmeticRelCodePositiveAtomicFixedPayloadPolynomial bitBound)

def arithmeticRelCodeValidFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (arithmeticRelCodeValidFormulaCodePolynomial bitBound)
    (arithmeticRelCodeValidPairFullyFixedPayloadPolynomial bitBound)

def arithmeticRelCodeInvalidPairFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (arithmeticRelCodeInvalidFormulaCodePolynomial bitBound)
    (arithmeticRelCodeNegativeAtomicFixedPayloadPolynomial bitBound)

def arithmeticRelCodeInvalidFullyFixedPayloadPolynomial
    (bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (arithmeticRelCodeInvalidFormulaCodePolynomial bitBound)
    (arithmeticRelCodeInvalidPairFullyFixedPayloadPolynomial bitBound)
    (arithmeticRelCodeInvalidPairFullyFixedPayloadPolynomial bitBound)

theorem relCodeFixedEqCertificate_structuralPayloadBound_le_fixed
    (value expected bitBound : Nat)
    (heq : value = expected)
    (hvalue : Nat.size value <= bitBound)
    (hexpected : expected <= 2) :
    hybridFormulaStructuralPayloadBound
        (relCodeFixedEqCertificate value expected heq) <=
      arithmeticRelCodePositiveAtomicFixedPayloadPolynomial bitBound := by
  change compilePositiveRelationPayloadResource relCodeFixedZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, relCodeFixedNumeralTerm expected] <= _
  unfold arithmeticRelCodePositiveAtomicFixedPayloadPolynomial
  exact compilePositiveRelationPayloadResource_le_fixed_of_closed
    relCodeFixedZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm value) (relCodeFixedNumeralTerm expected)
    0 (arithmeticRelCodeTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty value)
    (by
      simp [relCodeFixedNumeralTerm,
        LO.FirstOrder.Semiterm.Operator.operator])
    (arithmeticRelCodeShortNumeralTerm_code_length_le_fixed value bitBound
      hvalue)
    (arithmeticRelCodeFixedNumeralTerm_code_length_le_fixed expected bitBound
      hexpected)

theorem relCodeFixedNeCertificate_structuralPayloadBound_le_fixed
    (value expected bitBound : Nat)
    (hne : value ≠ expected)
    (hvalue : Nat.size value <= bitBound)
    (hexpected : expected <= 2) :
    hybridFormulaStructuralPayloadBound
        (relCodeFixedNeCertificate value expected hne) <=
      arithmeticRelCodeNegativeAtomicFixedPayloadPolynomial bitBound := by
  change compileNegativeRelationPayloadResource relCodeFixedZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, relCodeFixedNumeralTerm expected] <= _
  unfold arithmeticRelCodeNegativeAtomicFixedPayloadPolynomial
  exact compileNegativeRelationPayloadResource_le_fixed_of_closed
    relCodeFixedZeroValuation Language.Eq.eq
    (shortBinaryNumeralTerm value) (relCodeFixedNumeralTerm expected)
    0 (arithmeticRelCodeTermCodePolynomial bitBound)
    (shortBinaryNumeralTerm_freeVariables_eq_empty value)
    (by
      simp [relCodeFixedNumeralTerm,
        LO.FirstOrder.Semiterm.Operator.operator])
    (arithmeticRelCodeShortNumeralTerm_code_length_le_fixed value bitBound
      hvalue)
    (arithmeticRelCodeFixedNumeralTerm_code_length_le_fixed expected bitBound
      hexpected)

private theorem disjunctionLeftEnvelope_le_closed_relCode
    (left right : ValuationFormula) (childResource resource : Nat)
    (hpositive : 1 <= resource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= resource)
    (hrightCode : (binaryFormulaCode right).length <= resource)
    (horCode : (binaryFormulaCode (left ⋎ right)).length <= resource) :
    transparentHybridDisjunctionLeftPayloadEnvelope relCodeFixedZeroValuation
        left right childResource <=
      hybridDisjunctionGeneralPayloadEnvelope resource childResource := by
  apply transparentHybridDisjunctionLeftPayloadEnvelope_le_general
  · exact hpositive
  · rw [LO.FirstOrder.Semiformula.freeVariables_or, hleftClosed,
      hrightClosed]
    simp [valuationContext, formulaCodeSum]
  · exact hleftCode
  · exact hrightCode
  · exact horCode

private theorem disjunctionRightEnvelope_le_closed_relCode
    (left right : ValuationFormula) (childResource resource : Nat)
    (hpositive : 1 <= resource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= resource)
    (hrightCode : (binaryFormulaCode right).length <= resource)
    (horCode : (binaryFormulaCode (left ⋎ right)).length <= resource) :
    transparentHybridDisjunctionRightPayloadEnvelope relCodeFixedZeroValuation
        left right childResource <=
      hybridDisjunctionGeneralPayloadEnvelope resource childResource := by
  apply transparentHybridDisjunctionRightPayloadEnvelope_le_general
  · exact hpositive
  · rw [LO.FirstOrder.Semiformula.freeVariables_or, hleftClosed,
      hrightClosed]
    simp [valuationContext, formulaCodeSum]
  · exact hleftCode
  · exact hrightCode
  · exact horCode

private theorem relCodeValidPairCertificate_structuralPayloadBound_le_fixed
    (arity code expectedCode bitBound : Nat)
    (harityEq : arity = 2)
    (hcodeEq : code = expectedCode)
    (hexpectedCode : expectedCode <= 1)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (relCodeFixedEqCertificate arity 2 harityEq)
          (relCodeFixedEqCertificate code expectedCode hcodeEq)) <=
      arithmeticRelCodeValidPairFullyFixedPayloadPolynomial bitBound := by
  let leftFormula := relCodeFixedEqFormula arity 2
  let rightFormula := relCodeFixedEqFormula code expectedCode
  let leftCertificate := relCodeFixedEqCertificate arity 2 harityEq
  let rightCertificate :=
    relCodeFixedEqCertificate code expectedCode hcodeEq
  let syntaxResource := arithmeticRelCodeValidFormulaCodePolynomial bitBound
  let childResource :=
    arithmeticRelCodePositiveAtomicFixedPayloadPolynomial bitBound
  have hleftResource :
      hybridFormulaStructuralPayloadBound leftCertificate <= childResource := by
    dsimp only [leftCertificate, childResource]
    exact relCodeFixedEqCertificate_structuralPayloadBound_le_fixed arity 2
      bitBound harityEq haritySize (by omega)
  have hrightResource :
      hybridFormulaStructuralPayloadBound rightCertificate <= childResource := by
    dsimp only [rightCertificate, childResource]
    exact relCodeFixedEqCertificate_structuralPayloadBound_le_fixed code
      expectedCode bitBound hcodeEq hcodeSize (by omega)
  have hleftClosed : leftFormula.freeVariables = ∅ := by simp [leftFormula]
  have hrightClosed : rightFormula.freeVariables = ∅ := by simp [rightFormula]
  have hleftCode :
      (binaryFormulaCode leftFormula).length <= syntaxResource := by
    have h := relCodeFixedEqFormula_code_length_le_fixed arity 2 bitBound
      haritySize (by omega)
    dsimp only [leftFormula, syntaxResource]
    unfold arithmeticRelCodeValidFormulaCodePolynomial
    omega
  have hrightCode :
      (binaryFormulaCode rightFormula).length <= syntaxResource := by
    have h := relCodeFixedEqFormula_code_length_le_fixed code expectedCode
      bitBound hcodeSize (by omega)
    dsimp only [rightFormula, syntaxResource]
    unfold arithmeticRelCodeValidFormulaCodePolynomial
    omega
  have hleftAtomicCode :
      (binaryFormulaCode leftFormula).length <=
        arithmeticRelCodeAtomicFormulaCodePolynomial bitBound := by
    dsimp only [leftFormula]
    exact relCodeFixedEqFormula_code_length_le_fixed arity 2 bitBound
      haritySize (by omega)
  have hrightAtomicCode :
      (binaryFormulaCode rightFormula).length <=
        arithmeticRelCodeAtomicFormulaCodePolynomial bitBound := by
    dsimp only [rightFormula]
    exact relCodeFixedEqFormula_code_length_le_fixed code expectedCode bitBound
      hcodeSize (by omega)
  have handCode :
      (binaryFormulaCode (leftFormula ⋏ rightFormula)).length <=
        syntaxResource := by
    dsimp only [leftFormula, rightFormula, syntaxResource] at hleftAtomicCode hrightAtomicCode ⊢
    simp [binaryFormulaCode] at hleftAtomicCode hrightAtomicCode ⊢
    unfold arithmeticRelCodeValidFormulaCodePolynomial
    omega
  have hraw := transparentHybridConjunctionPayloadBound_le leftCertificate
    rightCertificate childResource childResource hleftResource hrightResource
  have hassembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      relCodeFixedZeroValuation leftFormula rightFormula childResource
      childResource syntaxResource
      (by
        dsimp only [syntaxResource]
        unfold arithmeticRelCodeValidFormulaCodePolynomial
        omega)
      hleftClosed hrightClosed hleftCode hrightCode handCode
  unfold arithmeticRelCodeValidPairFullyFixedPayloadPolynomial
  simpa only [leftFormula, rightFormula, leftCertificate, rightCertificate,
    syntaxResource, childResource] using hraw.trans hassembly

private theorem relCodeValidCase20Certificate_structuralPayloadBound_le_fixed
    (arity code bitBound : Nat)
    (hpair : arity = 2 ∧ code = 0)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (relCodeValidCase20Certificate arity code hpair) <=
      arithmeticRelCodeValidFullyFixedPayloadPolynomial bitBound := by
  let leftFormula :=
    relCodeFixedEqFormula arity 2 ⋏ relCodeFixedEqFormula code 0
  let rightFormula :=
    relCodeFixedEqFormula arity 2 ⋏ relCodeFixedEqFormula code 1
  let pairCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (relCodeFixedEqCertificate arity 2 hpair.1)
      (relCodeFixedEqCertificate code 0 hpair.2)
  let syntaxResource := arithmeticRelCodeValidFormulaCodePolynomial bitBound
  let pairResource :=
    arithmeticRelCodeValidPairFullyFixedPayloadPolynomial bitBound
  have hpairResource :
      hybridFormulaStructuralPayloadBound pairCertificate <= pairResource := by
    dsimp only [pairCertificate, pairResource]
    exact relCodeValidPairCertificate_structuralPayloadBound_le_fixed arity
      code 0 bitBound hpair.1 hpair.2 (by omega) haritySize hcodeSize
  have hleftClosed : leftFormula.freeVariables = ∅ := by simp [leftFormula]
  have hrightClosed : rightFormula.freeVariables = ∅ := by simp [rightFormula]
  have hfullClosed :
      (leftFormula ⋎ rightFormula).freeVariables = ∅ := by
    simp [leftFormula, rightFormula]
  have hfullCode :
      (binaryFormulaCode (leftFormula ⋎ rightFormula)).length <=
        syntaxResource := by
    change (binaryFormulaCode
      (compactAdditiveArithmeticRelCodeValidExplicitFormula arity code)).length <=
        syntaxResource
    rw [← compactAdditiveArithmeticRelCodeValidClosedFormula_alignment]
    exact
      compactAdditiveArithmeticRelCodeValidClosedFormula_code_length_le_fixed
        arity code bitBound haritySize hcodeSize
  have hleftCode :
      (binaryFormulaCode leftFormula).length <= syntaxResource := by
    dsimp only [leftFormula, rightFormula] at hfullCode ⊢
    simp [binaryFormulaCode] at hfullCode ⊢
    omega
  have hrightCode :
      (binaryFormulaCode rightFormula).length <= syntaxResource := by
    dsimp only [leftFormula, rightFormula] at hfullCode ⊢
    simp [binaryFormulaCode] at hfullCode ⊢
    omega
  have hraw := transparentHybridDisjunctionLeftPayloadBound_le
    (right := rightFormula) pairCertificate pairResource hpairResource
  have hassembly := disjunctionLeftEnvelope_le_closed_relCode leftFormula
    rightFormula pairResource syntaxResource
    (by
      dsimp only [syntaxResource]
      unfold arithmeticRelCodeValidFormulaCodePolynomial
      omega)
    hleftClosed hrightClosed hleftCode hrightCode hfullCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := rightFormula) pairCertificate) <=
    arithmeticRelCodeValidFullyFixedPayloadPolynomial bitBound
  unfold arithmeticRelCodeValidFullyFixedPayloadPolynomial
  simpa only [syntaxResource, pairResource] using hraw.trans hassembly

private theorem relCodeValidCase21Certificate_structuralPayloadBound_le_fixed
    (arity code bitBound : Nat)
    (hpair : arity = 2 ∧ code = 1)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (relCodeValidCase21Certificate arity code hpair) <=
      arithmeticRelCodeValidFullyFixedPayloadPolynomial bitBound := by
  let leftFormula :=
    relCodeFixedEqFormula arity 2 ⋏ relCodeFixedEqFormula code 0
  let rightFormula :=
    relCodeFixedEqFormula arity 2 ⋏ relCodeFixedEqFormula code 1
  let pairCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (relCodeFixedEqCertificate arity 2 hpair.1)
      (relCodeFixedEqCertificate code 1 hpair.2)
  let syntaxResource := arithmeticRelCodeValidFormulaCodePolynomial bitBound
  let pairResource :=
    arithmeticRelCodeValidPairFullyFixedPayloadPolynomial bitBound
  have hpairResource :
      hybridFormulaStructuralPayloadBound pairCertificate <= pairResource := by
    dsimp only [pairCertificate, pairResource]
    exact relCodeValidPairCertificate_structuralPayloadBound_le_fixed arity
      code 1 bitBound hpair.1 hpair.2 (by omega) haritySize hcodeSize
  have hleftClosed : leftFormula.freeVariables = ∅ := by simp [leftFormula]
  have hrightClosed : rightFormula.freeVariables = ∅ := by simp [rightFormula]
  have hfullCode :
      (binaryFormulaCode (leftFormula ⋎ rightFormula)).length <=
        syntaxResource := by
    change (binaryFormulaCode
      (compactAdditiveArithmeticRelCodeValidExplicitFormula arity code)).length <=
        syntaxResource
    rw [← compactAdditiveArithmeticRelCodeValidClosedFormula_alignment]
    exact
      compactAdditiveArithmeticRelCodeValidClosedFormula_code_length_le_fixed
        arity code bitBound haritySize hcodeSize
  have hleftCode :
      (binaryFormulaCode leftFormula).length <= syntaxResource := by
    dsimp only [leftFormula, rightFormula] at hfullCode ⊢
    simp [binaryFormulaCode] at hfullCode ⊢
    omega
  have hrightCode :
      (binaryFormulaCode rightFormula).length <= syntaxResource := by
    dsimp only [leftFormula, rightFormula] at hfullCode ⊢
    simp [binaryFormulaCode] at hfullCode ⊢
    omega
  have hraw := transparentHybridDisjunctionRightPayloadBound_le
    (left := leftFormula) pairCertificate pairResource hpairResource
  have hassembly := disjunctionRightEnvelope_le_closed_relCode leftFormula
    rightFormula pairResource syntaxResource
    (by
      dsimp only [syntaxResource]
      unfold arithmeticRelCodeValidFormulaCodePolynomial
      omega)
    hleftClosed hrightClosed hleftCode hrightCode hfullCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := leftFormula) pairCertificate) <=
    arithmeticRelCodeValidFullyFixedPayloadPolynomial bitBound
  unfold arithmeticRelCodeValidFullyFixedPayloadPolynomial
  simpa only [syntaxResource, pairResource] using hraw.trans hassembly

theorem
    compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (arity code bitBound : Nat)
    (hvalid : ArithmeticRelCodeValid arity code)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph
          arity code hvalid) <=
      arithmeticRelCodeValidFullyFixedPayloadPolynomial bitBound := by
  by_cases h20 : arity = 2 ∧ code = 0
  · simpa [compactAdditiveArithmeticRelCodeValidExplicitHybridCertificate,
      compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph,
      h20, hybridFormulaStructuralPayloadBound] using
      relCodeValidCase20Certificate_structuralPayloadBound_le_fixed arity code
        bitBound h20 haritySize hcodeSize
  · have h21 : arity = 2 ∧ code = 1 := by
      unfold ArithmeticRelCodeValid at hvalid
      rcases hvalid with hvalid | hvalid
      · exact False.elim (h20 hvalid)
      · exact hvalid
    simpa [compactAdditiveArithmeticRelCodeValidExplicitHybridCertificate,
      compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph,
      h20, h21, hybridFormulaStructuralPayloadBound] using
      relCodeValidCase21Certificate_structuralPayloadBound_le_fixed arity code
        bitBound h21 haritySize hcodeSize

private theorem relCodeInvalidPairCertificate_structuralPayloadBound_le_fixed
    (left leftExpected right rightExpected bitBound : Nat)
    (hinvalid : ¬(left = leftExpected ∧ right = rightExpected))
    (hleftSize : Nat.size left <= bitBound)
    (hrightSize : Nat.size right <= bitBound)
    (hleftExpected : leftExpected <= 2)
    (hrightExpected : rightExpected <= 2) :
    hybridFormulaStructuralPayloadBound
        (relCodeInvalidPairCertificate left leftExpected right rightExpected
          hinvalid) <=
      arithmeticRelCodeInvalidPairFullyFixedPayloadPolynomial bitBound := by
  let leftFormula := relCodeFixedNeFormula left leftExpected
  let rightFormula := relCodeFixedNeFormula right rightExpected
  let syntaxResource := arithmeticRelCodeInvalidFormulaCodePolynomial bitBound
  let childResource :=
    arithmeticRelCodeNegativeAtomicFixedPayloadPolynomial bitBound
  have hleftClosed : leftFormula.freeVariables = ∅ := by
    simp [leftFormula, relCodeFixedNeFormula]
  have hrightClosed : rightFormula.freeVariables = ∅ := by
    simp [rightFormula, relCodeFixedNeFormula]
  have hleftCode :
      (binaryFormulaCode leftFormula).length <= syntaxResource := by
    have heq := relCodeFixedEqFormula_code_length_le_fixed left leftExpected
      bitBound hleftSize hleftExpected
    have hneg := binaryFormulaCode_neg_length_le
      (relCodeFixedEqFormula left leftExpected)
    dsimp only [leftFormula, syntaxResource]
    unfold relCodeFixedNeFormula arithmeticRelCodeInvalidFormulaCodePolynomial
      arithmeticRelCodeValidFormulaCodePolynomial
    omega
  have hrightCode :
      (binaryFormulaCode rightFormula).length <= syntaxResource := by
    have heq := relCodeFixedEqFormula_code_length_le_fixed right rightExpected
      bitBound hrightSize hrightExpected
    have hneg := binaryFormulaCode_neg_length_le
      (relCodeFixedEqFormula right rightExpected)
    dsimp only [rightFormula, syntaxResource]
    unfold relCodeFixedNeFormula arithmeticRelCodeInvalidFormulaCodePolynomial
      arithmeticRelCodeValidFormulaCodePolynomial
    omega
  have hleftAtomicCode :
      (binaryFormulaCode leftFormula).length <=
        2 * arithmeticRelCodeAtomicFormulaCodePolynomial bitBound +
          (binaryNatCode 3).length + 8 := by
    have heq := relCodeFixedEqFormula_code_length_le_fixed left leftExpected
      bitBound hleftSize hleftExpected
    have hneg := binaryFormulaCode_neg_length_le
      (relCodeFixedEqFormula left leftExpected)
    dsimp only [leftFormula]
    unfold relCodeFixedNeFormula
    omega
  have hrightAtomicCode :
      (binaryFormulaCode rightFormula).length <=
        2 * arithmeticRelCodeAtomicFormulaCodePolynomial bitBound +
          (binaryNatCode 3).length + 8 := by
    have heq := relCodeFixedEqFormula_code_length_le_fixed right rightExpected
      bitBound hrightSize hrightExpected
    have hneg := binaryFormulaCode_neg_length_le
      (relCodeFixedEqFormula right rightExpected)
    dsimp only [rightFormula]
    unfold relCodeFixedNeFormula
    omega
  have horCode :
      (binaryFormulaCode (leftFormula ⋎ rightFormula)).length <=
        syntaxResource := by
    have hraw := binaryFormulaCode_or_length_le leftFormula rightFormula
    have htag3 : (binaryNatCode 3).length <= 32 := by decide
    dsimp only [syntaxResource]
    unfold arithmeticRelCodeInvalidFormulaCodePolynomial
      arithmeticRelCodeValidFormulaCodePolynomial
    omega
  by_cases hleft : left = leftExpected
  · have hright : right ≠ rightExpected := by
      intro hright
      exact hinvalid ⟨hleft, hright⟩
    let certificate := relCodeFixedNeCertificate right rightExpected hright
    have hchild :
        hybridFormulaStructuralPayloadBound certificate <= childResource := by
      dsimp only [certificate, childResource]
      exact relCodeFixedNeCertificate_structuralPayloadBound_le_fixed right
        rightExpected bitBound hright hrightSize hrightExpected
    have hraw := transparentHybridDisjunctionRightPayloadBound_le
      (left := leftFormula) certificate childResource hchild
    have hassembly := disjunctionRightEnvelope_le_closed_relCode leftFormula
      rightFormula childResource syntaxResource
      (by
        dsimp only [syntaxResource]
        unfold arithmeticRelCodeInvalidFormulaCodePolynomial
          arithmeticRelCodeValidFormulaCodePolynomial
        omega)
      hleftClosed hrightClosed hleftCode hrightCode horCode
    simp only [relCodeInvalidPairCertificate]
    rw [dif_pos hleft]
    unfold arithmeticRelCodeInvalidPairFullyFixedPayloadPolynomial
    simpa only [leftFormula, rightFormula, certificate, syntaxResource,
      childResource] using hraw.trans hassembly
  · let certificate := relCodeFixedNeCertificate left leftExpected hleft
    have hchild :
        hybridFormulaStructuralPayloadBound certificate <= childResource := by
      dsimp only [certificate, childResource]
      exact relCodeFixedNeCertificate_structuralPayloadBound_le_fixed left
        leftExpected bitBound hleft hleftSize hleftExpected
    have hraw := transparentHybridDisjunctionLeftPayloadBound_le
      (right := rightFormula) certificate childResource hchild
    have hassembly := disjunctionLeftEnvelope_le_closed_relCode leftFormula
      rightFormula childResource syntaxResource
      (by
        dsimp only [syntaxResource]
        unfold arithmeticRelCodeInvalidFormulaCodePolynomial
          arithmeticRelCodeValidFormulaCodePolynomial
        omega)
      hleftClosed hrightClosed hleftCode hrightCode horCode
    simp only [relCodeInvalidPairCertificate]
    rw [dif_neg hleft]
    unfold arithmeticRelCodeInvalidPairFullyFixedPayloadPolynomial
    simpa only [leftFormula, rightFormula, certificate, syntaxResource,
      childResource] using hraw.trans hassembly

theorem
    compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (arity code bitBound : Nat)
    (hinvalid : ¬ArithmeticRelCodeValid arity code)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
          arity code hinvalid) <=
      arithmeticRelCodeInvalidFullyFixedPayloadPolynomial bitBound := by
  have h20 : ¬(arity = 2 ∧ code = 0) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticRelCodeValid, hpair])
  have h21 : ¬(arity = 2 ∧ code = 1) := by
    intro hpair
    exact hinvalid (by simp [ArithmeticRelCodeValid, hpair])
  let certificate20 := relCodeInvalidPairCertificate arity 2 code 0 h20
  let certificate21 := relCodeInvalidPairCertificate arity 2 code 1 h21
  let pair20 := relCodeFixedNeFormula arity 2 ⋎
    relCodeFixedNeFormula code 0
  let pair21 := relCodeFixedNeFormula arity 2 ⋎
    relCodeFixedNeFormula code 1
  let syntaxResource := arithmeticRelCodeInvalidFormulaCodePolynomial bitBound
  let pairResource :=
    arithmeticRelCodeInvalidPairFullyFixedPayloadPolynomial bitBound
  have hresource20 :
      hybridFormulaStructuralPayloadBound certificate20 <= pairResource := by
    dsimp only [certificate20, pairResource]
    exact relCodeInvalidPairCertificate_structuralPayloadBound_le_fixed
      arity 2 code 0 bitBound h20 haritySize hcodeSize (by omega) (by omega)
  have hresource21 :
      hybridFormulaStructuralPayloadBound certificate21 <= pairResource := by
    dsimp only [certificate21, pairResource]
    exact relCodeInvalidPairCertificate_structuralPayloadBound_le_fixed
      arity 2 code 1 bitBound h21 haritySize hcodeSize (by omega) (by omega)
  have hpair20Closed : pair20.freeVariables = ∅ := by
    simp [pair20, relCodeFixedNeFormula]
  have hpair21Closed : pair21.freeVariables = ∅ := by
    simp [pair21, relCodeFixedNeFormula]
  have hfullCode :
      (binaryFormulaCode (pair20 ⋏ pair21)).length <= syntaxResource := by
    change (binaryFormulaCode
      (compactAdditiveArithmeticRelCodeInvalidExplicitFormula arity code)).length <=
        syntaxResource
    rw [← compactAdditiveArithmeticRelCodeInvalidClosedFormula_alignment]
    exact
      compactAdditiveArithmeticRelCodeInvalidClosedFormula_code_length_le_fixed
        arity code bitBound haritySize hcodeSize
  have hpair20Code :
      (binaryFormulaCode pair20).length <= syntaxResource := by
    dsimp only [pair20, pair21] at hfullCode ⊢
    simp [binaryFormulaCode] at hfullCode ⊢
    omega
  have hpair21Code :
      (binaryFormulaCode pair21).length <= syntaxResource := by
    dsimp only [pair20, pair21] at hfullCode ⊢
    simp [binaryFormulaCode] at hfullCode ⊢
    omega
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    certificate20 certificate21
  have hraw := transparentHybridConjunctionPayloadBound_le certificate20
    certificate21 pairResource pairResource hresource20 hresource21
  have hassembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      relCodeFixedZeroValuation pair20 pair21 pairResource pairResource
      syntaxResource
      (by
        dsimp only [syntaxResource]
        unfold arithmeticRelCodeInvalidFormulaCodePolynomial
          arithmeticRelCodeValidFormulaCodePolynomial
        omega)
      hpair20Closed hpair21Closed hpair20Code hpair21Code hfullCode
  unfold compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
    compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificate
    arithmeticRelCodeInvalidFullyFixedPayloadPolynomial
  simpa only [certificate20, certificate21, pair20, pair21, syntaxResource,
    pairResource, direct, hybridFormulaStructuralPayloadBound] using
      hraw.trans hassembly

#print axioms
  compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
#print axioms
  compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectArithmeticRelCodeValidFullyFixedBounds
