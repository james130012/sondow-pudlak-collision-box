import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinuePublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierPublicBounds
import integration.FoundationCompactNumericListedDirectArithmeticRelCodeValidPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resources for the syntax-formula branch tree

Each checked branch datum determines one explicit certificate tree.  Atomic
comparisons and child graphs are charged before the original conjunction and
disjunction paths are reconstructed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactArithmeticSymbolCode
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermContinuePublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierPublicBounds
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticRelCodeValidPublicBounds

private abbrev formulaZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation

private abbrev natListAtZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private abbrev relCodeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate.zeroValuation

private abbrev fixedNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
    value

private abbrev FormulaHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate formulaZeroValuation formula

private theorem fixedNumeralTerm_freeVariables_eq_empty (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  unfold fixedNumeralTerm
  unfold
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem natListAtFixedNumeralTerm_value (value : Nat) :
    termValue
        FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
        (fixedNumeralTerm value) = value := by
  simp

def syntaxFormulaNativeEqPayloadPolynomial (value expected : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial formulaZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]

theorem nativeEqCertificate_structuralPayloadBound_le_public
    (value expected : Nat) (heq : value = expected) :
    hybridFormulaStructuralPayloadBound
        (nativeEqCertificate value expected heq) <=
      syntaxFormulaNativeEqPayloadPolynomial value expected := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (fixedNumeralTerm expected).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    formulaZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] hleft hright
  change compilePositiveRelationPayloadResource formulaZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] <= _
  exact hpublic

def syntaxFormulaNativeNePayloadPolynomial (value expected : Nat) : Nat :=
  compileNegativeRelationPayloadPolynomial formulaZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]

theorem nativeNeCertificate_structuralPayloadBound_le_public
    (value expected : Nat) (hne : value ≠ expected) :
    hybridFormulaStructuralPayloadBound
        (nativeNeCertificate value expected hne) <=
      syntaxFormulaNativeNePayloadPolynomial value expected := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (fixedNumeralTerm expected).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compileNegativeRelationPayloadResource_le_publicPolynomial
    formulaZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] hleft hright
  change compileNegativeRelationPayloadResource formulaZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] <= _
  exact hpublic

def syntaxFormulaTermLePayloadEnvelope
    (left right : Nat) (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := Semiformula.rel Language.Eq.eq args
  let strictFormula := Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables
    formulaZeroValuation
  compilePositiveRelationPayloadPolynomial formulaZeroValuation
      Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial formulaZeroValuation
      Language.ORing.Rel.lt args +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert equalityFormula Gamma) +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert strictFormula Gamma) +
    FoundationCompactCertifiedContextProof.CertifiedPAContextProof.disjunctionFullAssemblyCost
      Gamma equalityFormula strictFormula

theorem termLeCertificate_structuralPayloadBound_le_public
    (left right : Nat) (leftTerm rightTerm : ValuationTerm)
    (hleftClosed : leftTerm.freeVariables ⊆ {0})
    (hrightClosed : rightTerm.freeVariables ⊆ {0})
    (hleft : termValue formulaZeroValuation leftTerm = left)
    (hright : termValue formulaZeroValuation rightTerm = right)
    (hle : left <= right) :
    hybridFormulaStructuralPayloadBound
        (termLeCertificate left right leftTerm rightTerm hleft hright hle) <=
      syntaxFormulaTermLePayloadEnvelope left right leftTerm rightTerm := by
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  have hequality :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      formulaZeroValuation Language.Eq.eq args hleftClosed hrightClosed
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      formulaZeroValuation Language.ORing.Rel.lt args hleftClosed hrightClosed
  by_cases heq : left = right
  · simp only [termLeCertificate, termLeFormula, id_eq]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold syntaxFormulaTermLePayloadEnvelope
    dsimp only [args, formulaZeroValuation] at hequality hstrict ⊢
    omega
  · simp only [termLeCertificate, termLeFormula, id_eq]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold syntaxFormulaTermLePayloadEnvelope
    dsimp only [args, formulaZeroValuation] at hequality hstrict ⊢
    omega

def syntaxFormulaShortNativeLePayloadEnvelope (left right : Nat) : Nat :=
  syntaxFormulaTermLePayloadEnvelope left right (shortBinaryNumeralTerm left)
    (fixedNumeralTerm right)

theorem shortNativeLeCertificate_structuralPayloadBound_le_public
    (left right : Nat) (hle : left <= right) :
    hybridFormulaStructuralPayloadBound
        (shortNativeLeCertificate left right hle) <=
      syntaxFormulaShortNativeLePayloadEnvelope left right := by
  have hleftClosed : (shortBinaryNumeralTerm left).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hrightClosed : (fixedNumeralTerm right).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  simpa only [shortNativeLeCertificate, shortNativeLeFormula, id_eq,
    syntaxFormulaShortNativeLePayloadEnvelope] using
    termLeCertificate_structuralPayloadBound_le_public left right
      (shortBinaryNumeralTerm left) (fixedNumeralTerm right)
      hleftClosed hrightClosed (by simp [termValue_shortBinaryNumeralTerm])
      (by simp) hle

def syntaxFormulaNativeShortLePayloadEnvelope (left right : Nat) : Nat :=
  syntaxFormulaTermLePayloadEnvelope left right (fixedNumeralTerm left)
    (shortBinaryNumeralTerm right)

theorem nativeShortLeCertificate_structuralPayloadBound_le_public
    (left right : Nat) (hle : left <= right) :
    hybridFormulaStructuralPayloadBound
        (nativeShortLeCertificate left right hle) <=
      syntaxFormulaNativeShortLePayloadEnvelope left right := by
  have hleftClosed : (fixedNumeralTerm left).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hrightClosed : (shortBinaryNumeralTerm right).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  simpa only [nativeShortLeCertificate, nativeShortLeFormula, id_eq,
    syntaxFormulaNativeShortLePayloadEnvelope] using
    termLeCertificate_structuralPayloadBound_le_public left right
      (fixedNumeralTerm left) (shortBinaryNumeralTerm right)
      hleftClosed hrightClosed (by simp)
      (by simp [termValue_shortBinaryNumeralTerm]) hle

noncomputable def syntaxFormulaNativeEqEitherPayloadEnvelope
    (value left right : Nat)
    (data : NativeEqEitherCheckedData value left right) : Nat :=
  match data with
  | .left _ =>
      transparentHybridDisjunctionLeftPayloadEnvelope formulaZeroValuation
        (nativeEqFormula value left) (nativeEqFormula value right)
        (syntaxFormulaNativeEqPayloadPolynomial value left)
  | .right _ =>
      transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
        (nativeEqFormula value left) (nativeEqFormula value right)
        (syntaxFormulaNativeEqPayloadPolynomial value right)

theorem
    nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
    (value left right : Nat)
    (data : NativeEqEitherCheckedData value left right) :
    hybridFormulaStructuralPayloadBound
        (nativeEqEitherCertificateFromData value left right data) <=
      syntaxFormulaNativeEqEitherPayloadEnvelope value left right data := by
  cases data with
  | left hleft =>
      have heq := nativeEqCertificate_structuralPayloadBound_le_public value
        left hleft
      have hpath := transparentHybridDisjunctionLeftPayloadBound_le
        (right := nativeEqFormula value right)
        (nativeEqCertificate value left hleft) _ heq
      unfold nativeEqEitherCertificateFromData
        syntaxFormulaNativeEqEitherPayloadEnvelope
      exact hpath
  | right hright =>
      have heq := nativeEqCertificate_structuralPayloadBound_le_public value
        right hright
      have hpath := transparentHybridDisjunctionRightPayloadBound_le
        (left := nativeEqFormula value left)
        (nativeEqCertificate value right hright) _ heq
      unfold nativeEqEitherCertificateFromData
        syntaxFormulaNativeEqEitherPayloadEnvelope
      exact hpath

def syntaxFormulaRelationSelectedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  (nativeEqFormula witness.tag 0 ⋎ nativeEqFormula witness.tag 1) ⋏
    compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
      width tokenCount current next binderArity witness

def syntaxFormulaLogicalSelectedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  (nativeEqFormula witness.tag 2 ⋎ nativeEqFormula witness.tag 3) ⋏
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount 1

def syntaxFormulaBinarySelectedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  (nativeEqFormula witness.tag 4 ⋎ nativeEqFormula witness.tag 5) ⋏
    compactUnifiedParserSyntaxFormulaBinaryClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity

def syntaxFormulaQuantifierSelectedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  (nativeEqFormula witness.tag 6 ⋎ nativeEqFormula witness.tag 7) ⋏
    compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity

def syntaxFormulaInvalidTagSelectedFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : ValuationFormula :=
  nativeNeFormula witness.tag 0 ⋏
    nativeNeFormula witness.tag 1 ⋏
    nativeNeFormula witness.tag 2 ⋏
    nativeNeFormula witness.tag 3 ⋏
    nativeNeFormula witness.tag 4 ⋏
    nativeNeFormula witness.tag 5 ⋏
    nativeNeFormula witness.tag 6 ⋏
    nativeNeFormula witness.tag 7 ⋏
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount

theorem syntaxFormulaTagBranchExplicitFormula_component_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness =
      syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current
          next binderArity witness ⋎
        syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current
            next witness ⋎
          syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current
              next binderArity witness ⋎
            syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
                current next binderArity witness ⋎
              syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
                current next witness := by
  rfl

def syntaxFormulaTagRelationPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (selectedResource : Nat) : Nat :=
  let relationFormula := syntaxFormulaRelationSelectedFormula tokenTable width
    tokenCount current next binderArity witness
  let logicalFormula := syntaxFormulaLogicalSelectedFormula tokenTable width
    tokenCount current next witness
  let binaryFormula := syntaxFormulaBinarySelectedFormula tokenTable width
    tokenCount current next binderArity witness
  let quantifierFormula := syntaxFormulaQuantifierSelectedFormula tokenTable
    width tokenCount current next binderArity witness
  let invalidFormula := syntaxFormulaInvalidTagSelectedFormula tokenTable width
    tokenCount current next witness
  transparentHybridDisjunctionLeftPayloadEnvelope formulaZeroValuation
    relationFormula
    (logicalFormula ⋎ binaryFormula ⋎ quantifierFormula ⋎ invalidFormula)
    selectedResource

theorem syntaxFormulaTagRelationPathPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (selected : FormulaHybridCertificate
      (syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current
        next binderArity witness))
    (selectedResource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <=
      selectedResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
                current next witness ⋎
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
          selected) <=
      syntaxFormulaTagRelationPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness selectedResource := by
  exact transparentHybridDisjunctionLeftPayloadBound_le selected _ hselected

def syntaxFormulaTagLogicalPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (selectedResource : Nat) : Nat :=
  let relationFormula := syntaxFormulaRelationSelectedFormula tokenTable width
    tokenCount current next binderArity witness
  let logicalFormula := syntaxFormulaLogicalSelectedFormula tokenTable width
    tokenCount current next witness
  let binaryFormula := syntaxFormulaBinarySelectedFormula tokenTable width
    tokenCount current next binderArity witness
  let quantifierFormula := syntaxFormulaQuantifierSelectedFormula tokenTable
    width tokenCount current next binderArity witness
  let invalidFormula := syntaxFormulaInvalidTagSelectedFormula tokenTable width
    tokenCount current next witness
  let tailResource := transparentHybridDisjunctionLeftPayloadEnvelope
    formulaZeroValuation logicalFormula
    (binaryFormula ⋎ quantifierFormula ⋎ invalidFormula) selectedResource
  transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
    relationFormula
    (logicalFormula ⋎ binaryFormula ⋎ quantifierFormula ⋎ invalidFormula)
    tailResource

theorem syntaxFormulaTagLogicalPathPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (selected : FormulaHybridCertificate
      (syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current
        next witness))
    (selectedResource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <=
      selectedResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := syntaxFormulaRelationSelectedFormula tokenTable width
            tokenCount current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right :=
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
            selected)) <=
      syntaxFormulaTagLogicalPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness selectedResource := by
  let tail := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
        current next binderArity witness ⋎
      syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount current
          next binderArity witness ⋎
        syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
          current next witness) selected
  have htail := transparentHybridDisjunctionLeftPayloadBound_le
    (right := syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
        current next binderArity witness ⋎
      syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount current
          next binderArity witness ⋎
        syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
          current next witness)
    selected _ hselected
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
      current next binderArity witness) tail _ htail
  unfold syntaxFormulaTagLogicalPathPayloadEnvelope
  simpa only [tail] using houter

def syntaxFormulaTagBinaryPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (selectedResource : Nat) : Nat :=
  let relationFormula := syntaxFormulaRelationSelectedFormula tokenTable width
    tokenCount current next binderArity witness
  let logicalFormula := syntaxFormulaLogicalSelectedFormula tokenTable width
    tokenCount current next witness
  let binaryFormula := syntaxFormulaBinarySelectedFormula tokenTable width
    tokenCount current next binderArity witness
  let quantifierFormula := syntaxFormulaQuantifierSelectedFormula tokenTable
    width tokenCount current next binderArity witness
  let invalidFormula := syntaxFormulaInvalidTagSelectedFormula tokenTable width
    tokenCount current next witness
  let binaryTailResource := transparentHybridDisjunctionLeftPayloadEnvelope
    formulaZeroValuation binaryFormula (quantifierFormula ⋎ invalidFormula)
    selectedResource
  let logicalTailResource := transparentHybridDisjunctionRightPayloadEnvelope
    formulaZeroValuation logicalFormula
    (binaryFormula ⋎ quantifierFormula ⋎ invalidFormula) binaryTailResource
  transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
    relationFormula
    (logicalFormula ⋎ binaryFormula ⋎ quantifierFormula ⋎ invalidFormula)
    logicalTailResource

theorem syntaxFormulaTagBinaryPathPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (selected : FormulaHybridCertificate
      (syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current
        next binderArity witness))
    (selectedResource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <=
      selectedResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := syntaxFormulaRelationSelectedFormula tokenTable width
            tokenCount current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := syntaxFormulaLogicalSelectedFormula tokenTable width
              tokenCount current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right :=
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
              selected))) <=
      syntaxFormulaTagBinaryPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness selectedResource := by
  let binaryTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := syntaxFormulaQuantifierSelectedFormula tokenTable width
          tokenCount current next binderArity witness ⋎
        syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
          current next witness) selected
  have hbinaryTail := transparentHybridDisjunctionLeftPayloadBound_le
    (right := syntaxFormulaQuantifierSelectedFormula tokenTable width
        tokenCount current next binderArity witness ⋎
      syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
        current next witness)
    selected _ hselected
  let logicalTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
        current next witness) binaryTail
  have hlogicalTail := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
      current next witness) binaryTail _ hbinaryTail
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
      current next binderArity witness) logicalTail _ hlogicalTail
  unfold syntaxFormulaTagBinaryPathPayloadEnvelope
  simpa only [binaryTail, logicalTail] using houter

def syntaxFormulaTagQuantifierPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (selectedResource : Nat) : Nat :=
  let relationFormula := syntaxFormulaRelationSelectedFormula tokenTable width
    tokenCount current next binderArity witness
  let logicalFormula := syntaxFormulaLogicalSelectedFormula tokenTable width
    tokenCount current next witness
  let binaryFormula := syntaxFormulaBinarySelectedFormula tokenTable width
    tokenCount current next binderArity witness
  let quantifierFormula := syntaxFormulaQuantifierSelectedFormula tokenTable
    width tokenCount current next binderArity witness
  let invalidFormula := syntaxFormulaInvalidTagSelectedFormula tokenTable width
    tokenCount current next witness
  let quantifierTailResource := transparentHybridDisjunctionLeftPayloadEnvelope
    formulaZeroValuation quantifierFormula invalidFormula selectedResource
  let binaryTailResource := transparentHybridDisjunctionRightPayloadEnvelope
    formulaZeroValuation binaryFormula (quantifierFormula ⋎ invalidFormula)
    quantifierTailResource
  let logicalTailResource := transparentHybridDisjunctionRightPayloadEnvelope
    formulaZeroValuation logicalFormula
    (binaryFormula ⋎ quantifierFormula ⋎ invalidFormula) binaryTailResource
  transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
    relationFormula
    (logicalFormula ⋎ binaryFormula ⋎ quantifierFormula ⋎ invalidFormula)
    logicalTailResource

theorem syntaxFormulaTagQuantifierPathPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (selected : FormulaHybridCertificate
      (syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
        current next binderArity witness))
    (selectedResource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <=
      selectedResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := syntaxFormulaRelationSelectedFormula tokenTable width
            tokenCount current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := syntaxFormulaLogicalSelectedFormula tokenTable width
              tokenCount current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := syntaxFormulaBinarySelectedFormula tokenTable width
                tokenCount current next binderArity witness)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right := syntaxFormulaInvalidTagSelectedFormula tokenTable
                  width tokenCount current next witness)
                selected)))) <=
      syntaxFormulaTagQuantifierPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness selectedResource := by
  let quantifierTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := syntaxFormulaInvalidTagSelectedFormula tokenTable width
        tokenCount current next witness) selected
  have hquantifierTail := transparentHybridDisjunctionLeftPayloadBound_le
    (right := syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
      current next witness) selected _ hselected
  let binaryTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
        current next binderArity witness) quantifierTail
  have hbinaryTail := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
      current next binderArity witness) quantifierTail _ hquantifierTail
  let logicalTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
        current next witness) binaryTail
  have hlogicalTail := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
      current next witness) binaryTail _ hbinaryTail
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
      current next binderArity witness) logicalTail _ hlogicalTail
  unfold syntaxFormulaTagQuantifierPathPayloadEnvelope
  simpa only [quantifierTail, binaryTail, logicalTail] using houter

def syntaxFormulaTagInvalidPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (selectedResource : Nat) : Nat :=
  let relationFormula := syntaxFormulaRelationSelectedFormula tokenTable width
    tokenCount current next binderArity witness
  let logicalFormula := syntaxFormulaLogicalSelectedFormula tokenTable width
    tokenCount current next witness
  let binaryFormula := syntaxFormulaBinarySelectedFormula tokenTable width
    tokenCount current next binderArity witness
  let quantifierFormula := syntaxFormulaQuantifierSelectedFormula tokenTable
    width tokenCount current next binderArity witness
  let invalidFormula := syntaxFormulaInvalidTagSelectedFormula tokenTable width
    tokenCount current next witness
  let quantifierTailResource := transparentHybridDisjunctionRightPayloadEnvelope
    formulaZeroValuation quantifierFormula invalidFormula selectedResource
  let binaryTailResource := transparentHybridDisjunctionRightPayloadEnvelope
    formulaZeroValuation binaryFormula (quantifierFormula ⋎ invalidFormula)
    quantifierTailResource
  let logicalTailResource := transparentHybridDisjunctionRightPayloadEnvelope
    formulaZeroValuation logicalFormula
    (binaryFormula ⋎ quantifierFormula ⋎ invalidFormula) binaryTailResource
  transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
    relationFormula
    (logicalFormula ⋎ binaryFormula ⋎ quantifierFormula ⋎ invalidFormula)
    logicalTailResource

theorem syntaxFormulaTagInvalidPathPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (selected : FormulaHybridCertificate
      (syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
        current next witness))
    (selectedResource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected <=
      selectedResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := syntaxFormulaRelationSelectedFormula tokenTable width
            tokenCount current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := syntaxFormulaLogicalSelectedFormula tokenTable width
              tokenCount current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := syntaxFormulaBinarySelectedFormula tokenTable width
                tokenCount current next binderArity witness)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := syntaxFormulaQuantifierSelectedFormula tokenTable
                  width tokenCount current next binderArity witness)
                selected)))) <=
      syntaxFormulaTagInvalidPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness selectedResource := by
  let quantifierTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxFormulaQuantifierSelectedFormula tokenTable width
        tokenCount current next binderArity witness) selected
  have hquantifierTail := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
      current next binderArity witness) selected _ hselected
  let binaryTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
        current next binderArity witness) quantifierTail
  have hbinaryTail := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
      current next binderArity witness) quantifierTail _ hquantifierTail
  let logicalTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
        current next witness) binaryTail
  have hlogicalTail := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
      current next witness) binaryTail _ hbinaryTail
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
      current next binderArity witness) logicalTail _ hlogicalTail
  unfold syntaxFormulaTagInvalidPathPayloadEnvelope
  simpa only [quantifierTail, binaryTail, logicalTail] using houter

noncomputable def syntaxFormulaRelationShortBodyPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  let shortFormula := shortNativeLeFormula current.tokensCount 2 ⋏
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  let longFormula := nativeShortLeFormula 3 current.tokensCount ⋏
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.relationArity (fixedNumeralTerm 1) ⋏
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.relationCode (fixedNumeralTerm 2) ⋏
    ((compactAdditiveArithmeticRelCodeValidClosedFormula witness.relationArity
          witness.relationCode ⋏
        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity witness.relationArity) ⋎
      (compactAdditiveArithmeticRelCodeInvalidClosedFormula
            witness.relationArity witness.relationCode ⋏
        compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
          tokenCount current next witness.tailBoundary witness.tailCount))
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (shortNativeLeFormula current.tokensCount 2)
    (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (syntaxFormulaShortNativeLePayloadEnvelope current.tokensCount 2)
    (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount hfailure)
  transparentHybridDisjunctionLeftPayloadEnvelope formulaZeroValuation
    shortFormula longFormula selectedResource

theorem syntaxFormulaRelationShortBodyPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hshort : current.tokensCount <= 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := nativeShortLeFormula 3 current.tokensCount ⋏
            compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable
              width tokenCount current.tokensBoundary current.tokensCount
              witness.relationArity (fixedNumeralTerm 1) ⋏
            compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable
              width tokenCount current.tokensBoundary current.tokensCount
              witness.relationCode (fixedNumeralTerm 2) ⋏
            ((compactAdditiveArithmeticRelCodeValidClosedFormula
                    witness.relationArity witness.relationCode ⋏
                compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
                  tokenTable width tokenCount current next witness.tailBoundary
                  witness.tailCount binderArity witness.relationArity) ⋎
              (compactAdditiveArithmeticRelCodeInvalidClosedFormula
                      witness.relationArity witness.relationCode ⋏
                compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable
                  width tokenCount current next witness.tailBoundary
                  witness.tailCount)))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (shortNativeLeCertificate current.tokensCount 2 hshort)
            (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary
              witness.tailCount hfailure))) <=
      syntaxFormulaRelationShortBodyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hfailure := by
  let shortCertificate := shortNativeLeCertificate current.tokensCount 2 hshort
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  have hshortResource :=
    shortNativeLeCertificate_structuralPayloadBound_le_public
      current.tokensCount 2 hshort
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    shortCertificate failureCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    shortCertificate failureCertificate _ _ hshortResource hfailureResource
  have houter := transparentHybridDisjunctionLeftPayloadBound_le
    (right := nativeShortLeFormula 3 current.tokensCount ⋏
      compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount
        witness.relationArity (fixedNumeralTerm 1) ⋏
      compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount
        witness.relationCode (fixedNumeralTerm 2) ⋏
      ((compactAdditiveArithmeticRelCodeValidClosedFormula
              witness.relationArity witness.relationCode ⋏
          compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount binderArity witness.relationArity) ⋎
        (compactAdditiveArithmeticRelCodeInvalidClosedFormula
                witness.relationArity witness.relationCode ⋏
          compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
            tokenCount current next witness.tailBoundary witness.tailCount)))
    selected _ hselected
  unfold syntaxFormulaRelationShortBodyPayloadEnvelope
  simpa only [shortCertificate, failureCertificate, selected] using houter

noncomputable def syntaxFormulaRelationValidBodyPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.relationArity) : Nat :=
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  let functionFormula :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.relationArity
  let atArityFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.relationArity (fixedNumeralTerm 1)
  let atCodeFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount witness.relationCode
      (fixedNumeralTerm 2)
  let validFormula := compactAdditiveArithmeticRelCodeValidClosedFormula
    witness.relationArity witness.relationCode ⋏ functionFormula
  let invalidFormula := compactAdditiveArithmeticRelCodeInvalidClosedFormula
    witness.relationArity witness.relationCode ⋏ failureFormula
  let shortFormula := shortNativeLeFormula current.tokensCount 2 ⋏
    failureFormula
  let validResource := transparentHybridConjunctionPayloadEnvelope
    relCodeZeroValuation
    (compactAdditiveArithmeticRelCodeValidClosedFormula witness.relationArity
      witness.relationCode) functionFormula
    (compactAdditiveArithmeticRelCodeValidPayloadEnvelope
      witness.relationArity witness.relationCode)
    (compactUnifiedParserSyntaxTermFunctionGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.relationArity hfunction)
  let codeBranchResource := transparentHybridDisjunctionLeftPayloadEnvelope
    relCodeZeroValuation validFormula invalidFormula validResource
  let codeTailResource := transparentHybridConjunctionPayloadEnvelope
    natListAtZeroValuation atCodeFormula (validFormula ⋎ invalidFormula)
    (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount 2
      witness.relationCode (fixedNumeralTerm 2)
      (natListAtFixedNumeralTerm_value 2) hatCode) codeBranchResource
  let arityTailResource := transparentHybridConjunctionPayloadEnvelope
    natListAtZeroValuation atArityFormula
    (atCodeFormula ⋏ (validFormula ⋎ invalidFormula))
    (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount 1
      witness.relationArity (fixedNumeralTerm 1)
      (natListAtFixedNumeralTerm_value 1) hatArity) codeTailResource
  let longResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeShortLeFormula 3 current.tokensCount)
    (atArityFormula ⋏ atCodeFormula ⋏ (validFormula ⋎ invalidFormula))
    (syntaxFormulaNativeShortLePayloadEnvelope 3 current.tokensCount)
    arityTailResource
  transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
    shortFormula
    (nativeShortLeFormula 3 current.tokensCount ⋏ atArityFormula ⋏
      atCodeFormula ⋏ (validFormula ⋎ invalidFormula)) longResource

theorem syntaxFormulaRelationValidBodyPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hthree : 3 <= current.tokensCount)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hvalid : ArithmeticRelCodeValid witness.relationArity
      witness.relationCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.relationArity) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := shortNativeLeFormula current.tokensCount 2 ⋏
            compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
              tokenCount current next witness.tailBoundary witness.tailCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 3 current.tokensCount hthree)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 1 witness.relationArity
                (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                hatArity)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 2 witness.relationCode
                  (fixedNumeralTerm 2) (natListAtFixedNumeralTerm_value 2)
                  hatCode)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  (right :=
                    compactAdditiveArithmeticRelCodeInvalidClosedFormula
                        witness.relationArity witness.relationCode ⋏
                      compactUnifiedParserSyntaxTermFailureClosedFormula
                        tokenTable width tokenCount current next
                        witness.tailBoundary witness.tailCount)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph
                      witness.relationArity witness.relationCode hvalid)
                    (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current next
                      witness.tailBoundary witness.tailCount binderArity
                      witness.relationArity hfunction))))))) <=
      syntaxFormulaRelationValidBodyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hatArity hatCode hfunction := by
  have hindexClosed (index : Nat) :
      (fixedNumeralTerm index).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  let countCertificate := nativeShortLeCertificate 3 current.tokensCount hthree
  let arityCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
      witness.relationArity (fixedNumeralTerm 1)
      (natListAtFixedNumeralTerm_value 1) hatArity
  let codeCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
      witness.relationCode (fixedNumeralTerm 2)
      (natListAtFixedNumeralTerm_value 2) hatCode
  let validCertificate :=
    compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph
      witness.relationArity witness.relationCode hvalid
  let functionCertificate :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity witness.relationArity hfunction
  have hcount := nativeShortLeCertificate_structuralPayloadBound_le_public 3
    current.tokensCount hthree
  have harity :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
      witness.relationArity (fixedNumeralTerm 1) (hindexClosed 1)
      (natListAtFixedNumeralTerm_value 1) hatArity
  have hcode :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
      witness.relationCode (fixedNumeralTerm 2) (hindexClosed 2)
      (natListAtFixedNumeralTerm_value 2) hatCode
  have hvalidResource :=
    compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      witness.relationArity witness.relationCode hvalid
  have hfunctionResource :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity witness.relationArity hfunction
  let validPair := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    validCertificate functionCertificate
  have hvalidPair := transparentHybridConjunctionPayloadBound_le
    validCertificate functionCertificate _ _ hvalidResource hfunctionResource
  let codeBranch :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := compactAdditiveArithmeticRelCodeInvalidClosedFormula
            witness.relationArity witness.relationCode ⋏
        compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
          tokenCount current next witness.tailBoundary witness.tailCount)
      validPair
  have hcodeBranch := transparentHybridDisjunctionLeftPayloadBound_le
    (right := compactAdditiveArithmeticRelCodeInvalidClosedFormula
          witness.relationArity witness.relationCode ⋏
      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
    validPair _ hvalidPair
  let codeTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    codeCertificate codeBranch
  have hcodeTail := transparentHybridConjunctionPayloadBound_le codeCertificate
    codeBranch _ _ hcode hcodeBranch
  let arityTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    arityCertificate codeTail
  have harityTail := transparentHybridConjunctionPayloadBound_le
    arityCertificate codeTail _ _ harity hcodeTail
  let longCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      arityTail
  have hlong := transparentHybridConjunctionPayloadBound_le countCertificate
    arityTail _ _ hcount harityTail
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := shortNativeLeFormula current.tokensCount 2 ⋏
      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
    longCertificate _ hlong
  unfold syntaxFormulaRelationValidBodyPayloadEnvelope
  exact houter

noncomputable def syntaxFormulaRelationInvalidBodyPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  let functionFormula :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.relationArity
  let atArityFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.relationArity (fixedNumeralTerm 1)
  let atCodeFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount witness.relationCode
      (fixedNumeralTerm 2)
  let validFormula := compactAdditiveArithmeticRelCodeValidClosedFormula
    witness.relationArity witness.relationCode ⋏ functionFormula
  let invalidFormula := compactAdditiveArithmeticRelCodeInvalidClosedFormula
    witness.relationArity witness.relationCode ⋏ failureFormula
  let shortFormula := shortNativeLeFormula current.tokensCount 2 ⋏
    failureFormula
  let invalidResource := transparentHybridConjunctionPayloadEnvelope
    relCodeZeroValuation
    (compactAdditiveArithmeticRelCodeInvalidClosedFormula witness.relationArity
      witness.relationCode) failureFormula
    (compactAdditiveArithmeticRelCodeInvalidPayloadEnvelope
      witness.relationArity witness.relationCode)
    (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount hfailure)
  let codeBranchResource := transparentHybridDisjunctionRightPayloadEnvelope
    relCodeZeroValuation validFormula invalidFormula invalidResource
  let codeTailResource := transparentHybridConjunctionPayloadEnvelope
    natListAtZeroValuation atCodeFormula (validFormula ⋎ invalidFormula)
    (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount 2
      witness.relationCode (fixedNumeralTerm 2)
      (natListAtFixedNumeralTerm_value 2) hatCode) codeBranchResource
  let arityTailResource := transparentHybridConjunctionPayloadEnvelope
    natListAtZeroValuation atArityFormula
    (atCodeFormula ⋏ (validFormula ⋎ invalidFormula))
    (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount 1
      witness.relationArity (fixedNumeralTerm 1)
      (natListAtFixedNumeralTerm_value 1) hatArity) codeTailResource
  let longResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeShortLeFormula 3 current.tokensCount)
    (atArityFormula ⋏ atCodeFormula ⋏ (validFormula ⋎ invalidFormula))
    (syntaxFormulaNativeShortLePayloadEnvelope 3 current.tokensCount)
    arityTailResource
  transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
    shortFormula
    (nativeShortLeFormula 3 current.tokensCount ⋏ atArityFormula ⋏
      atCodeFormula ⋏ (validFormula ⋎ invalidFormula)) longResource

theorem syntaxFormulaRelationInvalidBodyPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hthree : 3 <= current.tokensCount)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hinvalid : ¬ArithmeticRelCodeValid witness.relationArity
      witness.relationCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := shortNativeLeFormula current.tokensCount 2 ⋏
            compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
              tokenCount current next witness.tailBoundary witness.tailCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 3 current.tokensCount hthree)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 1 witness.relationArity
                (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                hatArity)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 2 witness.relationCode
                  (fixedNumeralTerm 2) (natListAtFixedNumeralTerm_value 2)
                  hatCode)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (left :=
                    compactAdditiveArithmeticRelCodeValidClosedFormula
                        witness.relationArity witness.relationCode ⋏
                      compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
                        tokenTable width tokenCount current next
                        witness.tailBoundary witness.tailCount binderArity
                        witness.relationArity)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
                      witness.relationArity witness.relationCode hinvalid)
                    (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current next
                      witness.tailBoundary witness.tailCount hfailure))))))) <=
      syntaxFormulaRelationInvalidBodyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hatArity hatCode hfailure := by
  have hindexClosed (index : Nat) :
      (fixedNumeralTerm index).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  let countCertificate := nativeShortLeCertificate 3 current.tokensCount hthree
  let arityCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
      witness.relationArity (fixedNumeralTerm 1)
      (natListAtFixedNumeralTerm_value 1) hatArity
  let codeCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
      witness.relationCode (fixedNumeralTerm 2)
      (natListAtFixedNumeralTerm_value 2) hatCode
  let invalidCertificate :=
    compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
      witness.relationArity witness.relationCode hinvalid
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  have hcount := nativeShortLeCertificate_structuralPayloadBound_le_public 3
    current.tokensCount hthree
  have harity :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
      witness.relationArity (fixedNumeralTerm 1) (hindexClosed 1)
      (natListAtFixedNumeralTerm_value 1) hatArity
  have hcode :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
      witness.relationCode (fixedNumeralTerm 2) (hindexClosed 2)
      (natListAtFixedNumeralTerm_value 2) hatCode
  have hinvalidResource :=
    compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      witness.relationArity witness.relationCode hinvalid
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let invalidPair :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      invalidCertificate failureCertificate
  have hinvalidPair := transparentHybridConjunctionPayloadBound_le
    invalidCertificate failureCertificate _ _ hinvalidResource hfailureResource
  let codeBranch :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := compactAdditiveArithmeticRelCodeValidClosedFormula
            witness.relationArity witness.relationCode ⋏
        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity witness.relationArity)
      invalidPair
  have hcodeBranch := transparentHybridDisjunctionRightPayloadBound_le
    (left := compactAdditiveArithmeticRelCodeValidClosedFormula
          witness.relationArity witness.relationCode ⋏
      compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount binderArity witness.relationArity)
    invalidPair _ hinvalidPair
  let codeTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    codeCertificate codeBranch
  have hcodeTail := transparentHybridConjunctionPayloadBound_le codeCertificate
    codeBranch _ _ hcode hcodeBranch
  let arityTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    arityCertificate codeTail
  have harityTail := transparentHybridConjunctionPayloadBound_le
    arityCertificate codeTail _ _ harity hcodeTail
  let longCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      arityTail
  have hlong := transparentHybridConjunctionPayloadBound_le countCertificate
    arityTail _ _ hcount harityTail
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := shortNativeLeFormula current.tokensCount 2 ⋏
      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
    longCertificate _ hlong
  unfold syntaxFormulaRelationInvalidBodyPayloadEnvelope
  exact houter

noncomputable def syntaxFormulaRelationTagBranchPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (bodyResource : Nat) : Nat :=
  let tagFormula := nativeEqFormula witness.tag 0 ⋎
    nativeEqFormula witness.tag 1
  let bodyFormula :=
    compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
      width tokenCount current next binderArity witness
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation tagFormula bodyFormula
    (syntaxFormulaNativeEqEitherPayloadEnvelope witness.tag 0 1 htag)
    bodyResource
  syntaxFormulaTagRelationPathPayloadEnvelope tokenTable width tokenCount
    current next binderArity witness selectedResource

/- RETIRED_EXPANDED_SELECTED_BRANCH_INTERMEDIATES
noncomputable def syntaxFormulaRelationTagBranchCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (bodyCertificate : FormulaHybridCertificate
      (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
        width tokenCount current next binderArity witness)) :
    FormulaHybridCertificate
      (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
        width tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
      bodyCertificate)

theorem syntaxFormulaRelationTagBranchPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 0 1)
    (bodyCertificate : FormulaHybridCertificate
      (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
        width tokenCount current next binderArity witness))
    (bodyResource : Nat)
    (hbody : hybridFormulaStructuralPayloadBound bodyCertificate <=
      bodyResource) :
    @hybridFormulaStructuralPayloadBound formulaZeroValuation
        (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
          width tokenCount current next binderArity witness)
        (syntaxFormulaRelationTagBranchCertificate tokenTable width tokenCount
          current next binderArity witness htag bodyCertificate) <=
      syntaxFormulaRelationTagBranchPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness htag bodyResource := by
  let selected : FormulaHybridCertificate
      (syntaxFormulaRelationSelectedFormula tokenTable width tokenCount current
        next binderArity witness) := by
    unfold syntaxFormulaRelationSelectedFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 0 1 htag) bodyCertificate
  have htagResource :=
    nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
      witness.tag 0 1 htag
  have hselected := transparentHybridConjunctionPayloadBound_le
    (nativeEqEitherCertificateFromData witness.tag 0 1 htag) bodyCertificate
    _ _ htagResource hbody
  have hpath := syntaxFormulaTagRelationPathPayloadBound_le tokenTable width
    tokenCount current next binderArity witness selected _ hselected
  unfold syntaxFormulaRelationTagBranchCertificate
    syntaxFormulaRelationTagBranchPayloadEnvelope
  change hybridFormulaStructuralPayloadBound selected <= _
  exact hpath

/- TEMP_SELECTED_BRANCH_DIAGNOSTIC
noncomputable def syntaxFormulaLogicalTagBranchPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 2 3)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 1) : Nat :=
  let tagFormula := nativeEqFormula witness.tag 2 ⋎
    nativeEqFormula witness.tag 3
  let continueFormula :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount 1
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation tagFormula continueFormula
    (syntaxFormulaNativeEqEitherPayloadEnvelope witness.tag 2 3 htag)
    (compactUnifiedParserSyntaxTermContinueGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 1
      hcontinue)
  syntaxFormulaTagLogicalPathPayloadEnvelope tokenTable width tokenCount current
    next binderArity witness selectedResource

theorem syntaxFormulaLogicalTagBranchPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 2 3)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 1) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := syntaxFormulaRelationSelectedFormula tokenTable width
            tokenCount current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right :=
              syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
                  current next binderArity witness ⋎
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
              (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount 1 hcontinue)))) <=
      syntaxFormulaLogicalTagBranchPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness htag hcontinue := by
  let continueCertificate :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount 1 hcontinue
  let selected : FormulaHybridCertificate
      (syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount current
        next witness) := by
    unfold syntaxFormulaLogicalSelectedFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
      continueCertificate
  have htagResource :=
    nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
      witness.tag 2 3 htag
  have hcontinueResource :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount 1 hcontinue
  have hselected := transparentHybridConjunctionPayloadBound_le
    (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
    continueCertificate _ _ htagResource hcontinueResource
  have hpath := syntaxFormulaTagLogicalPathPayloadBound_le tokenTable width
    tokenCount current next binderArity witness selected _ hselected
  unfold syntaxFormulaLogicalTagBranchPayloadEnvelope
  change hybridFormulaStructuralPayloadBound selected <= _
  exact hpath

noncomputable def syntaxFormulaBinaryTagBranchPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 4 5)
    (hbinary : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
      binderArity) : Nat :=
  let tagFormula := nativeEqFormula witness.tag 4 ⋎
    nativeEqFormula witness.tag 5
  let binaryFormula := compactUnifiedParserSyntaxFormulaBinaryClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation tagFormula binaryFormula
    (syntaxFormulaNativeEqEitherPayloadEnvelope witness.tag 4 5 htag)
    (compactUnifiedParserSyntaxFormulaBinaryGraphPayloadEnvelope tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity hbinary)
  syntaxFormulaTagBinaryPathPayloadEnvelope tokenTable width tokenCount current
    next binderArity witness selectedResource

theorem syntaxFormulaBinaryTagBranchPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 4 5)
    (hbinary : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
      binderArity) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := syntaxFormulaRelationSelectedFormula tokenTable width
            tokenCount current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := syntaxFormulaLogicalSelectedFormula tokenTable width
              tokenCount current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right :=
                syntaxFormulaQuantifierSelectedFormula tokenTable width
                    tokenCount current next binderArity witness ⋎
                  syntaxFormulaInvalidTagSelectedFormula tokenTable width
                    tokenCount current next witness)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
                (compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current next
                  witness.tailBoundary witness.tailCount binderArity
                  hbinary))))) <=
      syntaxFormulaBinaryTagBranchPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness htag hbinary := by
  let binaryCertificate :=
    compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity hbinary
  let selected : FormulaHybridCertificate
      (syntaxFormulaBinarySelectedFormula tokenTable width tokenCount current
        next binderArity witness) := by
    unfold syntaxFormulaBinarySelectedFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
      binaryCertificate
  have htagResource :=
    nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
      witness.tag 4 5 htag
  have hbinaryResource :=
    compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity hbinary
  have hselected := transparentHybridConjunctionPayloadBound_le
    (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
    binaryCertificate _ _ htagResource hbinaryResource
  have hpath := syntaxFormulaTagBinaryPathPayloadBound_le tokenTable width
    tokenCount current next binderArity witness selected _ hselected
  unfold syntaxFormulaBinaryTagBranchPayloadEnvelope
  change hybridFormulaStructuralPayloadBound selected <= _
  exact hpath

noncomputable def syntaxFormulaQuantifierTagBranchPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 6 7)
    (hquantifier : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity) : Nat :=
  let tagFormula := nativeEqFormula witness.tag 6 ⋎
    nativeEqFormula witness.tag 7
  let quantifierFormula :=
    compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation tagFormula quantifierFormula
    (syntaxFormulaNativeEqEitherPayloadEnvelope witness.tag 6 7 htag)
    (compactUnifiedParserSyntaxFormulaQuantifierGraphPayloadEnvelope tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity hquantifier)
  syntaxFormulaTagQuantifierPathPayloadEnvelope tokenTable width tokenCount
    current next binderArity witness selectedResource

theorem syntaxFormulaQuantifierTagBranchPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 6 7)
    (hquantifier : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := syntaxFormulaRelationSelectedFormula tokenTable width
            tokenCount current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := syntaxFormulaLogicalSelectedFormula tokenTable width
              tokenCount current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := syntaxFormulaBinarySelectedFormula tokenTable width
                tokenCount current next binderArity witness)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right := syntaxFormulaInvalidTagSelectedFormula tokenTable
                  width tokenCount current next witness)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
                  (compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
                    tokenTable width tokenCount current next
                    witness.tailBoundary witness.tailCount binderArity
                    hquantifier)))))) <=
      syntaxFormulaQuantifierTagBranchPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness htag hquantifier := by
  let quantifierCertificate :=
    compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity hquantifier
  let selected : FormulaHybridCertificate
      (syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
        current next binderArity witness) := by
    unfold syntaxFormulaQuantifierSelectedFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
      quantifierCertificate
  have htagResource :=
    nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
      witness.tag 6 7 htag
  have hquantifierResource :=
    compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity hquantifier
  have hselected := transparentHybridConjunctionPayloadBound_le
    (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
    quantifierCertificate _ _ htagResource hquantifierResource
  have hpath := syntaxFormulaTagQuantifierPathPayloadBound_le tokenTable width
    tokenCount current next binderArity witness selected _ hselected
  unfold syntaxFormulaQuantifierTagBranchPayloadEnvelope
  change hybridFormulaStructuralPayloadBound selected <= _
  exact hpath
END_TEMP_SELECTED_BRANCH_DIAGNOSTIC -/
END_RETIRED_EXPANDED_SELECTED_BRANCH_INTERMEDIATES -/

def syntaxFormulaNativeEqEitherPublicFinitePayloadEnvelope
    (value left right : Nat) : Nat :=
  transparentHybridDisjunctionLeftPayloadEnvelope formulaZeroValuation
      (nativeEqFormula value left) (nativeEqFormula value right)
      (syntaxFormulaNativeEqPayloadPolynomial value left) +
    transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
      (nativeEqFormula value left) (nativeEqFormula value right)
      (syntaxFormulaNativeEqPayloadPolynomial value right)

theorem syntaxFormulaNativeEqEitherPayloadEnvelope_le_publicFinite
    (value left right : Nat)
    (data : NativeEqEitherCheckedData value left right) :
    syntaxFormulaNativeEqEitherPayloadEnvelope value left right data <=
      syntaxFormulaNativeEqEitherPublicFinitePayloadEnvelope value left
        right := by
  cases data <;>
    simp [syntaxFormulaNativeEqEitherPayloadEnvelope,
      syntaxFormulaNativeEqEitherPublicFinitePayloadEnvelope]

theorem
    nativeEqEitherCertificateFromData_structuralPayloadBound_le_publicFinite
    (value left right : Nat)
    (data : NativeEqEitherCheckedData value left right) :
    hybridFormulaStructuralPayloadBound
        (nativeEqEitherCertificateFromData value left right data) <=
      syntaxFormulaNativeEqEitherPublicFinitePayloadEnvelope value left
        right := by
  exact
    (nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
      value left right data).trans
    (syntaxFormulaNativeEqEitherPayloadEnvelope_le_publicFinite value left
      right data)

def syntaxFormulaRelationShortBodyPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Nat :=
  let shortFormula := shortNativeLeFormula current.tokensCount 2 ⋏
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  let longFormula := nativeShortLeFormula 3 current.tokensCount ⋏
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.relationArity (fixedNumeralTerm 1) ⋏
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.relationCode (fixedNumeralTerm 2) ⋏
    ((compactAdditiveArithmeticRelCodeValidClosedFormula witness.relationArity
          witness.relationCode ⋏
        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity witness.relationArity) ⋎
      (compactAdditiveArithmeticRelCodeInvalidClosedFormula
            witness.relationArity witness.relationCode ⋏
        compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
          tokenCount current next witness.tailBoundary witness.tailCount))
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (shortNativeLeFormula current.tokensCount 2)
    (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (syntaxFormulaShortNativeLePayloadEnvelope current.tokensCount 2)
    (compactUnifiedParserSyntaxTermFailurePublicFinitePayloadEnvelope tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount)
  transparentHybridDisjunctionLeftPayloadEnvelope formulaZeroValuation
    shortFormula longFormula selectedResource

theorem syntaxFormulaRelationShortBodyPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    syntaxFormulaRelationShortBodyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hfailure <=
      syntaxFormulaRelationShortBodyPublicFinitePayloadEnvelope tokenTable
        width tokenCount current next binderArity witness := by
  unfold syntaxFormulaRelationShortBodyPayloadEnvelope
    syntaxFormulaRelationShortBodyPublicFinitePayloadEnvelope
  exact transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount hfailure))

theorem syntaxFormulaRelationShortBodyPayloadBound_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hshort : current.tokensCount <= 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := nativeShortLeFormula 3 current.tokensCount ⋏
            compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable
              width tokenCount current.tokensBoundary current.tokensCount
              witness.relationArity (fixedNumeralTerm 1) ⋏
            compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable
              width tokenCount current.tokensBoundary current.tokensCount
              witness.relationCode (fixedNumeralTerm 2) ⋏
            ((compactAdditiveArithmeticRelCodeValidClosedFormula
                    witness.relationArity witness.relationCode ⋏
                compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
                  tokenTable width tokenCount current next witness.tailBoundary
                  witness.tailCount binderArity witness.relationArity) ⋎
              (compactAdditiveArithmeticRelCodeInvalidClosedFormula
                      witness.relationArity witness.relationCode ⋏
                compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable
                  width tokenCount current next witness.tailBoundary
                  witness.tailCount)))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (shortNativeLeCertificate current.tokensCount 2 hshort)
            (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary
              witness.tailCount hfailure))) <=
      syntaxFormulaRelationShortBodyPublicFinitePayloadEnvelope tokenTable
        width tokenCount current next binderArity witness := by
  exact
    (syntaxFormulaRelationShortBodyPayloadBound_le_public tokenTable width
      tokenCount current next binderArity witness hshort hfailure).trans
    (syntaxFormulaRelationShortBodyPayloadEnvelope_le_publicFinite tokenTable
      width tokenCount current next binderArity witness hfailure)

def syntaxFormulaRelationValidBodyPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Nat :=
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  let functionFormula :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.relationArity
  let atArityFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.relationArity (fixedNumeralTerm 1)
  let atCodeFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount witness.relationCode
      (fixedNumeralTerm 2)
  let validFormula := compactAdditiveArithmeticRelCodeValidClosedFormula
    witness.relationArity witness.relationCode ⋏ functionFormula
  let invalidFormula := compactAdditiveArithmeticRelCodeInvalidClosedFormula
    witness.relationArity witness.relationCode ⋏ failureFormula
  let shortFormula := shortNativeLeFormula current.tokensCount 2 ⋏
    failureFormula
  let validResource := transparentHybridConjunctionPayloadEnvelope
    relCodeZeroValuation
    (compactAdditiveArithmeticRelCodeValidClosedFormula witness.relationArity
      witness.relationCode) functionFormula
    (compactAdditiveArithmeticRelCodeValidPayloadEnvelope
      witness.relationArity witness.relationCode)
    (compactUnifiedParserSyntaxTermFunctionPublicFinitePayloadEnvelope tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.relationArity)
  let codeBranchResource := transparentHybridDisjunctionLeftPayloadEnvelope
    relCodeZeroValuation validFormula invalidFormula validResource
  let codeTailResource := transparentHybridConjunctionPayloadEnvelope
    natListAtZeroValuation atCodeFormula (validFormula ⋎ invalidFormula)
    (compactAdditiveNatListAtRowsAtValuationIndexPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      witness.relationCode (fixedNumeralTerm 2)) codeBranchResource
  let arityTailResource := transparentHybridConjunctionPayloadEnvelope
    natListAtZeroValuation atArityFormula
    (atCodeFormula ⋏ (validFormula ⋎ invalidFormula))
    (compactAdditiveNatListAtRowsAtValuationIndexPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      witness.relationArity (fixedNumeralTerm 1)) codeTailResource
  let longResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeShortLeFormula 3 current.tokensCount)
    (atArityFormula ⋏ atCodeFormula ⋏ (validFormula ⋎ invalidFormula))
    (syntaxFormulaNativeShortLePayloadEnvelope 3 current.tokensCount)
    arityTailResource
  transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
    shortFormula
    (nativeShortLeFormula 3 current.tokensCount ⋏ atArityFormula ⋏
      atCodeFormula ⋏ (validFormula ⋎ invalidFormula)) longResource

theorem syntaxFormulaRelationValidBodyPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.relationArity) :
    syntaxFormulaRelationValidBodyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hatArity hatCode hfunction <=
      syntaxFormulaRelationValidBodyPublicFinitePayloadEnvelope tokenTable
        width tokenCount current next binderArity witness := by
  unfold syntaxFormulaRelationValidBodyPayloadEnvelope
    syntaxFormulaRelationValidBodyPublicFinitePayloadEnvelope
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
        (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 1 witness.relationArity (fixedNumeralTerm 1)
          (natListAtFixedNumeralTerm_value 1) hatArity)
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.relationCode (fixedNumeralTerm 2)
            (natListAtFixedNumeralTerm_value 2) hatCode)
          (transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
            (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
              (compactUnifiedParserSyntaxTermFunctionGraphPayloadEnvelope_le_publicFinite
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount binderArity witness.relationArity
                hfunction))))))

def syntaxFormulaRelationInvalidBodyPublicFinitePayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Nat :=
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  let functionFormula :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.relationArity
  let atArityFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.relationArity (fixedNumeralTerm 1)
  let atCodeFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount witness.relationCode
      (fixedNumeralTerm 2)
  let validFormula := compactAdditiveArithmeticRelCodeValidClosedFormula
    witness.relationArity witness.relationCode ⋏ functionFormula
  let invalidFormula := compactAdditiveArithmeticRelCodeInvalidClosedFormula
    witness.relationArity witness.relationCode ⋏ failureFormula
  let shortFormula := shortNativeLeFormula current.tokensCount 2 ⋏
    failureFormula
  let invalidResource := transparentHybridConjunctionPayloadEnvelope
    relCodeZeroValuation
    (compactAdditiveArithmeticRelCodeInvalidClosedFormula witness.relationArity
      witness.relationCode) failureFormula
    (compactAdditiveArithmeticRelCodeInvalidPayloadEnvelope
      witness.relationArity witness.relationCode)
    (compactUnifiedParserSyntaxTermFailurePublicFinitePayloadEnvelope tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount)
  let codeBranchResource := transparentHybridDisjunctionRightPayloadEnvelope
    relCodeZeroValuation validFormula invalidFormula invalidResource
  let codeTailResource := transparentHybridConjunctionPayloadEnvelope
    natListAtZeroValuation atCodeFormula (validFormula ⋎ invalidFormula)
    (compactAdditiveNatListAtRowsAtValuationIndexPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      witness.relationCode (fixedNumeralTerm 2)) codeBranchResource
  let arityTailResource := transparentHybridConjunctionPayloadEnvelope
    natListAtZeroValuation atArityFormula
    (atCodeFormula ⋏ (validFormula ⋎ invalidFormula))
    (compactAdditiveNatListAtRowsAtValuationIndexPublicFinitePayloadEnvelope
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      witness.relationArity (fixedNumeralTerm 1)) codeTailResource
  let longResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeShortLeFormula 3 current.tokensCount)
    (atArityFormula ⋏ atCodeFormula ⋏ (validFormula ⋎ invalidFormula))
    (syntaxFormulaNativeShortLePayloadEnvelope 3 current.tokensCount)
    arityTailResource
  transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
    shortFormula
    (nativeShortLeFormula 3 current.tokensCount ⋏ atArityFormula ⋏
      atCodeFormula ⋏ (validFormula ⋎ invalidFormula)) longResource

theorem syntaxFormulaRelationInvalidBodyPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hatArity : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.relationArity)
    (hatCode : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.relationCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    syntaxFormulaRelationInvalidBodyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hatArity hatCode hfailure <=
      syntaxFormulaRelationInvalidBodyPublicFinitePayloadEnvelope tokenTable
        width tokenCount current next binderArity witness := by
  unfold syntaxFormulaRelationInvalidBodyPayloadEnvelope
    syntaxFormulaRelationInvalidBodyPublicFinitePayloadEnvelope
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
        (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope_le_publicFinite
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 1 witness.relationArity (fixedNumeralTerm 1)
          (natListAtFixedNumeralTerm_value 1) hatArity)
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope_le_publicFinite
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.relationCode (fixedNumeralTerm 2)
            (natListAtFixedNumeralTerm_value 2) hatCode)
          (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
            (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
              (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope_le_publicFinite
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount hfailure))))))

theorem syntaxFormulaTagRelationPathPayloadEnvelope_mono
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    {small large : Nat} (hresource : small <= large) :
    syntaxFormulaTagRelationPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness small <=
      syntaxFormulaTagRelationPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness large := by
  unfold syntaxFormulaTagRelationPathPayloadEnvelope
  exact transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _ hresource

theorem syntaxFormulaTagLogicalPathPayloadEnvelope_mono
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    {small large : Nat} (hresource : small <= large) :
    syntaxFormulaTagLogicalPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness small <=
      syntaxFormulaTagLogicalPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness large := by
  unfold syntaxFormulaTagLogicalPathPayloadEnvelope
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _ hresource)

theorem syntaxFormulaTagBinaryPathPayloadEnvelope_mono
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    {small large : Nat} (hresource : small <= large) :
    syntaxFormulaTagBinaryPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness small <=
      syntaxFormulaTagBinaryPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness large := by
  unfold syntaxFormulaTagBinaryPathPayloadEnvelope
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
      (transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _ hresource))

theorem syntaxFormulaTagQuantifierPathPayloadEnvelope_mono
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    {small large : Nat} (hresource : small <= large) :
    syntaxFormulaTagQuantifierPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness small <=
      syntaxFormulaTagQuantifierPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness large := by
  unfold syntaxFormulaTagQuantifierPathPayloadEnvelope
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
      (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
        (transparentHybridDisjunctionLeftPayloadEnvelope_mono _ _ _
          hresource)))

theorem syntaxFormulaTagInvalidPathPayloadEnvelope_mono
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    {small large : Nat} (hresource : small <= large) :
    syntaxFormulaTagInvalidPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness small <=
      syntaxFormulaTagInvalidPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness large := by
  unfold syntaxFormulaTagInvalidPathPayloadEnvelope
  exact transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
    (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
      (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
        (transparentHybridDisjunctionRightPayloadEnvelope_mono _ _ _
          hresource)))

#print axioms nativeEqCertificate_structuralPayloadBound_le_public
#print axioms nativeNeCertificate_structuralPayloadBound_le_public
#print axioms shortNativeLeCertificate_structuralPayloadBound_le_public
#print axioms nativeShortLeCertificate_structuralPayloadBound_le_public
#print axioms
  nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
#print axioms syntaxFormulaTagBranchExplicitFormula_component_alignment
#print axioms syntaxFormulaTagRelationPathPayloadBound_le
#print axioms syntaxFormulaTagLogicalPathPayloadBound_le
#print axioms syntaxFormulaTagBinaryPathPayloadBound_le
#print axioms syntaxFormulaTagQuantifierPathPayloadBound_le
#print axioms syntaxFormulaTagInvalidPathPayloadBound_le
#print axioms syntaxFormulaRelationShortBodyPayloadBound_le_public
#print axioms syntaxFormulaRelationValidBodyPayloadBound_le_public
#print axioms syntaxFormulaRelationInvalidBodyPayloadBound_le_public

end FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds
