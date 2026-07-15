import integration.FoundationCompactNumericListedDirectFormulaSetEqCons

/-!
# Direct membership graphs for constructed logical formulas

The principal formula used by a rule is computed from stored child formulas;
it is not stored as a separate witness.  These relations scan the stored
context and require one row to be exactly the unary or binary constructor.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaConstructorMembership

open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectFormulaConstructorSlices

def CompactAdditiveUnaryFormulaConstructorMemberRows
    (tokenTable width tokenCount tag
      gammaBoundary gammaCount
      bodyStart bodyFinish bodyCount : Nat) : Prop :=
  exists index, index < gammaCount ∧
    exists targetStart, targetStart <= tokenCount ∧
    exists targetFinish, targetFinish <= tokenCount ∧
      CompactFixedWidthEntry gammaBoundary tokenCount index targetStart ∧
      CompactFixedWidthEntry gammaBoundary tokenCount
        (index + 1) targetFinish ∧
      CompactFixedWidthEntry tokenTable width targetStart (bodyCount + 1) ∧
      CompactAdditiveUnaryFormulaConstructorSlices
        tokenTable width tokenCount tag
          bodyStart bodyFinish bodyCount
          targetStart targetFinish (bodyCount + 1)

def CompactAdditiveBinaryFormulaConstructorMemberRows
    (tokenTable width tokenCount tag
      gammaBoundary gammaCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount : Nat) : Prop :=
  exists index, index < gammaCount ∧
    exists targetStart, targetStart <= tokenCount ∧
    exists targetFinish, targetFinish <= tokenCount ∧
      CompactFixedWidthEntry gammaBoundary tokenCount index targetStart ∧
      CompactFixedWidthEntry gammaBoundary tokenCount
        (index + 1) targetFinish ∧
      CompactFixedWidthEntry tokenTable width targetStart
        (leftCount + rightCount + 1) ∧
      CompactAdditiveBinaryFormulaConstructorSlices
        tokenTable width tokenCount tag
          leftStart leftFinish leftCount
          rightStart rightFinish rightCount
          targetStart targetFinish (leftCount + rightCount + 1)

def compactAdditiveUnaryFormulaConstructorMemberRowsDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount tag
      gammaBoundary gammaCount bodyStart bodyFinish bodyCount.
    ∃ index < gammaCount,
      ∃ targetStart <⁺ tokenCount,
        ∃ targetFinish <⁺ tokenCount,
          !(compactFixedWidthEntryDef)
            gammaBoundary tokenCount index targetStart ∧
          !(compactFixedWidthEntryDef)
            gammaBoundary tokenCount (index + 1) targetFinish ∧
          !(compactFixedWidthEntryDef)
            tokenTable width targetStart (bodyCount + 1) ∧
          !(compactAdditiveUnaryFormulaConstructorSlicesDef)
            tokenTable width tokenCount tag
              bodyStart bodyFinish bodyCount
              targetStart targetFinish (bodyCount + 1)”

def compactAdditiveBinaryFormulaConstructorMemberRowsDef :
    𝚺₀.Semisentence 12 := .mkSigma
  “tokenTable width tokenCount tag
      gammaBoundary gammaCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount.
    ∃ index < gammaCount,
      ∃ targetStart <⁺ tokenCount,
        ∃ targetFinish <⁺ tokenCount,
          !(compactFixedWidthEntryDef)
            gammaBoundary tokenCount index targetStart ∧
          !(compactFixedWidthEntryDef)
            gammaBoundary tokenCount (index + 1) targetFinish ∧
          !(compactFixedWidthEntryDef)
            tokenTable width targetStart
              (leftCount + rightCount + 1) ∧
          !(compactAdditiveBinaryFormulaConstructorSlicesDef)
            tokenTable width tokenCount tag
              leftStart leftFinish leftCount
              rightStart rightFinish rightCount
              targetStart targetFinish (leftCount + rightCount + 1)”

@[simp] theorem compactAdditiveUnaryFormulaConstructorMemberRowsDef_spec
    (tokenTable width tokenCount tag
      gammaBoundary gammaCount bodyStart bodyFinish bodyCount : Nat) :
    compactAdditiveUnaryFormulaConstructorMemberRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, tag,
          gammaBoundary, gammaCount, bodyStart, bodyFinish, bodyCount] ↔
      CompactAdditiveUnaryFormulaConstructorMemberRows
        tokenTable width tokenCount tag
          gammaBoundary gammaCount bodyStart bodyFinish bodyCount := by
  have hconstructor
      (targetFinish targetStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetFinish, targetStart, index,
                tokenTable, width, tokenCount, tag,
                gammaBoundary, gammaCount, bodyStart, bodyFinish, bodyCount]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 12), #4, #5, #6,
              #9, #10, #11, #1, #0, ‘(#11 + 1)’])
          Empty.elim) compactAdditiveUnaryFormulaConstructorSlicesDef.val ↔
        CompactAdditiveUnaryFormulaConstructorSlices
          tokenTable width tokenCount tag
            bodyStart bodyFinish bodyCount
            targetStart targetFinish (bodyCount + 1) := by
    have henv :
        (Semiterm.val
            ![targetFinish, targetStart, index,
              tokenTable, width, tokenCount, tag,
              gammaBoundary, gammaCount, bodyStart, bodyFinish, bodyCount]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 12), #4, #5, #6,
            #9, #10, #11, #1, #0, ‘(#11 + 1)’]) =
          ![tokenTable, width, tokenCount, tag,
            bodyStart, bodyFinish, bodyCount,
            targetStart, targetFinish, bodyCount + 1] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactAdditiveUnaryFormulaConstructorSlicesDef_spec
      tokenTable width tokenCount tag
        bodyStart bodyFinish bodyCount
        targetStart targetFinish (bodyCount + 1)
  simp [compactAdditiveUnaryFormulaConstructorMemberRowsDef,
    CompactAdditiveUnaryFormulaConstructorMemberRows, hconstructor]

@[simp] theorem compactAdditiveBinaryFormulaConstructorMemberRowsDef_spec
    (tokenTable width tokenCount tag
      gammaBoundary gammaCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount : Nat) :
    compactAdditiveBinaryFormulaConstructorMemberRowsDef.val.Evalb
        ![tokenTable, width, tokenCount, tag,
          gammaBoundary, gammaCount,
          leftStart, leftFinish, leftCount,
          rightStart, rightFinish, rightCount] ↔
      CompactAdditiveBinaryFormulaConstructorMemberRows
        tokenTable width tokenCount tag
          gammaBoundary gammaCount
          leftStart leftFinish leftCount
          rightStart rightFinish rightCount := by
  have hconstructor
      (targetFinish targetStart index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetFinish, targetStart, index,
                tokenTable, width, tokenCount, tag,
                gammaBoundary, gammaCount,
                leftStart, leftFinish, leftCount,
                rightStart, rightFinish, rightCount]
              Empty.elim ∘
            ![(#3 : Semiterm ℒₒᵣ Empty 15), #4, #5, #6,
              #9, #10, #11, #12, #13, #14,
              #1, #0, ‘((#11 + #14) + 1)’])
          Empty.elim) compactAdditiveBinaryFormulaConstructorSlicesDef.val ↔
        CompactAdditiveBinaryFormulaConstructorSlices
          tokenTable width tokenCount tag
            leftStart leftFinish leftCount
            rightStart rightFinish rightCount
            targetStart targetFinish (leftCount + rightCount + 1) := by
    have henv :
        (Semiterm.val
            ![targetFinish, targetStart, index,
              tokenTable, width, tokenCount, tag,
              gammaBoundary, gammaCount,
              leftStart, leftFinish, leftCount,
              rightStart, rightFinish, rightCount]
            Empty.elim ∘
          ![(#3 : Semiterm ℒₒᵣ Empty 15), #4, #5, #6,
            #9, #10, #11, #12, #13, #14,
            #1, #0, ‘((#11 + #14) + 1)’]) =
          ![tokenTable, width, tokenCount, tag,
            leftStart, leftFinish, leftCount,
            rightStart, rightFinish, rightCount,
            targetStart, targetFinish, leftCount + rightCount + 1] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactAdditiveBinaryFormulaConstructorSlicesDef_spec
      tokenTable width tokenCount tag
        leftStart leftFinish leftCount
        rightStart rightFinish rightCount
        targetStart targetFinish (leftCount + rightCount + 1)
  simp [compactAdditiveBinaryFormulaConstructorMemberRowsDef,
    CompactAdditiveBinaryFormulaConstructorMemberRows, hconstructor]

theorem compactAdditiveUnaryFormulaConstructorMemberRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveUnaryFormulaConstructorMemberRowsDef.val := by
  simp [compactAdditiveUnaryFormulaConstructorMemberRowsDef]

theorem compactAdditiveBinaryFormulaConstructorMemberRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveBinaryFormulaConstructorMemberRowsDef.val := by
  simp [compactAdditiveBinaryFormulaConstructorMemberRowsDef]

theorem compactAdditiveUnaryFormulaConstructorMemberRows_iff
    {tokenTable width tokenCount tag gammaBoundary
      bodyStart bodyFinish : Nat}
    {gamma : List (List Nat)} {body : List Nat}
    (hgamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary gamma)
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodyStart bodyFinish body) :
    CompactAdditiveUnaryFormulaConstructorMemberRows
        tokenTable width tokenCount tag
          gammaBoundary gamma.length bodyStart bodyFinish body.length ↔
      tokenFormulaMem (tag :: body) gamma = true := by
  rw [tokenFormulaMem_eq_true_iff]
  constructor
  · rintro ⟨index, hindex,
      targetStart, _htargetStart, targetFinish, _htargetFinish,
      htargetStartEntry, htargetFinishEntry, hcountEntry, hconstructor⟩
    rcases hgamma index hindex with
      ⟨rowStart, _hrowStart, rowFinish, _hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have hstart : targetStart = rowStart :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetStartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowStartEntry).symm
    have hfinish : targetFinish = rowFinish :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetFinishEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowFinishEntry).symm
    subst targetStart
    subst targetFinish
    have hcount : body.length + 1 = (gamma.getI index).length :=
      (CompactFixedWidthEntry.value_eq_tableValue hcountEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          (CompactAdditiveNatListDirectLayout.headerEntry hrowLayout)).symm
    have hrowEq : gamma.getI index = tag :: body :=
      (compactAdditiveUnaryFormulaConstructorSlices_iff_cons
        hbody hrowLayout).mp (by simpa [hcount] using hconstructor)
    rw [List.getI_eq_getElem gamma hindex] at hrowEq
    exact hrowEq ▸ List.getElem_mem hindex
  · intro hmember
    obtain ⟨index, hindex, hvalue⟩ :=
      List.mem_iff_getElem.mp hmember
    rcases hgamma index hindex with
      ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have hrowEq : gamma.getI index = tag :: body := by
      rw [List.getI_eq_getElem gamma hindex, hvalue]
    have hrowLayout' : CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount rowStart rowFinish (tag :: body) := by
      simpa [hrowEq] using hrowLayout
    have hcountEntry :=
      CompactAdditiveNatListDirectLayout.headerEntry hrowLayout'
    have hconstructor :=
      (compactAdditiveUnaryFormulaConstructorSlices_iff_cons
        hbody hrowLayout').mpr rfl
    exact ⟨index, hindex,
      rowStart, hrowStart, rowFinish, hrowFinish,
      hrowStartEntry, hrowFinishEntry,
      (by simpa using hcountEntry), (by simpa using hconstructor)⟩

theorem compactAdditiveBinaryFormulaConstructorMemberRows_iff
    {tokenTable width tokenCount tag gammaBoundary
      leftStart leftFinish rightStart rightFinish : Nat}
    {gamma : List (List Nat)} {left right : List Nat}
    (hgamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary gamma)
    (hleft : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      leftStart leftFinish left)
    (hright : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      rightStart rightFinish right) :
    CompactAdditiveBinaryFormulaConstructorMemberRows
        tokenTable width tokenCount tag
          gammaBoundary gamma.length
          leftStart leftFinish left.length
          rightStart rightFinish right.length ↔
      tokenFormulaMem (tag :: (left ++ right)) gamma = true := by
  rw [tokenFormulaMem_eq_true_iff]
  constructor
  · rintro ⟨index, hindex,
      targetStart, _htargetStart, targetFinish, _htargetFinish,
      htargetStartEntry, htargetFinishEntry, hcountEntry, hconstructor⟩
    rcases hgamma index hindex with
      ⟨rowStart, _hrowStart, rowFinish, _hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have hstart : targetStart = rowStart :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetStartEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowStartEntry).symm
    have hfinish : targetFinish = rowFinish :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetFinishEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hrowFinishEntry).symm
    subst targetStart
    subst targetFinish
    have hcount : left.length + right.length + 1 =
        (gamma.getI index).length :=
      (CompactFixedWidthEntry.value_eq_tableValue hcountEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          (CompactAdditiveNatListDirectLayout.headerEntry hrowLayout)).symm
    have hrowEq : gamma.getI index = tag :: (left ++ right) :=
      (compactAdditiveBinaryFormulaConstructorSlices_iff_cons_append
        hleft hright hrowLayout).mp (by simpa [hcount] using hconstructor)
    rw [List.getI_eq_getElem gamma hindex] at hrowEq
    exact hrowEq ▸ List.getElem_mem hindex
  · intro hmember
    obtain ⟨index, hindex, hvalue⟩ :=
      List.mem_iff_getElem.mp hmember
    rcases hgamma index hindex with
      ⟨rowStart, hrowStart, rowFinish, hrowFinish,
        hrowStartEntry, hrowFinishEntry, hrowLayout⟩
    have hrowEq : gamma.getI index = tag :: (left ++ right) := by
      rw [List.getI_eq_getElem gamma hindex, hvalue]
    have hrowLayout' : CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount rowStart rowFinish
          (tag :: (left ++ right)) := by
      simpa [hrowEq] using hrowLayout
    have hcountEntry :=
      CompactAdditiveNatListDirectLayout.headerEntry hrowLayout'
    have hconstructor :=
      (compactAdditiveBinaryFormulaConstructorSlices_iff_cons_append
        hleft hright hrowLayout').mpr rfl
    exact ⟨index, hindex,
      rowStart, hrowStart, rowFinish, hrowFinish,
      hrowStartEntry, hrowFinishEntry,
      (by simpa using hcountEntry), (by simpa using hconstructor)⟩

theorem compactAdditiveFormulaAndMemberRows_iff
    {tokenTable width tokenCount gammaBoundary
      leftStart leftFinish rightStart rightFinish : Nat}
    {gamma : List (List Nat)} {left right : List Nat}
    (hgamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary gamma)
    (hleft : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      leftStart leftFinish left)
    (hright : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      rightStart rightFinish right) :
    CompactAdditiveBinaryFormulaConstructorMemberRows
        tokenTable width tokenCount 4
          gammaBoundary gamma.length
          leftStart leftFinish left.length
          rightStart rightFinish right.length ↔
      tokenFormulaMem (tokenFormulaAnd left right) gamma = true := by
  simpa [tokenFormulaAnd] using
    compactAdditiveBinaryFormulaConstructorMemberRows_iff
      hgamma hleft hright (tag := 4)

theorem compactAdditiveFormulaOrMemberRows_iff
    {tokenTable width tokenCount gammaBoundary
      leftStart leftFinish rightStart rightFinish : Nat}
    {gamma : List (List Nat)} {left right : List Nat}
    (hgamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary gamma)
    (hleft : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      leftStart leftFinish left)
    (hright : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      rightStart rightFinish right) :
    CompactAdditiveBinaryFormulaConstructorMemberRows
        tokenTable width tokenCount 5
          gammaBoundary gamma.length
          leftStart leftFinish left.length
          rightStart rightFinish right.length ↔
      tokenFormulaMem (tokenFormulaOr left right) gamma = true := by
  simpa [tokenFormulaOr] using
    compactAdditiveBinaryFormulaConstructorMemberRows_iff
      hgamma hleft hright (tag := 5)

theorem compactAdditiveFormulaAllMemberRows_iff
    {tokenTable width tokenCount gammaBoundary bodyStart bodyFinish : Nat}
    {gamma : List (List Nat)} {body : List Nat}
    (hgamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary gamma)
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodyStart bodyFinish body) :
    CompactAdditiveUnaryFormulaConstructorMemberRows
        tokenTable width tokenCount 6
          gammaBoundary gamma.length bodyStart bodyFinish body.length ↔
      tokenFormulaMem (tokenFormulaAll body) gamma = true := by
  simpa [tokenFormulaAll] using
    compactAdditiveUnaryFormulaConstructorMemberRows_iff
      hgamma hbody (tag := 6)

theorem compactAdditiveFormulaExsMemberRows_iff
    {tokenTable width tokenCount gammaBoundary bodyStart bodyFinish : Nat}
    {gamma : List (List Nat)} {body : List Nat}
    (hgamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary gamma)
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodyStart bodyFinish body) :
    CompactAdditiveUnaryFormulaConstructorMemberRows
        tokenTable width tokenCount 7
          gammaBoundary gamma.length bodyStart bodyFinish body.length ↔
      tokenFormulaMem (tokenFormulaExs body) gamma = true := by
  simpa [tokenFormulaExs] using
    compactAdditiveUnaryFormulaConstructorMemberRows_iff
      hgamma hbody (tag := 7)

#print axioms compactAdditiveUnaryFormulaConstructorMemberRowsDef_spec
#print axioms compactAdditiveBinaryFormulaConstructorMemberRowsDef_spec
#print axioms compactAdditiveUnaryFormulaConstructorMemberRowsDef_sigmaZero
#print axioms compactAdditiveBinaryFormulaConstructorMemberRowsDef_sigmaZero
#print axioms compactAdditiveUnaryFormulaConstructorMemberRows_iff
#print axioms compactAdditiveBinaryFormulaConstructorMemberRows_iff
#print axioms compactAdditiveFormulaAndMemberRows_iff
#print axioms compactAdditiveFormulaOrMemberRows_iff
#print axioms compactAdditiveFormulaAllMemberRows_iff
#print axioms compactAdditiveFormulaExsMemberRows_iff

end FoundationCompactNumericListedDirectFormulaConstructorMembership
