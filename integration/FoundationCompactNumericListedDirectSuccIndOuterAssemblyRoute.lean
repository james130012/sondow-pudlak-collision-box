import integration.FoundationCompactNumericListedDirectSuccIndStepAssemblyRoute

/-!
# Direct checked outer assembly for the successor-induction sentence

Two disjunction constructors join the negated base, negated quantified step,
and quantified final slots.  The resulting slot is exactly the public
successor-induction sentence on canonical inputs.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSuccIndOuterAssemblyRoute

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectFormulaConstructorSlices
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute

def CompactSuccIndOuterAssemblyRoute
    (tokenTable width tokenCount : Nat)
    (negatedBase negatedQuantifiedStep quantifiedFinal innerDisjunction
      sentence : CompactNatListRowSlot) : Prop :=
  CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      negatedBase.start negatedBase.count negatedBase.finish
      negatedBase.boundary negatedBase.boundarySize /\
    CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      negatedQuantifiedStep.start negatedQuantifiedStep.count
      negatedQuantifiedStep.finish negatedQuantifiedStep.boundary
      negatedQuantifiedStep.boundarySize /\
    CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      quantifiedFinal.start quantifiedFinal.count quantifiedFinal.finish
      quantifiedFinal.boundary quantifiedFinal.boundarySize /\
    CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      innerDisjunction.start innerDisjunction.count innerDisjunction.finish
      innerDisjunction.boundary innerDisjunction.boundarySize /\
    CompactAdditiveBinaryFormulaConstructorSlices tokenTable width tokenCount 5
      negatedQuantifiedStep.start negatedQuantifiedStep.finish
        negatedQuantifiedStep.count
      quantifiedFinal.start quantifiedFinal.finish quantifiedFinal.count
      innerDisjunction.start innerDisjunction.finish innerDisjunction.count /\
    CompactAdditiveNatListWitnessRows tokenTable width tokenCount
      sentence.start sentence.count sentence.finish
      sentence.boundary sentence.boundarySize /\
    CompactAdditiveBinaryFormulaConstructorSlices tokenTable width tokenCount 5
      negatedBase.start negatedBase.finish negatedBase.count
      innerDisjunction.start innerDisjunction.finish innerDisjunction.count
      sentence.start sentence.finish sentence.count

def compactSuccIndOuterAssemblyRouteDef : 𝚺₀.Semisentence 28 := .mkSigma
  “tokenTable width tokenCount
      negatedBaseStart negatedBaseFinish negatedBaseBoundary negatedBaseCount
        negatedBaseBoundarySize
      negatedQuantifiedStepStart negatedQuantifiedStepFinish
        negatedQuantifiedStepBoundary negatedQuantifiedStepCount
        negatedQuantifiedStepBoundarySize
      quantifiedFinalStart quantifiedFinalFinish quantifiedFinalBoundary
        quantifiedFinalCount quantifiedFinalBoundarySize
      innerStart innerFinish innerBoundary innerCount innerBoundarySize
      sentenceStart sentenceFinish sentenceBoundary sentenceCount
        sentenceBoundarySize.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount
      negatedBaseStart negatedBaseCount negatedBaseFinish
      negatedBaseBoundary negatedBaseBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount
      negatedQuantifiedStepStart negatedQuantifiedStepCount
      negatedQuantifiedStepFinish negatedQuantifiedStepBoundary
      negatedQuantifiedStepBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount
      quantifiedFinalStart quantifiedFinalCount quantifiedFinalFinish
      quantifiedFinalBoundary quantifiedFinalBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount
      innerStart innerCount innerFinish innerBoundary innerBoundarySize ∧
    !(compactAdditiveBinaryFormulaConstructorSlicesDef)
      tokenTable width tokenCount 5
      negatedQuantifiedStepStart negatedQuantifiedStepFinish
        negatedQuantifiedStepCount
      quantifiedFinalStart quantifiedFinalFinish quantifiedFinalCount
      innerStart innerFinish innerCount ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount
      sentenceStart sentenceCount sentenceFinish sentenceBoundary
        sentenceBoundarySize ∧
    !(compactAdditiveBinaryFormulaConstructorSlicesDef)
      tokenTable width tokenCount 5
      negatedBaseStart negatedBaseFinish negatedBaseCount
      innerStart innerFinish innerCount
      sentenceStart sentenceFinish sentenceCount”

def compactSuccIndOuterAssemblyRouteEnvironment
    (tokenTable width tokenCount : Nat)
    (negatedBase negatedQuantifiedStep quantifiedFinal innerDisjunction
      sentence : CompactNatListRowSlot) : Fin 28 -> Nat :=
  ![tokenTable, width, tokenCount,
    negatedBase.start, negatedBase.finish, negatedBase.boundary,
      negatedBase.count, negatedBase.boundarySize,
    negatedQuantifiedStep.start, negatedQuantifiedStep.finish,
      negatedQuantifiedStep.boundary, negatedQuantifiedStep.count,
      negatedQuantifiedStep.boundarySize,
    quantifiedFinal.start, quantifiedFinal.finish, quantifiedFinal.boundary,
      quantifiedFinal.count, quantifiedFinal.boundarySize,
    innerDisjunction.start, innerDisjunction.finish,
      innerDisjunction.boundary, innerDisjunction.count,
      innerDisjunction.boundarySize,
    sentence.start, sentence.finish, sentence.boundary, sentence.count,
      sentence.boundarySize]

set_option maxHeartbeats 900000 in
-- Seven embedded row and constructor relations require local normalization.
set_option maxRecDepth 4096 in
@[simp] theorem compactSuccIndOuterAssemblyRouteDef_spec
    (tokenTable width tokenCount : Nat)
    (negatedBase negatedQuantifiedStep quantifiedFinal innerDisjunction
      sentence : CompactNatListRowSlot) :
    compactSuccIndOuterAssemblyRouteDef.val.Evalb
        (compactSuccIndOuterAssemblyRouteEnvironment tokenTable width tokenCount
          negatedBase negatedQuantifiedStep quantifiedFinal innerDisjunction
          sentence) ↔
      CompactSuccIndOuterAssemblyRoute tokenTable width tokenCount
        negatedBase negatedQuantifiedStep quantifiedFinal innerDisjunction
        sentence := by
  let env := compactSuccIndOuterAssemblyRouteEnvironment
    tokenTable width tokenCount negatedBase negatedQuantifiedStep
      quantifiedFinal innerDisjunction sentence
  change compactSuccIndOuterAssemblyRouteDef.val.Evalb env ↔ _
  have hnegatedBaseRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
          #3, #6, #4, #5, #7]) =
        ![tokenTable, width, tokenCount,
          negatedBase.start, negatedBase.count, negatedBase.finish,
          negatedBase.boundary, negatedBase.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnegatedQuantifiedStepRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
          #8, #11, #9, #10, #12]) =
        ![tokenTable, width, tokenCount,
          negatedQuantifiedStep.start, negatedQuantifiedStep.count,
          negatedQuantifiedStep.finish, negatedQuantifiedStep.boundary,
          negatedQuantifiedStep.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hquantifiedFinalRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
          #13, #16, #14, #15, #17]) =
        ![tokenTable, width, tokenCount,
          quantifiedFinal.start, quantifiedFinal.count,
          quantifiedFinal.finish, quantifiedFinal.boundary,
          quantifiedFinal.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hinnerRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
          #18, #21, #19, #20, #22]) =
        ![tokenTable, width, tokenCount,
          innerDisjunction.start, innerDisjunction.count,
          innerDisjunction.finish, innerDisjunction.boundary,
          innerDisjunction.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hinnerSlicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2, ‘5’,
          #8, #9, #11, #13, #14, #16, #18, #19, #21]) =
        ![tokenTable, width, tokenCount, 5,
          negatedQuantifiedStep.start, negatedQuantifiedStep.finish,
            negatedQuantifiedStep.count,
          quantifiedFinal.start, quantifiedFinal.finish, quantifiedFinal.count,
          innerDisjunction.start, innerDisjunction.finish,
            innerDisjunction.count] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndOuterAssemblyRouteEnvironment]
  have hsentenceRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
          #23, #26, #24, #25, #27]) =
        ![tokenTable, width, tokenCount,
          sentence.start, sentence.count, sentence.finish,
          sentence.boundary, sentence.boundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsentenceSlicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2, ‘5’,
          #3, #4, #6, #18, #19, #21, #23, #24, #26]) =
        ![tokenTable, width, tokenCount, 5,
          negatedBase.start, negatedBase.finish, negatedBase.count,
          innerDisjunction.start, innerDisjunction.finish,
            innerDisjunction.count,
          sentence.start, sentence.finish, sentence.count] := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactSuccIndOuterAssemblyRouteEnvironment]
  have hnegatedBaseRowsSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
              #3, #6, #4, #5, #7])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows tokenTable width tokenCount
          negatedBase.start negatedBase.count negatedBase.finish
          negatedBase.boundary negatedBase.boundarySize := by
    rw [hnegatedBaseRowsEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount negatedBase.start negatedBase.count
      negatedBase.finish negatedBase.boundary negatedBase.boundarySize
  have hnegatedQuantifiedStepRowsSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
              #8, #11, #9, #10, #12])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows tokenTable width tokenCount
          negatedQuantifiedStep.start negatedQuantifiedStep.count
          negatedQuantifiedStep.finish negatedQuantifiedStep.boundary
          negatedQuantifiedStep.boundarySize := by
    rw [hnegatedQuantifiedStepRowsEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount negatedQuantifiedStep.start
      negatedQuantifiedStep.count negatedQuantifiedStep.finish
      negatedQuantifiedStep.boundary negatedQuantifiedStep.boundarySize
  have hquantifiedFinalRowsSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
              #13, #16, #14, #15, #17])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows tokenTable width tokenCount
          quantifiedFinal.start quantifiedFinal.count quantifiedFinal.finish
          quantifiedFinal.boundary quantifiedFinal.boundarySize := by
    rw [hquantifiedFinalRowsEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount quantifiedFinal.start quantifiedFinal.count
      quantifiedFinal.finish quantifiedFinal.boundary
      quantifiedFinal.boundarySize
  have hinnerRowsSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
              #18, #21, #19, #20, #22])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows tokenTable width tokenCount
          innerDisjunction.start innerDisjunction.count innerDisjunction.finish
          innerDisjunction.boundary innerDisjunction.boundarySize := by
    rw [hinnerRowsEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount innerDisjunction.start
      innerDisjunction.count innerDisjunction.finish
      innerDisjunction.boundary innerDisjunction.boundarySize
  have hinnerSlicesSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2, ‘5’,
              #8, #9, #11, #13, #14, #16, #18, #19, #21])
          Empty.elim) compactAdditiveBinaryFormulaConstructorSlicesDef.val ↔
        CompactAdditiveBinaryFormulaConstructorSlices
          tokenTable width tokenCount 5
          negatedQuantifiedStep.start negatedQuantifiedStep.finish
            negatedQuantifiedStep.count
          quantifiedFinal.start quantifiedFinal.finish quantifiedFinal.count
          innerDisjunction.start innerDisjunction.finish
            innerDisjunction.count := by
    rw [hinnerSlicesEnv]
    exact compactAdditiveBinaryFormulaConstructorSlicesDef_spec
      tokenTable width tokenCount 5
      negatedQuantifiedStep.start negatedQuantifiedStep.finish
        negatedQuantifiedStep.count
      quantifiedFinal.start quantifiedFinal.finish quantifiedFinal.count
      innerDisjunction.start innerDisjunction.finish innerDisjunction.count
  have hsentenceRowsSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2,
              #23, #26, #24, #25, #27])
          Empty.elim) compactAdditiveNatListWitnessRowsDef.val ↔
        CompactAdditiveNatListWitnessRows tokenTable width tokenCount
          sentence.start sentence.count sentence.finish sentence.boundary
          sentence.boundarySize := by
    rw [hsentenceRowsEnv]
    exact compactAdditiveNatListWitnessRowsDef_spec
      tokenTable width tokenCount sentence.start sentence.count
      sentence.finish sentence.boundary sentence.boundarySize
  have hsentenceSlicesSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 28), #1, #2, ‘5’,
              #3, #4, #6, #18, #19, #21, #23, #24, #26])
          Empty.elim) compactAdditiveBinaryFormulaConstructorSlicesDef.val ↔
        CompactAdditiveBinaryFormulaConstructorSlices
          tokenTable width tokenCount 5
          negatedBase.start negatedBase.finish negatedBase.count
          innerDisjunction.start innerDisjunction.finish
            innerDisjunction.count
          sentence.start sentence.finish sentence.count := by
    rw [hsentenceSlicesEnv]
    exact compactAdditiveBinaryFormulaConstructorSlicesDef_spec
      tokenTable width tokenCount 5
      negatedBase.start negatedBase.finish negatedBase.count
      innerDisjunction.start innerDisjunction.finish innerDisjunction.count
      sentence.start sentence.finish sentence.count
  simp [compactSuccIndOuterAssemblyRouteDef,
    CompactSuccIndOuterAssemblyRoute,
    hnegatedBaseRowsSpec, hnegatedQuantifiedStepRowsSpec,
    hquantifiedFinalRowsSpec, hinnerRowsSpec, hinnerSlicesSpec,
    hsentenceRowsSpec, hsentenceSlicesSpec]

theorem compactSuccIndOuterAssemblyRouteDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSuccIndOuterAssemblyRouteDef.val := by
  simp [compactSuccIndOuterAssemblyRouteDef]

theorem CompactSuccIndOuterAssemblyRoute.sound_canonical
    {tokenTable width tokenCount : Nat}
    {negatedBaseSlot negatedQuantifiedStepSlot quantifiedFinalSlot
      innerDisjunctionSlot sentenceSlot : CompactNatListRowSlot}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hroute : CompactSuccIndOuterAssemblyRoute tokenTable width tokenCount
      negatedBaseSlot negatedQuantifiedStepSlot quantifiedFinalSlot
      innerDisjunctionSlot sentenceSlot)
    (hnegatedBase : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount negatedBaseSlot.start negatedBaseSlot.finish
        (compactArithmeticFormulaTokens (∼compactSuccIndBaseFormula body)))
    (hnegatedQuantifiedStep : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount negatedQuantifiedStepSlot.start
        negatedQuantifiedStepSlot.finish
        (compactArithmeticFormulaTokens
          (∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
            compactSuccIndStepSuccessorFormula body)))))
    (hquantifiedFinal : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount quantifiedFinalSlot.start
        quantifiedFinalSlot.finish
        (compactArithmeticFormulaTokens
          (∀⁰ compactSuccIndStepZeroFormula body))) :
    ∃ sentenceTokens : List Nat,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        sentenceSlot.start sentenceSlot.finish sentenceTokens /\
      sentenceTokens = compactArithmeticFormulaTokens (succInd body) := by
  rcases hroute with
    ⟨hnegatedBaseRows, hnegatedQuantifiedStepRows, hquantifiedFinalRows,
      hinnerRows, hinnerSlices, hsentenceRows, hsentenceSlices⟩
  rcases hnegatedBaseRows.realize with
    ⟨negatedBaseTokens, hnegatedBaseCount,
      hnegatedBaseRowsLayout, _hnegatedBaseElementRows⟩
  have hnegatedBaseEq :
      compactArithmeticFormulaTokens (∼compactSuccIndBaseFormula body) =
        negatedBaseTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hnegatedBaseRowsLayout hnegatedBase).1
  subst negatedBaseTokens
  have hnegatedBaseCountValue : negatedBaseSlot.count =
      (compactArithmeticFormulaTokens
        (∼compactSuccIndBaseFormula body)).length := hnegatedBaseCount.symm
  rcases hnegatedQuantifiedStepRows.realize with
    ⟨negatedQuantifiedStepTokens, hnegatedQuantifiedStepCount,
      hnegatedQuantifiedStepRowsLayout,
      _hnegatedQuantifiedStepElementRows⟩
  have hnegatedQuantifiedStepEq :
      compactArithmeticFormulaTokens
          (∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
            compactSuccIndStepSuccessorFormula body))) =
        negatedQuantifiedStepTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hnegatedQuantifiedStepRowsLayout hnegatedQuantifiedStep).1
  subst negatedQuantifiedStepTokens
  have hnegatedQuantifiedStepCountValue :
      negatedQuantifiedStepSlot.count =
        (compactArithmeticFormulaTokens
          (∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
            compactSuccIndStepSuccessorFormula body)))).length :=
    hnegatedQuantifiedStepCount.symm
  rcases hquantifiedFinalRows.realize with
    ⟨quantifiedFinalTokens, hquantifiedFinalCount,
      hquantifiedFinalRowsLayout, _hquantifiedFinalElementRows⟩
  have hquantifiedFinalEq :
      compactArithmeticFormulaTokens
          (∀⁰ compactSuccIndStepZeroFormula body) = quantifiedFinalTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hquantifiedFinalRowsLayout hquantifiedFinal).1
  subst quantifiedFinalTokens
  have hquantifiedFinalCountValue : quantifiedFinalSlot.count =
      (compactArithmeticFormulaTokens
        (∀⁰ compactSuccIndStepZeroFormula body)).length :=
    hquantifiedFinalCount.symm
  rcases hinnerRows.realize with
    ⟨innerTokens, hinnerCount, hinnerLayout, _hinnerElementRows⟩
  have hinnerCountValue : innerDisjunctionSlot.count = innerTokens.length :=
    hinnerCount.symm
  have hinnerSlices' : CompactAdditiveBinaryFormulaConstructorSlices
      tokenTable width tokenCount 5
      negatedQuantifiedStepSlot.start negatedQuantifiedStepSlot.finish
        (compactArithmeticFormulaTokens
          (∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
            compactSuccIndStepSuccessorFormula body)))).length
      quantifiedFinalSlot.start quantifiedFinalSlot.finish
        (compactArithmeticFormulaTokens
          (∀⁰ compactSuccIndStepZeroFormula body)).length
      innerDisjunctionSlot.start innerDisjunctionSlot.finish
        innerTokens.length := by
    simpa only [hnegatedQuantifiedStepCountValue,
      hquantifiedFinalCountValue, hinnerCountValue] using hinnerSlices
  have hinnerValue : innerTokens = tokenFormulaOr
      (compactArithmeticFormulaTokens
        (∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body))))
      (compactArithmeticFormulaTokens
        (∀⁰ compactSuccIndStepZeroFormula body)) :=
    (compactAdditiveFormulaOrSlices_iff
      hnegatedQuantifiedStep hquantifiedFinal hinnerLayout).mp hinnerSlices'
  have hinnerCanonical : innerTokens = compactArithmeticFormulaTokens
      ((∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
        compactSuccIndStepSuccessorFormula body))) ⋎
          (∀⁰ compactSuccIndStepZeroFormula body)) := by
    rw [hinnerValue]
    rfl
  rcases hsentenceRows.realize with
    ⟨sentenceTokens, hsentenceCount, hsentenceLayout,
      _hsentenceElementRows⟩
  have hsentenceCountValue : sentenceSlot.count = sentenceTokens.length :=
    hsentenceCount.symm
  have hsentenceSlices' : CompactAdditiveBinaryFormulaConstructorSlices
      tokenTable width tokenCount 5
      negatedBaseSlot.start negatedBaseSlot.finish
        (compactArithmeticFormulaTokens
          (∼compactSuccIndBaseFormula body)).length
      innerDisjunctionSlot.start innerDisjunctionSlot.finish
        innerTokens.length
      sentenceSlot.start sentenceSlot.finish sentenceTokens.length := by
    simpa only [hnegatedBaseCountValue, hinnerCountValue,
      hsentenceCountValue] using hsentenceSlices
  have hsentenceValue : sentenceTokens = tokenFormulaOr
      (compactArithmeticFormulaTokens
        (∼compactSuccIndBaseFormula body)) innerTokens :=
    (compactAdditiveFormulaOrSlices_iff
      hnegatedBase hinnerLayout hsentenceLayout).mp hsentenceSlices'
  have hconstructed : sentenceTokens = compactArithmeticFormulaTokens
      (compactSuccIndConstructedFormula body) := by
    rw [hsentenceValue, hinnerCanonical]
    rfl
  refine ⟨sentenceTokens, hsentenceLayout, ?_⟩
  rw [hconstructed, compactSuccIndConstructedFormula_eq_succInd]

#print axioms compactSuccIndOuterAssemblyRouteDef_spec
#print axioms compactSuccIndOuterAssemblyRouteDef_sigmaZero
#print axioms CompactSuccIndOuterAssemblyRoute.sound_canonical

end FoundationCompactNumericListedDirectSuccIndOuterAssemblyRoute
