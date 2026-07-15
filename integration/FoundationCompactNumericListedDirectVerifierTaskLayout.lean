import integration.FoundationCompactNumericListedDirectVerifierValueLayouts

/-!
# Direct layouts for numeric verifier tasks

A verifier task is a numeric tag followed by five additive natural-number
lists: context, first formula, second formula, witness, and proof suffix.
The layouts below expose these six consecutive components without decoding a
typed object inside the arithmetic formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec

def CompactNumericNodeFieldsDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (fields : CompactNumericNodeFields) : Prop :=
  ∃ gammaFinish firstFinish secondFinish witnessFinish,
    CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount start gammaFinish fields.1 ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish fields.2.1 ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount firstFinish secondFinish fields.2.2.1 ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount secondFinish witnessFinish
        fields.2.2.2.1 ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessFinish finish fields.2.2.2.2

theorem compactNumericNodeFieldsDirectLayout_canonical
    (frontTokens : List Nat) (fields : CompactNumericNodeFields)
    (backTokens : List Nat) :
    let fieldTokens := compactAdditiveEncode fields
    let tokens := frontTokens ++ fieldTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + fieldTokens.length
    CompactNumericNodeFieldsDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish fields := by
  let gamma := fields.1
  let firstFormula := fields.2.1
  let secondFormula := fields.2.2.1
  let witness := fields.2.2.2.1
  let suffix := fields.2.2.2.2
  let fieldTokens := compactAdditiveEncode fields
  let tokens := frontTokens ++ fieldTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let gammaFinish := start + (compactAdditiveEncode gamma).length
  let firstFinish := gammaFinish +
    (compactAdditiveEncode firstFormula).length
  let secondFinish := firstFinish +
    (compactAdditiveEncode secondFormula).length
  let witnessFinish := secondFinish +
    (compactAdditiveEncode witness).length
  let finish := start + fieldTokens.length
  let afterGamma := frontTokens ++ compactAdditiveEncode gamma
  let afterFirst := afterGamma ++ compactAdditiveEncode firstFormula
  let afterSecond := afterFirst ++ compactAdditiveEncode secondFormula
  let afterWitness := afterSecond ++ compactAdditiveEncode witness
  have hfieldTokens : fieldTokens =
      compactAdditiveEncode gamma ++
      compactAdditiveEncode firstFormula ++
      compactAdditiveEncode secondFormula ++
      compactAdditiveEncode witness ++
      compactAdditiveEncode suffix := by
    change compactAdditiveEncode fields = _
    rw [show fields =
      (gamma, (firstFormula, (secondFormula, (witness, suffix)))) by rfl]
    simp only [compactAdditiveEncode_prod]
    simp [List.append_assoc]
  have hcommonTokens : tokens =
      frontTokens ++ compactAdditiveEncode gamma ++
      compactAdditiveEncode firstFormula ++
      compactAdditiveEncode secondFormula ++
      compactAdditiveEncode witness ++
      compactAdditiveEncode suffix ++ backTokens := by
    rw [show tokens = frontTokens ++ fieldTokens ++ backTokens by rfl]
    rw [hfieldTokens]
    simp [List.append_assoc]
  have hgammaFull :
      frontTokens ++ compactAdditiveEncode gamma ++
        (compactAdditiveEncode firstFormula ++
          compactAdditiveEncode secondFormula ++
          compactAdditiveEncode witness ++
          compactAdditiveEncode suffix ++ backTokens) = tokens := by
    simpa [List.append_assoc] using hcommonTokens.symm
  have hfirstFull :
      afterGamma ++ compactAdditiveEncode firstFormula ++
        (compactAdditiveEncode secondFormula ++
          compactAdditiveEncode witness ++
          compactAdditiveEncode suffix ++ backTokens) = tokens := by
    simpa [afterGamma, List.append_assoc] using hcommonTokens.symm
  have hsecondFull :
      afterFirst ++ compactAdditiveEncode secondFormula ++
        (compactAdditiveEncode witness ++
          compactAdditiveEncode suffix ++ backTokens) = tokens := by
    simpa [afterFirst, afterGamma, List.append_assoc] using
      hcommonTokens.symm
  have hwitnessFull :
      afterSecond ++ compactAdditiveEncode witness ++
        (compactAdditiveEncode suffix ++ backTokens) = tokens := by
    simpa [afterSecond, afterFirst, afterGamma, List.append_assoc] using
      hcommonTokens.symm
  have hsuffixFull :
      afterWitness ++ compactAdditiveEncode suffix ++ backTokens = tokens := by
    simpa [afterWitness, afterSecond, afterFirst, afterGamma,
      List.append_assoc] using hcommonTokens.symm
  have hgammaRaw := compactAdditiveNatListListDirectLayout_canonical
    frontTokens gamma
      (compactAdditiveEncode firstFormula ++
        compactAdditiveEncode secondFormula ++
        compactAdditiveEncode witness ++
        compactAdditiveEncode suffix ++ backTokens)
  have hfirstRaw := compactAdditiveNatListDirectLayout_canonical
    afterGamma firstFormula
      (compactAdditiveEncode secondFormula ++
        compactAdditiveEncode witness ++
        compactAdditiveEncode suffix ++ backTokens)
  have hsecondRaw := compactAdditiveNatListDirectLayout_canonical
    afterFirst secondFormula
      (compactAdditiveEncode witness ++
        compactAdditiveEncode suffix ++ backTokens)
  have hwitnessRaw := compactAdditiveNatListDirectLayout_canonical
    afterSecond witness (compactAdditiveEncode suffix ++ backTokens)
  have hsuffixRaw := compactAdditiveNatListDirectLayout_canonical
    afterWitness suffix backTokens
  dsimp only at hgammaRaw hfirstRaw hsecondRaw hwitnessRaw hsuffixRaw
  rw [hgammaFull] at hgammaRaw
  rw [hfirstFull] at hfirstRaw
  rw [hsecondFull] at hsecondRaw
  rw [hwitnessFull] at hwitnessRaw
  rw [hsuffixFull] at hsuffixRaw
  have hafterGamma : afterGamma.length = gammaFinish := by
    simp [afterGamma, gammaFinish, start]
  have hafterFirst : afterFirst.length = firstFinish := by
    dsimp only [afterFirst, afterGamma, firstFinish, gammaFinish, start]
    simp only [List.length_append]
  have hafterSecond : afterSecond.length = secondFinish := by
    dsimp only [afterSecond, afterFirst, afterGamma, secondFinish,
      firstFinish, gammaFinish, start]
    simp only [List.length_append]
  have hafterWitness : afterWitness.length = witnessFinish := by
    dsimp only [afterWitness, afterSecond, afterFirst, afterGamma,
      witnessFinish, secondFinish, firstFinish, gammaFinish, start]
    simp only [List.length_append]
  have hfinish : finish = witnessFinish +
      (compactAdditiveEncode suffix).length := by
    dsimp only [finish, witnessFinish, secondFinish, firstFinish,
      gammaFinish, start]
    rw [hfieldTokens]
    simp only [List.length_append]
    omega
  have hgamma : CompactAdditiveNatListListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      start gammaFinish gamma := by
    simpa only [width, gammaFinish] using hgammaRaw
  have hfirst : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      gammaFinish firstFinish firstFormula := by
    simpa only [width, hafterGamma, firstFinish] using hfirstRaw
  have hsecond : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      firstFinish secondFinish secondFormula := by
    simpa only [width, hafterFirst, secondFinish] using hsecondRaw
  have hwitness : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      secondFinish witnessFinish witness := by
    simpa only [width, hafterSecond, witnessFinish] using hwitnessRaw
  have hsuffix : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      witnessFinish finish suffix := by
    simpa only [width, hafterWitness, hfinish] using hsuffixRaw
  exact ⟨gammaFinish, firstFinish, secondFinish, witnessFinish,
    hgamma, hfirst, hsecond, hwitness, hsuffix⟩

def CompactNumericVerifierTaskDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (task : CompactNumericVerifierTask) : Prop :=
  ∃ fieldsStart,
    CompactAdditiveTokenCell
      tokenTable width tokenCount start task.1 fieldsStart ∧
    CompactNumericNodeFieldsDirectLayout
      tokenTable width tokenCount fieldsStart finish task.2

theorem compactNumericVerifierTaskDirectLayout_canonical
    (frontTokens : List Nat) (task : CompactNumericVerifierTask)
    (backTokens : List Nat) :
    let taskTokens := compactAdditiveEncode task
    let tokens := frontTokens ++ taskTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + taskTokens.length
    CompactNumericVerifierTaskDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish task := by
  let tag := task.1
  let fields := task.2
  let taskTokens := compactAdditiveEncode task
  let tokens := frontTokens ++ taskTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let fieldsStart := start + 1
  let finish := start + taskTokens.length
  let afterTag := frontTokens ++ compactAdditiveEncode tag
  have htaskTokens : taskTokens =
      compactAdditiveEncode tag ++ compactAdditiveEncode fields := by
    change compactAdditiveEncode task = _
    rw [show task = (tag, fields) by rfl]
    exact compactAdditiveEncode_prod (tag, fields)
  have htagTokens : compactAdditiveEncode tag = [tag] := rfl
  have hcommonTokens : tokens =
      frontTokens ++ compactAdditiveEncode tag ++
        compactAdditiveEncode fields ++ backTokens := by
    rw [show tokens = frontTokens ++ taskTokens ++ backTokens by rfl]
    rw [htaskTokens]
    simp [List.append_assoc]
  have htagFull : frontTokens ++ compactAdditiveEncode tag ++
      (compactAdditiveEncode fields ++ backTokens) = tokens := by
    simpa [List.append_assoc] using hcommonTokens.symm
  have hfieldsFull : afterTag ++ compactAdditiveEncode fields ++
      backTokens = tokens := by
    simpa [afterTag, List.append_assoc] using hcommonTokens.symm
  have htagRaw := compactAdditiveNatValueDirectLayout_canonical
    frontTokens tag (compactAdditiveEncode fields ++ backTokens)
  have hfieldsRaw := compactNumericNodeFieldsDirectLayout_canonical
    afterTag fields backTokens
  dsimp only at htagRaw hfieldsRaw
  rw [htagFull] at htagRaw
  rw [hfieldsFull] at hfieldsRaw
  have hafterTag : afterTag.length = fieldsStart := by
    simp [afterTag, fieldsStart, start, htagTokens]
  have hfinish : finish = fieldsStart +
      (compactAdditiveEncode fields).length := by
    dsimp only [finish, fieldsStart, start]
    rw [htaskTokens, htagTokens]
    simp only [List.length_append, List.length_singleton]
    omega
  have htagLength : (compactAdditiveEncode tag).length = 1 := by
    rfl
  have htag : CompactAdditiveTokenCell
      (compactFixedWidthTableCode width tokens) width tokens.length
      start tag fieldsStart := by
    simpa only [CompactAdditiveNatValueDirectLayout, width,
      fieldsStart, htagLength] using htagRaw
  have hfields : CompactNumericNodeFieldsDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      fieldsStart finish fields := by
    simpa only [width, hafterTag, hfinish] using hfieldsRaw
  exact ⟨fieldsStart, htag, hfields⟩

#print axioms compactNumericNodeFieldsDirectLayout_canonical
#print axioms compactNumericVerifierTaskDirectLayout_canonical

end FoundationCompactNumericListedDirectVerifierTaskLayout
