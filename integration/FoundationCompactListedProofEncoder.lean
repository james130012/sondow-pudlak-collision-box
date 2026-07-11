import integration.FoundationComputableCompactPAProofEncoder
import integration.FoundationCompactListedCertifiedVerifier

/-!
# Canonical encoder for list-preserving compact proof trees
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedProofEncoder

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactListedProofDecoder
open FoundationComputableCompactPAProofEncoder

def toListed :
    CheckedPAProofTree -> ListedCheckedPAProofTree
  | .closed Gamma formula =>
      .closed (canonicalSequentList Gamma) formula
  | .axm Gamma sentence =>
      .axm (canonicalSequentList Gamma) sentence
  | .verum Gamma =>
      .verum (canonicalSequentList Gamma)
  | .and Gamma leftFormula rightFormula left right =>
      .and (canonicalSequentList Gamma) leftFormula rightFormula
        (toListed left) (toListed right)
  | .or Gamma leftFormula rightFormula premise =>
      .or (canonicalSequentList Gamma) leftFormula rightFormula
        (toListed premise)
  | .all Gamma formula premise =>
      .all (canonicalSequentList Gamma) formula (toListed premise)
  | .exs Gamma formula witness premise =>
      .exs (canonicalSequentList Gamma) formula witness (toListed premise)
  | .wk Gamma premise =>
      .wk (canonicalSequentList Gamma) (toListed premise)
  | .shift Gamma premise =>
      .shift (canonicalSequentList Gamma) (toListed premise)
  | .cut Gamma formula left right =>
      .cut (canonicalSequentList Gamma) formula
        (toListed left) (toListed right)

@[simp] theorem toListed_toChecked
    (tree : CheckedPAProofTree) :
    (toListed tree).toChecked = tree := by
  induction tree <;>
    simp [toListed,
      ListedCheckedPAProofTree.toChecked, *]

theorem decodeCompactSequentList_canonicalBinaryCode_append
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (fuel : Nat) (hfuel : sequentSymbolCount Gamma < fuel)
    (suffix : List Bool) :
    decodeCompactSequentList fuel
        (canonicalBinarySequentCode Gamma ++ suffix) =
      some (canonicalSequentList Gamma, suffix) := by
  let formulaVector :
      List.Vector LO.FirstOrder.ArithmeticProposition Gamma.card :=
    ⟨canonicalSequentList Gamma, by simp⟩
  have hformula
      (formula : LO.FirstOrder.ArithmeticProposition)
      (hformulaMem : formula ∈ formulaVector.toList) :
      formulaSymbolCount formula < fuel := by
    have hmem : formula ∈ Gamma := by
      simpa [formulaVector] using hformulaMem
    have hle :
        formulaSymbolCount formula <= Gamma.sum formulaSymbolCount :=
      Finset.single_le_sum
        (f := formulaSymbolCount) (s := Gamma)
        (fun item _ => Nat.zero_le (formulaSymbolCount item)) hmem
    exact hle.trans_lt hfuel
  have hmany :=
    decodeManyVector_toList_flatMap_append
      (decodeCompactFormula 0 fuel)
      binaryFormulaCode formulaVector suffix
      (fun formula hformulaMem rest =>
        decodeCompactFormula_binaryFormulaCode_append
          formula fuel (hformula formula hformulaMem) rest)
  have hmany' :
      decodeManyVector (decodeCompactFormula 0 fuel) Gamma.card
          ((canonicalSequentList Gamma).flatMap binaryFormulaCode ++ suffix) =
        some (formulaVector, suffix) := by
    simpa [formulaVector] using hmany
  simp [canonicalBinarySequentCode, decodeCompactSequentList,
    hmany', formulaVector]

theorem decodeCompactListedProof_canonicalBinaryCode_append
    (tree : CheckedPAProofTree) (fuel : Nat)
    (hfuel : tree.parseWeight < fuel) (suffix : List Bool) :
    decodeCompactListedProof fuel
        (canonicalBinaryProofCode tree ++ suffix) =
      some (toListed tree, suffix) := by
  induction tree generalizing fuel suffix with
  | closed Gamma formula =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula : formulaSymbolCount formula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactListedProof,
            decodeCompactSequentList_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula,
            toListed]
  | axm Gamma sentence =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula :
              formulaSymbolCount
                  (Rewriting.emb sentence :
                    LO.FirstOrder.ArithmeticProposition) < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactListedProof,
            decodeCompactSequentList_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              (Rewriting.emb sentence :
                LO.FirstOrder.ArithmeticProposition) fuel hformula,
            propositionToSentence, toListed]
  | verum Gamma =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactListedProof,
            decodeCompactSequentList_canonicalBinaryCode_append
              Gamma fuel hseq,
            toListed]
  | and Gamma leftFormula rightFormula left right ihLeft ihRight =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hleftFormula : formulaSymbolCount leftFormula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hrightFormula : formulaSymbolCount rightFormula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hleft : left.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hright : right.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactListedProof,
            decodeCompactSequentList_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              leftFormula fuel hleftFormula,
            decodeCompactFormula_binaryFormulaCode_append
              rightFormula fuel hrightFormula,
            ihLeft fuel hleft, ihRight fuel hright,
            toListed]
  | or Gamma leftFormula rightFormula premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hleftFormula : formulaSymbolCount leftFormula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hrightFormula : formulaSymbolCount rightFormula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactListedProof,
            decodeCompactSequentList_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              leftFormula fuel hleftFormula,
            decodeCompactFormula_binaryFormulaCode_append
              rightFormula fuel hrightFormula,
            ih fuel hpremise, toListed]
  | all Gamma formula premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula : formulaSymbolCount formula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactListedProof,
            decodeCompactSequentList_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula,
            ih fuel hpremise, toListed]
  | exs Gamma formula witness premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula : formulaSymbolCount formula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hwitness : termSymbolCount witness < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactListedProof,
            decodeCompactSequentList_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula,
            decodeCompactTerm_binaryTermCode_append witness fuel hwitness,
            ih fuel hpremise, toListed]
  | wk Gamma premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactListedProof,
            decodeCompactSequentList_canonicalBinaryCode_append
              Gamma fuel hseq,
            ih fuel hpremise, toListed]
  | shift Gamma premise ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hpremise : premise.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactListedProof,
            decodeCompactSequentList_canonicalBinaryCode_append
              Gamma fuel hseq,
            ih fuel hpremise, toListed]
  | cut Gamma formula left right ihLeft ihRight =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula : formulaSymbolCount formula < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hleft : left.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hright : right.parseWeight < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactListedProof,
            decodeCompactSequentList_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula,
            ihLeft fuel hleft, ihRight fuel hright,
            toListed]

#print axioms decodeCompactListedProof_canonicalBinaryCode_append

end FoundationCompactListedProofEncoder
