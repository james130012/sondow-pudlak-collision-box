import integration.FoundationCompactCertifiedPAProof

/-!
# Computable canonical encoding of compact PA proof trees

`Finset.toList` is proof-irrelevant but noncomputable.  We instead sort every
displayed sequent by its injective binary formula code.  This yields an
executable encoder with exactly the same payload length as the earlier
order-independent encoding.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationComputableCompactPAProofEncoder

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof

@[reducible] def formulaCodeLinearOrder :
    LinearOrder LO.FirstOrder.ArithmeticProposition :=
  LinearOrder.lift' binaryFormulaCode binaryFormulaCode_injective

def canonicalSequentList
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) :
    List LO.FirstOrder.ArithmeticProposition := by
  letI := formulaCodeLinearOrder
  exact Gamma.sort (fun left right => left ≤ right)

@[simp] theorem canonicalSequentList_length
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) :
    (canonicalSequentList Gamma).length = Gamma.card := by
  simp [canonicalSequentList]

@[simp] theorem mem_canonicalSequentList
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    {formula : LO.FirstOrder.ArithmeticProposition} :
    formula ∈ canonicalSequentList Gamma ↔ formula ∈ Gamma := by
  simp [canonicalSequentList]

@[simp] theorem canonicalSequentList_toFinset
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) :
    (canonicalSequentList Gamma).toFinset = Gamma := by
  ext formula
  simp

theorem canonicalSequentList_perm_toList
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) :
    (canonicalSequentList Gamma).Perm Gamma.toList := by
  rw [← Multiset.coe_eq_coe, Finset.coe_toList]
  simpa [canonicalSequentList] using
    (Finset.sort_eq Gamma
      (fun left right => @LE.le _ formulaCodeLinearOrder left right))

def canonicalBinarySequentCode
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) : List Bool :=
  binaryNatCode Gamma.card ++
    (canonicalSequentList Gamma).flatMap binaryFormulaCode

theorem canonicalFormulaPayload_length
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) :
    ((canonicalSequentList Gamma).flatMap binaryFormulaCode).length =
      (Gamma.toList.flatMap binaryFormulaCode).length := by
  rw [List.length_flatMap, List.length_flatMap]
  exact ((canonicalSequentList_perm_toList Gamma).map
    (fun formula => (binaryFormulaCode formula).length)).sum_eq

theorem canonicalBinarySequentCode_length
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition) :
    (canonicalBinarySequentCode Gamma).length =
      (binarySequentCode Gamma).length := by
  simp only [canonicalBinarySequentCode, binarySequentCode,
    List.length_append]
  rw [canonicalFormulaPayload_length]

theorem decodeCompactSequent_canonicalBinaryCode_append
    (Gamma : Finset LO.FirstOrder.ArithmeticProposition)
    (fuel : Nat) (hfuel : sequentSymbolCount Gamma < fuel)
    (suffix : List Bool) :
    decodeCompactSequent fuel
        (canonicalBinarySequentCode Gamma ++ suffix) =
      some (Gamma, suffix) := by
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
        formulaSymbolCount formula ≤ Gamma.sum formulaSymbolCount :=
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
  simp [canonicalBinarySequentCode, decodeCompactSequent,
    hmany', formulaVector]

def canonicalBinaryProofCode :
    CheckedPAProofTree → List Bool
  | .closed Gamma formula =>
      binaryNatCode 0 ++ canonicalBinarySequentCode Gamma ++
        binaryFormulaCode formula
  | .axm Gamma sigma =>
      binaryNatCode 1 ++ canonicalBinarySequentCode Gamma ++
        binaryFormulaCode
          (Rewriting.emb sigma : LO.FirstOrder.ArithmeticProposition)
  | .verum Gamma =>
      binaryNatCode 2 ++ canonicalBinarySequentCode Gamma
  | .and Gamma leftFormula rightFormula left right =>
      binaryNatCode 3 ++ canonicalBinarySequentCode Gamma ++
        binaryFormulaCode leftFormula ++ binaryFormulaCode rightFormula ++
        canonicalBinaryProofCode left ++ canonicalBinaryProofCode right
  | .or Gamma leftFormula rightFormula premise =>
      binaryNatCode 4 ++ canonicalBinarySequentCode Gamma ++
        binaryFormulaCode leftFormula ++ binaryFormulaCode rightFormula ++
        canonicalBinaryProofCode premise
  | .all Gamma formula premise =>
      binaryNatCode 5 ++ canonicalBinarySequentCode Gamma ++
        binaryFormulaCode formula ++ canonicalBinaryProofCode premise
  | .exs Gamma formula witness premise =>
      binaryNatCode 6 ++ canonicalBinarySequentCode Gamma ++
        binaryFormulaCode formula ++ binaryTermCode witness ++
        canonicalBinaryProofCode premise
  | .wk Gamma premise =>
      binaryNatCode 7 ++ canonicalBinarySequentCode Gamma ++
        canonicalBinaryProofCode premise
  | .shift Gamma premise =>
      binaryNatCode 8 ++ canonicalBinarySequentCode Gamma ++
        canonicalBinaryProofCode premise
  | .cut Gamma formula left right =>
      binaryNatCode 9 ++ canonicalBinarySequentCode Gamma ++
        binaryFormulaCode formula ++ canonicalBinaryProofCode left ++
        canonicalBinaryProofCode right

theorem canonicalBinaryProofCode_length
    (tree : CheckedPAProofTree) :
    (canonicalBinaryProofCode tree).length = tree.binaryCode.length := by
  induction tree <;>
    simp [canonicalBinaryProofCode,
      CheckedPAProofTree.binaryCode,
      canonicalBinarySequentCode_length, *]

theorem decodeCompactProof_canonicalBinaryCode_append
    (tree : CheckedPAProofTree) (fuel : Nat)
    (hfuel : tree.parseWeight < fuel) (suffix : List Bool) :
    decodeCompactProof fuel (canonicalBinaryProofCode tree ++ suffix) =
      some (tree, suffix) := by
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
          simp [canonicalBinaryProofCode, decodeCompactProof,
            decodeCompactSequent_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula]
  | axm Gamma sigma =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          have hformula :
              formulaSymbolCount
                  (Rewriting.emb sigma :
                    LO.FirstOrder.ArithmeticProposition) < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactProof,
            decodeCompactSequent_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              (Rewriting.emb sigma :
                LO.FirstOrder.ArithmeticProposition) fuel hformula,
            propositionToSentence]
  | verum Gamma =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hseq : sequentSymbolCount Gamma < fuel := by
            simp [CheckedPAProofTree.parseWeight] at hfuel
            omega
          simp [canonicalBinaryProofCode, decodeCompactProof,
            decodeCompactSequent_canonicalBinaryCode_append
              Gamma fuel hseq]
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
          simp [canonicalBinaryProofCode, decodeCompactProof,
            decodeCompactSequent_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              leftFormula fuel hleftFormula,
            decodeCompactFormula_binaryFormulaCode_append
              rightFormula fuel hrightFormula,
            ihLeft fuel hleft, ihRight fuel hright]
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
          simp [canonicalBinaryProofCode, decodeCompactProof,
            decodeCompactSequent_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              leftFormula fuel hleftFormula,
            decodeCompactFormula_binaryFormulaCode_append
              rightFormula fuel hrightFormula,
            ih fuel hpremise]
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
          simp [canonicalBinaryProofCode, decodeCompactProof,
            decodeCompactSequent_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula,
            ih fuel hpremise]
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
          simp [canonicalBinaryProofCode, decodeCompactProof,
            decodeCompactSequent_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula,
            decodeCompactTerm_binaryTermCode_append
              witness fuel hwitness,
            ih fuel hpremise]
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
          simp [canonicalBinaryProofCode, decodeCompactProof,
            decodeCompactSequent_canonicalBinaryCode_append
              Gamma fuel hseq,
            ih fuel hpremise]
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
          simp [canonicalBinaryProofCode, decodeCompactProof,
            decodeCompactSequent_canonicalBinaryCode_append
              Gamma fuel hseq,
            ih fuel hpremise]
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
          simp [canonicalBinaryProofCode, decodeCompactProof,
            decodeCompactSequent_canonicalBinaryCode_append
              Gamma fuel hseq,
            decodeCompactFormula_binaryFormulaCode_append
              formula fuel hformula,
            ihLeft fuel hleft, ihRight fuel hright]

def canonicalBinaryCertifiedPAProofCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) : List Bool :=
  canonicalBinaryProofCode tree ++
    binaryStructuralValidityCertificateCode certificate

theorem canonicalBinaryCertifiedPAProofCode_length
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    (canonicalBinaryCertifiedPAProofCode tree certificate).length =
      (binaryCertifiedPAProofCode tree certificate).length := by
  simp [canonicalBinaryCertifiedPAProofCode,
    binaryCertifiedPAProofCode,
    canonicalBinaryProofCode_length]

theorem decodeCompactCertifiedPAProof_canonicalBinaryCode_append
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate)
    (fuel : Nat)
    (htree : tree.parseWeight < fuel)
    (hcertificate : structuralCertificateParseWeight certificate < fuel)
    (suffix : List Bool) :
    decodeCompactCertifiedPAProof fuel
        (canonicalBinaryCertifiedPAProofCode tree certificate ++ suffix) =
      some ((tree, certificate), suffix) := by
  simp [decodeCompactCertifiedPAProof,
    canonicalBinaryCertifiedPAProofCode,
    decodeCompactProof_canonicalBinaryCode_append tree fuel htree,
    decodeStructuralValidityCertificate_binaryCode_append
      certificate fuel hcertificate]

def canonicalPackedCertifiedPAProofCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) : Nat :=
  packBinaryString (canonicalBinaryCertifiedPAProofCode tree certificate)

@[simp] theorem decodeCompactPackedCertifiedPAProof_canonicalPackedCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    decodeCompactPackedCertifiedPAProof
        (canonicalPackedCertifiedPAProofCode tree certificate) =
      some (tree, certificate) := by
  have htree :
      tree.parseWeight <
        (canonicalBinaryCertifiedPAProofCode tree certificate).length + 1 := by
    have hweight := tree.parseWeight_le_binaryLength
    rw [CheckedPAProofTree.binaryLength] at hweight
    have hcanonical := canonicalBinaryProofCode_length tree
    simp only [canonicalBinaryCertifiedPAProofCode, List.length_append]
    omega
  have hcertificate :
      structuralCertificateParseWeight certificate <
        (canonicalBinaryCertifiedPAProofCode tree certificate).length + 1 := by
    have hweight :=
      structuralCertificateParseWeight_le_binaryCode_length certificate
    simp only [canonicalBinaryCertifiedPAProofCode, List.length_append]
    omega
  have hdecode :
      decodeCompactCertifiedPAProof
          ((canonicalBinaryCertifiedPAProofCode tree certificate).length + 1)
          (canonicalBinaryCertifiedPAProofCode tree certificate) =
        some ((tree, certificate), []) := by
    simpa using
      decodeCompactCertifiedPAProof_canonicalBinaryCode_append
        tree certificate
          ((canonicalBinaryCertifiedPAProofCode tree certificate).length + 1)
          htree hcertificate []
  simp [decodeCompactPackedCertifiedPAProof,
    canonicalPackedCertifiedPAProofCode,
    hdecode]

@[simp] theorem size_canonicalPackedCertifiedPAProofCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    Nat.size (canonicalPackedCertifiedPAProofCode tree certificate) =
      (canonicalBinaryCertifiedPAProofCode tree certificate).length + 1 := by
  simp [canonicalPackedCertifiedPAProofCode]

@[simp] theorem packedPayloadLength_canonicalPackedCertifiedPAProofCode
    (tree : CheckedPAProofTree)
    (certificate : StructuralValidityCertificate) :
    packedPayloadLength
        (canonicalPackedCertifiedPAProofCode tree certificate) =
      (canonicalBinaryCertifiedPAProofCode tree certificate).length := by
  simp [packedPayloadLength]

end FoundationComputableCompactPAProofEncoder
