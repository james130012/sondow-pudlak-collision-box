import integration.FoundationCompactNumericListedDirectVerifierTypedNonLeafGlobalBound

/-!
# Globally bounded canonical root-parse rows for non-leaf nodes

Each constructor below exposes the actual one-step child schedule of the
numeric listed task machine.  Root parsing depends only on the canonical proof
and structural-certificate shapes, so no certificate-validity hypothesis is
needed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCanonicalNonLeafRowsGlobalBound

open FoundationCompactPAAxiomCertificate
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertificateVerifier
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierTypedNonLeafGlobalBound

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierCanonicalAndCheckedStepRow_with_globalBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree :=
      .and Gamma leftFormula rightFormula left right
    let structuralCertificate : StructuralValidityCertificate :=
      .binary leftCertificate rightCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((compactListedProofTokens left ++ compactListedProofTokens right ++
            proofSuffix,
          compactStructuralCertificateTokens leftCertificate ++
            compactStructuralCertificateTokens rightCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: compactNumericParseTask ::
          compactNumericCombineTask 3 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
                rowWeight := by
  dsimp only
  intro hcurrent hnext
  let tree : ListedCheckedPAProofTree :=
    .and Gamma leftFormula rightFormula left right
  let structuralCertificate : StructuralValidityCertificate :=
    .binary leftCertificate rightCertificate
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens structuralCertificate ++
      certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected structuralCertificate
      certificateSuffix
  let nextProofTokens :=
    compactListedProofTokens left ++ compactListedProofTokens right ++
      proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens leftCertificate ++
      compactStructuralCertificateTokens rightCertificate ++
      certificateSuffix
  let nextTasks :=
    compactNumericParseTask :: compactNumericParseTask ::
      compactNumericCombineTask 3 proofNode.2 :: restTasks
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((nextProofTokens, nextCertificateTokens), (nextTasks, values)), none)
  have hcurrent' :
      compactNumericVerifierStateWeight currentState <= rowWeight := by
    simpa only [currentState, proofTokens, certificateTokens, tree,
      structuralCertificate] using hcurrent
  have hnext' :
      compactNumericVerifierStateWeight nextState <= rowWeight := by
    simpa only [nextState, nextProofTokens, nextCertificateTokens,
      nextTasks, proofNode, tree] using hnext
  have hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode := by
    simp only [proofTokens, proofNode, tree,
      compactListedProofNodeFieldsParser_canonical_append]
  have hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simp only [certificateTokens, certificateNode, structuralCertificate,
      compactStructuralCertificateNodeParser_canonical_append]
  have hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/
      proofNode.1 = 5 \/ proofNode.1 = 6 \/ proofNode.1 = 7 \/
      proofNode.1 = 8 \/ proofNode.1 = 9 := by
    simp [proofNode, tree, compactListedProofNodeExpectedFields]
  have htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, structuralCertificate,
      nextProofTokens, nextCertificateTokens, nextTasks,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition,
      List.append_assoc]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values))).mp htransition
  have hrow :=
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalBound
      proofTokens certificateTokens nextProofTokens nextCertificateTokens
      restTasks nextTasks values values proofNode certificateNode
      hproofParser hcertificateParser hproofTag houtputCase
      hcurrent' hnext'
  simpa only [currentState, nextState, proofTokens, certificateTokens,
    nextProofTokens, nextCertificateTokens, nextTasks, proofNode, tree,
    structuralCertificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierCanonicalOrCheckedStepRow_with_globalBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (leftFormula rightFormula : LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree :=
      .or Gamma leftFormula rightFormula premise
    let structuralCertificate : StructuralValidityCertificate :=
      .unary premiseCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((compactListedProofTokens premise ++ proofSuffix,
          compactStructuralCertificateTokens premiseCertificate ++
            certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 4 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
                rowWeight := by
  dsimp only
  intro hcurrent hnext
  let tree : ListedCheckedPAProofTree :=
    .or Gamma leftFormula rightFormula premise
  let structuralCertificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens structuralCertificate ++
      certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected structuralCertificate
      certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask ::
    compactNumericCombineTask 4 proofNode.2 :: restTasks
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((nextProofTokens, nextCertificateTokens), (nextTasks, values)), none)
  have hcurrent' :
      compactNumericVerifierStateWeight currentState <= rowWeight := by
    simpa only [currentState, proofTokens, certificateTokens, tree,
      structuralCertificate] using hcurrent
  have hnext' :
      compactNumericVerifierStateWeight nextState <= rowWeight := by
    simpa only [nextState, nextProofTokens, nextCertificateTokens,
      nextTasks, proofNode, tree] using hnext
  have hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode := by
    simp only [proofTokens, proofNode, tree,
      compactListedProofNodeFieldsParser_canonical_append]
  have hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simp only [certificateTokens, certificateNode, structuralCertificate,
      compactStructuralCertificateNodeParser_canonical_append]
  have hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/
      proofNode.1 = 5 \/ proofNode.1 = 6 \/ proofNode.1 = 7 \/
      proofNode.1 = 8 \/ proofNode.1 = 9 := by
    simp [proofNode, tree, compactListedProofNodeExpectedFields]
  have htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, structuralCertificate,
      nextProofTokens, nextCertificateTokens, nextTasks,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values))).mp htransition
  have hrow :=
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalBound
      proofTokens certificateTokens nextProofTokens nextCertificateTokens
      restTasks nextTasks values values proofNode certificateNode
      hproofParser hcertificateParser hproofTag houtputCase
      hcurrent' hnext'
  simpa only [currentState, nextState, proofTokens, certificateTokens,
    nextProofTokens, nextCertificateTokens, nextTasks, proofNode, tree,
    structuralCertificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierCanonicalAllCheckedStepRow_with_globalBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .all Gamma formula premise
    let structuralCertificate : StructuralValidityCertificate :=
      .unary premiseCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((compactListedProofTokens premise ++ proofSuffix,
          compactStructuralCertificateTokens premiseCertificate ++
            certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 5 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
                rowWeight := by
  dsimp only
  intro hcurrent hnext
  let tree : ListedCheckedPAProofTree := .all Gamma formula premise
  let structuralCertificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens structuralCertificate ++
      certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected structuralCertificate
      certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask ::
    compactNumericCombineTask 5 proofNode.2 :: restTasks
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((nextProofTokens, nextCertificateTokens), (nextTasks, values)), none)
  have hcurrent' :
      compactNumericVerifierStateWeight currentState <= rowWeight := by
    simpa only [currentState, proofTokens, certificateTokens, tree,
      structuralCertificate] using hcurrent
  have hnext' :
      compactNumericVerifierStateWeight nextState <= rowWeight := by
    simpa only [nextState, nextProofTokens, nextCertificateTokens,
      nextTasks, proofNode, tree] using hnext
  have hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode := by
    simp only [proofTokens, proofNode, tree,
      compactListedProofNodeFieldsParser_canonical_append]
  have hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simp only [certificateTokens, certificateNode, structuralCertificate,
      compactStructuralCertificateNodeParser_canonical_append]
  have hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/
      proofNode.1 = 5 \/ proofNode.1 = 6 \/ proofNode.1 = 7 \/
      proofNode.1 = 8 \/ proofNode.1 = 9 := by
    simp [proofNode, tree, compactListedProofNodeExpectedFields]
  have htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, structuralCertificate,
      nextProofTokens, nextCertificateTokens, nextTasks,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values))).mp htransition
  have hrow :=
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalBound
      proofTokens certificateTokens nextProofTokens nextCertificateTokens
      restTasks nextTasks values values proofNode certificateNode
      hproofParser hcertificateParser hproofTag houtputCase
      hcurrent' hnext'
  simpa only [currentState, nextState, proofTokens, certificateTokens,
    nextProofTokens, nextCertificateTokens, nextTasks, proofNode, tree,
    structuralCertificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierCanonicalExsCheckedStepRow_with_globalBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree :=
      .exs Gamma formula witness premise
    let structuralCertificate : StructuralValidityCertificate :=
      .unary premiseCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((compactListedProofTokens premise ++ proofSuffix,
          compactStructuralCertificateTokens premiseCertificate ++
            certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 6 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
                rowWeight := by
  dsimp only
  intro hcurrent hnext
  let tree : ListedCheckedPAProofTree :=
    .exs Gamma formula witness premise
  let structuralCertificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens structuralCertificate ++
      certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected structuralCertificate
      certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask ::
    compactNumericCombineTask 6 proofNode.2 :: restTasks
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((nextProofTokens, nextCertificateTokens), (nextTasks, values)), none)
  have hcurrent' :
      compactNumericVerifierStateWeight currentState <= rowWeight := by
    simpa only [currentState, proofTokens, certificateTokens, tree,
      structuralCertificate] using hcurrent
  have hnext' :
      compactNumericVerifierStateWeight nextState <= rowWeight := by
    simpa only [nextState, nextProofTokens, nextCertificateTokens,
      nextTasks, proofNode, tree] using hnext
  have hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode := by
    simp only [proofTokens, proofNode, tree,
      compactListedProofNodeFieldsParser_canonical_append]
  have hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simp only [certificateTokens, certificateNode, structuralCertificate,
      compactStructuralCertificateNodeParser_canonical_append]
  have hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/
      proofNode.1 = 5 \/ proofNode.1 = 6 \/ proofNode.1 = 7 \/
      proofNode.1 = 8 \/ proofNode.1 = 9 := by
    simp [proofNode, tree, compactListedProofNodeExpectedFields]
  have htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, structuralCertificate,
      nextProofTokens, nextCertificateTokens, nextTasks,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values))).mp htransition
  have hrow :=
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalBound
      proofTokens certificateTokens nextProofTokens nextCertificateTokens
      restTasks nextTasks values values proofNode certificateNode
      hproofParser hcertificateParser hproofTag houtputCase
      hcurrent' hnext'
  simpa only [currentState, nextState, proofTokens, certificateTokens,
    nextProofTokens, nextCertificateTokens, nextTasks, proofNode, tree,
    structuralCertificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierCanonicalWkCheckedStepRow_with_globalBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .wk Gamma premise
    let structuralCertificate : StructuralValidityCertificate :=
      .unary premiseCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((compactListedProofTokens premise ++ proofSuffix,
          compactStructuralCertificateTokens premiseCertificate ++
            certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 7 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
                rowWeight := by
  dsimp only
  intro hcurrent hnext
  let tree : ListedCheckedPAProofTree := .wk Gamma premise
  let structuralCertificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens structuralCertificate ++
      certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected structuralCertificate
      certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask ::
    compactNumericCombineTask 7 proofNode.2 :: restTasks
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((nextProofTokens, nextCertificateTokens), (nextTasks, values)), none)
  have hcurrent' :
      compactNumericVerifierStateWeight currentState <= rowWeight := by
    simpa only [currentState, proofTokens, certificateTokens, tree,
      structuralCertificate] using hcurrent
  have hnext' :
      compactNumericVerifierStateWeight nextState <= rowWeight := by
    simpa only [nextState, nextProofTokens, nextCertificateTokens,
      nextTasks, proofNode, tree] using hnext
  have hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode := by
    simp only [proofTokens, proofNode, tree,
      compactListedProofNodeFieldsParser_canonical_append]
  have hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simp only [certificateTokens, certificateNode, structuralCertificate,
      compactStructuralCertificateNodeParser_canonical_append]
  have hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/
      proofNode.1 = 5 \/ proofNode.1 = 6 \/ proofNode.1 = 7 \/
      proofNode.1 = 8 \/ proofNode.1 = 9 := by
    simp [proofNode, tree, compactListedProofNodeExpectedFields]
  have htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, structuralCertificate,
      nextProofTokens, nextCertificateTokens, nextTasks,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values))).mp htransition
  have hrow :=
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalBound
      proofTokens certificateTokens nextProofTokens nextCertificateTokens
      restTasks nextTasks values values proofNode certificateNode
      hproofParser hcertificateParser hproofTag houtputCase
      hcurrent' hnext'
  simpa only [currentState, nextState, proofTokens, certificateTokens,
    nextProofTokens, nextCertificateTokens, nextTasks, proofNode, tree,
    structuralCertificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierCanonicalShiftCheckedStepRow_with_globalBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (premise : ListedCheckedPAProofTree)
    (premiseCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .shift Gamma premise
    let structuralCertificate : StructuralValidityCertificate :=
      .unary premiseCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((compactListedProofTokens premise ++ proofSuffix,
          compactStructuralCertificateTokens premiseCertificate ++
            certificateSuffix),
        (compactNumericParseTask ::
          compactNumericCombineTask 8 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
                rowWeight := by
  dsimp only
  intro hcurrent hnext
  let tree : ListedCheckedPAProofTree := .shift Gamma premise
  let structuralCertificate : StructuralValidityCertificate :=
    .unary premiseCertificate
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens structuralCertificate ++
      certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected structuralCertificate
      certificateSuffix
  let nextProofTokens := compactListedProofTokens premise ++ proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens premiseCertificate ++
      certificateSuffix
  let nextTasks := compactNumericParseTask ::
    compactNumericCombineTask 8 proofNode.2 :: restTasks
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((nextProofTokens, nextCertificateTokens), (nextTasks, values)), none)
  have hcurrent' :
      compactNumericVerifierStateWeight currentState <= rowWeight := by
    simpa only [currentState, proofTokens, certificateTokens, tree,
      structuralCertificate] using hcurrent
  have hnext' :
      compactNumericVerifierStateWeight nextState <= rowWeight := by
    simpa only [nextState, nextProofTokens, nextCertificateTokens,
      nextTasks, proofNode, tree] using hnext
  have hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode := by
    simp only [proofTokens, proofNode, tree,
      compactListedProofNodeFieldsParser_canonical_append]
  have hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simp only [certificateTokens, certificateNode, structuralCertificate,
      compactStructuralCertificateNodeParser_canonical_append]
  have hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/
      proofNode.1 = 5 \/ proofNode.1 = 6 \/ proofNode.1 = 7 \/
      proofNode.1 = 8 \/ proofNode.1 = 9 := by
    simp [proofNode, tree, compactListedProofNodeExpectedFields]
  have htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, structuralCertificate,
      nextProofTokens, nextCertificateTokens, nextTasks,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values))).mp htransition
  have hrow :=
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalBound
      proofTokens certificateTokens nextProofTokens nextCertificateTokens
      restTasks nextTasks values values proofNode certificateNode
      hproofParser hcertificateParser hproofTag houtputCase
      hcurrent' hnext'
  simpa only [currentState, nextState, proofTokens, certificateTokens,
    nextProofTokens, nextCertificateTokens, nextTasks, proofNode, tree,
    structuralCertificate] using hrow

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem
    exists_compactNumericVerifierCanonicalCutCheckedStepRow_with_globalBound
    (Gamma : List LO.FirstOrder.ArithmeticProposition)
    (formula : LO.FirstOrder.ArithmeticProposition)
    (left right : ListedCheckedPAProofTree)
    (leftCertificate rightCertificate : StructuralValidityCertificate)
    (proofSuffix certificateSuffix : List Nat)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    {rowWeight : Nat} :
    let tree : ListedCheckedPAProofTree := .cut Gamma formula left right
    let structuralCertificate : StructuralValidityCertificate :=
      .binary leftCertificate rightCertificate
    let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
    let currentState : CompactNumericVerifierState :=
      (((compactListedProofTokens tree ++ proofSuffix,
          compactStructuralCertificateTokens structuralCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: restTasks, values)), none)
    let nextState : CompactNumericVerifierState :=
      (((compactListedProofTokens left ++ compactListedProofTokens right ++
            proofSuffix,
          compactStructuralCertificateTokens leftCertificate ++
            compactStructuralCertificateTokens rightCertificate ++
            certificateSuffix),
        (compactNumericParseTask :: compactNumericParseTask ::
          compactNumericCombineTask 9 proofNode.2 :: restTasks, values)),
        none)
    compactNumericVerifierStateWeight currentState <= rowWeight ->
      compactNumericVerifierStateWeight nextState <= rowWeight ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = currentState /\
          row.nextState = nextState /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <=
              compactNumericVerifierTypedNonLeafGlobalCoordinateSizeBound
                rowWeight := by
  dsimp only
  intro hcurrent hnext
  let tree : ListedCheckedPAProofTree := .cut Gamma formula left right
  let structuralCertificate : StructuralValidityCertificate :=
    .binary leftCertificate rightCertificate
  let proofTokens := compactListedProofTokens tree ++ proofSuffix
  let certificateTokens :=
    compactStructuralCertificateTokens structuralCertificate ++
      certificateSuffix
  let proofNode := compactListedProofNodeExpectedFields tree proofSuffix
  let certificateNode :=
    compactStructuralCertificateNodeExpected structuralCertificate
      certificateSuffix
  let nextProofTokens :=
    compactListedProofTokens left ++ compactListedProofTokens right ++
      proofSuffix
  let nextCertificateTokens :=
    compactStructuralCertificateTokens leftCertificate ++
      compactStructuralCertificateTokens rightCertificate ++
      certificateSuffix
  let nextTasks :=
    compactNumericParseTask :: compactNumericParseTask ::
      compactNumericCombineTask 9 proofNode.2 :: restTasks
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens),
      (compactNumericParseTask :: restTasks, values)), none)
  let nextState : CompactNumericVerifierState :=
    (((nextProofTokens, nextCertificateTokens), (nextTasks, values)), none)
  have hcurrent' :
      compactNumericVerifierStateWeight currentState <= rowWeight := by
    simpa only [currentState, proofTokens, certificateTokens, tree,
      structuralCertificate] using hcurrent
  have hnext' :
      compactNumericVerifierStateWeight nextState <= rowWeight := by
    simpa only [nextState, nextProofTokens, nextCertificateTokens,
      nextTasks, proofNode, tree] using hnext
  have hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode := by
    simp only [proofTokens, proofNode, tree,
      compactListedProofNodeFieldsParser_canonical_append]
  have hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode := by
    simp only [certificateTokens, certificateNode, structuralCertificate,
      compactStructuralCertificateNodeParser_canonical_append]
  have hproofTag : proofNode.1 = 3 \/ proofNode.1 = 4 \/
      proofNode.1 = 5 \/ proofNode.1 = 6 \/ proofNode.1 = 7 \/
      proofNode.1 = 8 \/ proofNode.1 = 9 := by
    simp [proofNode, tree, compactListedProofNodeExpectedFields]
  have htransition : compactNumericNodeTransition proofNode certificateNode
      restTasks values =
        some ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values)) := by
    simp [proofNode, certificateNode, tree, structuralCertificate,
      nextProofTokens, nextCertificateTokens, nextTasks,
      compactListedProofNodeExpectedFields,
      compactStructuralCertificateNodeExpected,
      compactNumericNodeFieldsSuffix, compactNumericNodeTransition,
      List.append_assoc]
  have houtputCase : CompactNumericNodeTransitionOutputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens), (nextTasks, values)) :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode restTasks values
        ((nextProofTokens, nextCertificateTokens),
          (nextTasks, values))).mp htransition
  have hrow :=
    exists_compactNumericVerifierNonLeafCheckedStepRow_of_outputCase_with_globalBound
      proofTokens certificateTokens nextProofTokens nextCertificateTokens
      restTasks nextTasks values values proofNode certificateNode
      hproofParser hcertificateParser hproofTag houtputCase
      hcurrent' hnext'
  simpa only [currentState, nextState, proofTokens, certificateTokens,
    nextProofTokens, nextCertificateTokens, nextTasks, proofNode, tree,
    structuralCertificate] using hrow

#print axioms
  exists_compactNumericVerifierCanonicalAndCheckedStepRow_with_globalBound
#print axioms
  exists_compactNumericVerifierCanonicalOrCheckedStepRow_with_globalBound
#print axioms
  exists_compactNumericVerifierCanonicalAllCheckedStepRow_with_globalBound
#print axioms
  exists_compactNumericVerifierCanonicalExsCheckedStepRow_with_globalBound
#print axioms
  exists_compactNumericVerifierCanonicalWkCheckedStepRow_with_globalBound
#print axioms
  exists_compactNumericVerifierCanonicalShiftCheckedStepRow_with_globalBound
#print axioms
  exists_compactNumericVerifierCanonicalCutCheckedStepRow_with_globalBound

end FoundationCompactNumericListedDirectVerifierCanonicalNonLeafRowsGlobalBound
