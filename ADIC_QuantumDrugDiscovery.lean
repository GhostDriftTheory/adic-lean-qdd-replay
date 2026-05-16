import Mathlib
import Adic.ADIC_RSound_Replay

set_option linter.style.whitespace false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

/-!
ADIC Quantum Drug Discovery Replay Core

Domain layer for quantum-assisted drug-discovery candidate selection.
This file does not formalize quantum mechanics or therapeutic efficacy.
It encodes the decision evidence layer as ADIC replay roots of the form
"violation <= 0".
-/

namespace ADIC

noncomputable section

namespace QuantumDrugDiscovery

open ReplayCore

/-- A program variable together with its certified interval. -/
structure QDDVar (D : DPos) where
  idx  : Nat
  cert : IEnc D

/-- Encoded fixed-point policy thresholds.  A field `k : Int` denotes `k / D`. -/
structure ScreeningPolicy (D : DPos) where
  maxEnergy          : Int
  minPredictionScore : Int
  maxErrorBound      : Int
  requireApproval    : Bool

/-- The decision variables exposed by the program replay environment. -/
structure DecisionVars (D : DPos) where
  energyEstimate  : QDDVar D
  predictionScore : QDDVar D
  errorBound      : QDDVar D
  approvalFlag    : QDDVar D

/-- Boolean approval encoded in the same fixed-point scale as the replay core. -/
def boolEnc (D : DPos) (b : Bool) : Int :=
  if b then ((D : Nat) : Int) else 0

/-- Singleton interval for an encoded threshold. -/
def constI (D : DPos) (k : Int) : IEnc D :=
  ReplayCore.ISingleton D k

/-- energy - maxEnergy <= 0. -/
def energyViolationCert
    (D : DPos)
    (v : DecisionVars D)
    (p : ScreeningPolicy D) : IEnc D :=
  Primitives.T_sub D v.energyEstimate.cert (constI D p.maxEnergy)

/-- minPredictionScore - predictionScore <= 0. -/
def scoreViolationCert
    (D : DPos)
    (v : DecisionVars D)
    (p : ScreeningPolicy D) : IEnc D :=
  Primitives.T_sub D (constI D p.minPredictionScore) v.predictionScore.cert

/-- errorBound - maxErrorBound <= 0. -/
def errorViolationCert
    (D : DPos)
    (v : DecisionVars D)
    (p : ScreeningPolicy D) : IEnc D :=
  Primitives.T_sub D v.errorBound.cert (constI D p.maxErrorBound)

/-- requireApproval - approvalFlag <= 0. -/
def approvalViolationCert
    (D : DPos)
    (v : DecisionVars D)
    (p : ScreeningPolicy D) : IEnc D :=
  Primitives.T_sub D (constI D (boolEnc D p.requireApproval)) v.approvalFlag.cert

/--
Specification rows for the four declared QDD selection constraints.
Rows are post-order and roots point to the four violation rows.

0  energy
1  maxEnergy
2  energy - maxEnergy
3  predictionScore
4  minPredictionScore
5  minPredictionScore - predictionScore
6  errorBound
7  maxErrorBound
8  errorBound - maxErrorBound
9  approvalFlag
10 requireApproval
11 requireApproval - approvalFlag
-/
def qddSpecRows
    (D : DPos)
    (v : DecisionVars D)
    (p : ScreeningPolicy D) : List (ReplayCore.SpecRow D) :=
  [ ReplayCore.SpecRow.var v.energyEstimate.idx v.energyEstimate.cert
  , ReplayCore.SpecRow.const p.maxEnergy
  , ReplayCore.SpecRow.sub 0 1 (energyViolationCert D v p)
  , ReplayCore.SpecRow.var v.predictionScore.idx v.predictionScore.cert
  , ReplayCore.SpecRow.const p.minPredictionScore
  , ReplayCore.SpecRow.sub 4 3 (scoreViolationCert D v p)
  , ReplayCore.SpecRow.var v.errorBound.idx v.errorBound.cert
  , ReplayCore.SpecRow.const p.maxErrorBound
  , ReplayCore.SpecRow.sub 6 7 (errorViolationCert D v p)
  , ReplayCore.SpecRow.var v.approvalFlag.idx v.approvalFlag.cert
  , ReplayCore.SpecRow.const (boolEnc D p.requireApproval)
  , ReplayCore.SpecRow.sub 10 9 (approvalViolationCert D v p)
  ]

/-- Root indices corresponding to the four QDD violation expressions. -/
def qddRoots : List Nat := [2, 5, 8, 11]

/-- ADIC certificate obtained by adding the QDD domain specification layer. -/
def qddCert
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (v : DecisionVars D)
    (p : ScreeningPolicy D) : ReplayCore.Cert D :=
  { rows := rows
    specRows := qddSpecRows D v p
    roots := qddRoots }

/-- Domain-level validity: all QDD violation expressions evaluate to <= 0. -/
def QDDReplayValid
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (v : DecisionVars D)
    (p : ScreeningPolicy D) : Prop :=
  ReplayCore.SemanticValid D rows (qddSpecRows D v p) qddRoots

/-- Main QDD soundness theorem: verifier acceptance implies QDD replay validity. -/
theorem qdd_replay_sound
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (v : DecisionVars D)
    (p : ScreeningPolicy D) :
    ReplayCore.verifierBool D (qddCert D rows v p) = true →
    QDDReplayValid D rows v p := by
  intro h
  exact ReplayCore.verifierBool_sound D (qddCert D rows v p) h

/-- Product-verifier version for a deployed checker matching the Lean verifier. -/
theorem qdd_productVerifier_sound
    (D : DPos)
    (checker : ReplayCore.Cert D → Bool)
    (rows : List (ReplayCore.ProgRow D))
    (v : DecisionVars D)
    (p : ScreeningPolicy D) :
    ReplayCore.ProductVerifierMatches D checker →
    checker (qddCert D rows v p) = true →
    QDDReplayValid D rows v p := by
  intro hMatch hAccept
  exact ReplayCore.productVerifier_sound D checker (qddCert D rows v p) hMatch hAccept

/-! ## Expanded QDD candidate-selection artifact

--
The following section extends the minimal quantum‐drug discovery (QDD) replay layer
with a richer domain model and decision logic.  It introduces identifiers and records
to capture the provenance of quantum calculations, classical AI screening, ADMET
metrics, uncertainty, approvals and more.  It then defines structured
selection, rejection and review policies and the corresponding violation
certificates and replay validity predicates.  Finally, it proves soundness
theorems showing that a successful ADIC verifier run implies the declared
decision is semantically valid within this expanded QDD domain.

These additions do not remove any existing definitions; they merely
provide a more expressive layer on top of the existing four-condition example.

Within this section we remain inside the `QuantumDrugDiscovery` namespace.

  -/

/-! ### Domain identifiers and records -/

-- Identifiers for chemical and computational entities in the QDD domain.
-- These IDs do not have semantics beyond acting as keys for provenance.
structure QDDIds where
  moleculeId      : Nat
  targetId        : Nat
  assayContextId  : Nat
  proteinTargetId : Nat
  bindingSiteId   : Nat
  ligandFamilyId  : Nat

-- Identifiers for the quantum calculation setup, such as method, basis and backend.
structure QuantumSetupIds where
  quantumMethodId : Nat
  basisSetId      : Nat
  hamiltonianId   : Nat
  ansatzId        : Nat
  optimizerId     : Nat
  backendId       : Nat

-- Identifiers for the classical (AI) model and data.
structure ClassicalSetupIds where
  classicalModelId : Nat
  datasetId        : Nat
  featureSetId     : Nat

-- Provenance information recorded for ADIC replayability.  Nonzero IDs
-- indicate the hash or identifier used for a particular data/model/job.
structure ProvenanceIds where
  datasetHash          : Nat
  modelHash            : Nat
  parameterHash        : Nat
  quantumJobId         : Nat
  backendCalibrationId : Nat
  randomSeed           : Nat
  timestampId          : Nat
  operatorId           : Nat
  approvalId           : Nat

-- Evidence produced from a quantum calculation stage.
structure QuantumEvaluationRecord (D : DPos) where
  energyEstimate     : QDDVar D
  bindingEnergyProxy : QDDVar D
  quantumErrorBound  : QDDVar D
  quantumFeatureId   : Nat
  setupIds           : QuantumSetupIds
  provenance         : ProvenanceIds

-- Evidence produced from a classical AI screening stage.
structure ClassicalScreeningRecord (D : DPos) where
  classicalInputFeatureId : Nat
  predictionScore         : QDDVar D
  modelConfidence         : QDDVar D
  predictionUncertainty   : QDDVar D
  datasetShift            : QDDVar D
  setupIds                : ClassicalSetupIds

-- Evidence produced from ADMET/toxicity evaluation.
structure ADMETRecord (D : DPos) where
  toxicityScore   : QDDVar D
  solubilityScore : QDDVar D
  stabilityScore  : QDDVar D
  admetRisk       : QDDVar D

-- Evidence of human approval, containing a boolean flag and identifiers.
structure HumanApprovalRecord (D : DPos) where
  approvalFlag : QDDVar D
  reviewerId   : Nat
  approvalId   : Nat

/-! ### Policy structures -/

-- Selection policy thresholds.  Each integer field encodes a rational threshold
-- via division by D.  For booleans we reuse `boolEnc`.
structure QDDSelectionPolicy (D : DPos) where
  maxEnergy                : Int
  minBindingEnergyProxy    : Int
  minPredictionScore       : Int
  maxToxicity              : Int
  minSolubility            : Int
  minStability             : Int
  maxAdmetRisk             : Int
  maxQuantumError          : Int
  minModelConfidence       : Int
  maxPredictionUncertainty : Int
  maxDatasetShift          : Int
  requireApproval          : Bool

-- Review policy thresholds.  These specify when a candidate should be
-- flagged for manual review rather than selected or outright rejected.
structure QDDReviewPolicy (D : DPos) where
  reviewQuantumError          : Int
  reviewMinModelConfidence    : Int
  reviewPredictionUncertainty : Int
  reviewDatasetShift          : Int
  requireApproval             : Bool

/-! ### Decision enumerations -/

-- The three possible outcomes of the candidate selection process.
inductive DecisionKind where
  | selected
  | rejected
  | needsReview
  deriving DecidableEq

-- Explicit reasons for rejecting a candidate.  Each corresponds to a violation
-- of one of the selection thresholds.
inductive RejectionReason where
  | energyTooHigh
  | bindingEnergyTooLow
  | predictionTooLow
  | toxicityTooHigh
  | solubilityTooLow
  | stabilityTooLow
  | admetRiskTooHigh
  | quantumErrorTooHigh
  | confidenceTooLow
  | uncertaintyTooHigh
  | datasetShiftTooHigh
  | approvalMissing
  | pipelineBroken
  deriving DecidableEq

-- Explicit reasons for flagging a candidate for human review.
inductive ReviewReason where
  | quantumErrorReview
  | confidenceReview
  | uncertaintyReview
  | datasetShiftReview
  | approvalPending
  | pipelineReview
  | provenanceIncomplete
  deriving DecidableEq

/-! ### Candidate decision object -/

-- All evidence and metadata for a single candidate.  The fields
-- `rejectionReason` and `reviewReason` are `none` except when
-- `kind` is `rejected` or `needsReview`.
structure CandidateSelectionDecision (D : DPos) where
  ids             : QDDIds
  quantum         : QuantumEvaluationRecord D
  classical       : ClassicalScreeningRecord D
  admet           : ADMETRecord D
  approval        : HumanApprovalRecord D
  kind            : DecisionKind
  rejectionReason : Option RejectionReason
  reviewReason    : Option ReviewReason

/-! ### Generic violation certificates -/

-- Certificate for `x - maxVal ≤ 0`.  Used for selection constraints.
def leViolationCert
    (D : DPos)
    (x : QDDVar D)
    (maxVal : Int) : IEnc D :=
  Primitives.T_sub D x.cert (constI D maxVal)

-- Certificate for `minVal - x ≤ 0`.  Used for selection constraints.
def geViolationCert
    (D : DPos)
    (minVal : Int)
    (x : QDDVar D) : IEnc D :=
  Primitives.T_sub D (constI D minVal) x.cert

-- Certificate for `maxVal - x ≤ 0`.  Used for rejection when `x` is too high.
def highViolationCert
    (D : DPos)
    (maxVal : Int)
    (x : QDDVar D) : IEnc D :=
  Primitives.T_sub D (constI D maxVal) x.cert

-- Certificate for `x - minVal ≤ 0`.  Used for rejection when `x` is too low.
def lowViolationCert
    (D : DPos)
    (x : QDDVar D)
    (minVal : Int) : IEnc D :=
  Primitives.T_sub D x.cert (constI D minVal)

-- Certificate for `requireApproval - approvalFlag ≤ 0`.  Used in selection.
def approvalViolationCert'
    (D : DPos)
    (a : HumanApprovalRecord D)
    (p : QDDSelectionPolicy D) : IEnc D :=
  Primitives.T_sub D
    (constI D (boolEnc D p.requireApproval))
    a.approvalFlag.cert

-- Certificate for `approvalFlag - requireApproval ≤ 0`.  Used in rejection/review
-- to show a missing approval.
def approvalMissingCert
    (D : DPos)
    (a : HumanApprovalRecord D)
    (requireApproval : Bool) : IEnc D :=
  Primitives.T_sub D
    a.approvalFlag.cert
    (constI D (boolEnc D requireApproval))

-- Return the pipeline linkage flag.  It encodes `D` if the quantum
-- output feeds into the classical input, and 0 otherwise.
def pipelineLinkFlag
    (D : DPos)
    (q : QuantumEvaluationRecord D)
    (c : ClassicalScreeningRecord D) : Int :=
  if q.quantumFeatureId = c.classicalInputFeatureId then ((D : Nat) : Int) else 0

-- Certificate for `requireLink - pipelineLinkFlag ≤ 0`.  Used in selection.
def pipelineLinkViolationCert
    (D : DPos)
    (d : CandidateSelectionDecision D) : IEnc D :=
  Primitives.T_sub D
    (constI D ((D : Nat) : Int))
    (constI D (pipelineLinkFlag D d.quantum d.classical))

-- Certificate for `pipelineLinkFlag - requireLink ≤ 0`.  Used in rejection/review.
def pipelineBrokenCert
    (D : DPos)
    (d : CandidateSelectionDecision D) : IEnc D :=
  Primitives.T_sub D
    (constI D (pipelineLinkFlag D d.quantum d.classical))
    (constI D ((D : Nat) : Int))

/-! ### Provenance completeness checks -/

-- Internal helper to test if a natural number is nonzero.
def checkNotZero (n : Nat) : Bool :=
  if n = 0 then false else true

-- Return `true` iff all provenance fields in the quantum record are nonzero.
def provenanceCompleteBool
    {D : DPos}
    (q : QuantumEvaluationRecord D) : Bool :=
  checkNotZero q.provenance.datasetHash &&
  checkNotZero q.provenance.modelHash &&
  checkNotZero q.provenance.parameterHash &&
  checkNotZero q.provenance.quantumJobId &&
  checkNotZero q.provenance.backendCalibrationId &&
  checkNotZero q.provenance.randomSeed &&
  checkNotZero q.provenance.timestampId &&
  checkNotZero q.provenance.operatorId &&
  checkNotZero q.provenance.approvalId

-- Return an encoded flag for provenance completeness: `D` when complete, else 0.
def provenanceCompleteFlag
    (D : DPos)
    (q : QuantumEvaluationRecord D) : Int :=
  if provenanceCompleteBool q then ((D : Nat) : Int) else 0

-- Certificate asserting completeness is required (selection).
-- It encodes `D` minus `provenanceCompleteFlag`.
def provenanceRequiredCert
    (D : DPos)
    (d : CandidateSelectionDecision D) : IEnc D :=
  Primitives.T_sub D
    (constI D ((D : Nat) : Int))
    (constI D (provenanceCompleteFlag D d.quantum))

-- Certificate asserting provenance is incomplete (review).
-- It encodes `provenanceCompleteFlag` minus `D`.
def provenanceIncompleteCert
    (D : DPos)
    (d : CandidateSelectionDecision D) : IEnc D :=
  Primitives.T_sub D
    (constI D (provenanceCompleteFlag D d.quantum))
    (constI D ((D : Nat) : Int))

/-! ### Selected-candidate specification -/

-- Build the specification rows for a selected candidate.  There are 42 rows.
-- Each triple of rows (value, threshold, difference) corresponds to a
-- selection constraint.  The final two rows check the pipeline link and
-- provenance completeness.  The root indices identify exactly the
-- violation rows (difference rows) in order.
def qddSelectionSpecRows
    (D : DPos)
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D) : List (ReplayCore.SpecRow D) :=
  [ ReplayCore.SpecRow.var d.quantum.energyEstimate.idx d.quantum.energyEstimate.cert
  , ReplayCore.SpecRow.const p.maxEnergy
  , ReplayCore.SpecRow.sub 0 1
      (leViolationCert D d.quantum.energyEstimate p.maxEnergy)

  , ReplayCore.SpecRow.var d.quantum.bindingEnergyProxy.idx d.quantum.bindingEnergyProxy.cert
  , ReplayCore.SpecRow.const p.minBindingEnergyProxy
  , ReplayCore.SpecRow.sub 4 3
      (geViolationCert D p.minBindingEnergyProxy d.quantum.bindingEnergyProxy)

  , ReplayCore.SpecRow.var d.classical.predictionScore.idx d.classical.predictionScore.cert
  , ReplayCore.SpecRow.const p.minPredictionScore
  , ReplayCore.SpecRow.sub 7 6
      (geViolationCert D p.minPredictionScore d.classical.predictionScore)

  , ReplayCore.SpecRow.var d.admet.toxicityScore.idx d.admet.toxicityScore.cert
  , ReplayCore.SpecRow.const p.maxToxicity
  , ReplayCore.SpecRow.sub 9 10
      (leViolationCert D d.admet.toxicityScore p.maxToxicity)

  , ReplayCore.SpecRow.var d.admet.solubilityScore.idx d.admet.solubilityScore.cert
  , ReplayCore.SpecRow.const p.minSolubility
  , ReplayCore.SpecRow.sub 13 12
      (geViolationCert D p.minSolubility d.admet.solubilityScore)

  , ReplayCore.SpecRow.var d.admet.stabilityScore.idx d.admet.stabilityScore.cert
  , ReplayCore.SpecRow.const p.minStability
  , ReplayCore.SpecRow.sub 16 15
      (geViolationCert D p.minStability d.admet.stabilityScore)

  , ReplayCore.SpecRow.var d.admet.admetRisk.idx d.admet.admetRisk.cert
  , ReplayCore.SpecRow.const p.maxAdmetRisk
  , ReplayCore.SpecRow.sub 18 19
      (leViolationCert D d.admet.admetRisk p.maxAdmetRisk)

  , ReplayCore.SpecRow.var d.quantum.quantumErrorBound.idx d.quantum.quantumErrorBound.cert
  , ReplayCore.SpecRow.const p.maxQuantumError
  , ReplayCore.SpecRow.sub 21 22
      (leViolationCert D d.quantum.quantumErrorBound p.maxQuantumError)

  , ReplayCore.SpecRow.var d.classical.modelConfidence.idx d.classical.modelConfidence.cert
  , ReplayCore.SpecRow.const p.minModelConfidence
  , ReplayCore.SpecRow.sub 25 24
      (geViolationCert D p.minModelConfidence d.classical.modelConfidence)

  , ReplayCore.SpecRow.var d.classical.predictionUncertainty.idx d.classical.predictionUncertainty.cert
  , ReplayCore.SpecRow.const p.maxPredictionUncertainty
  , ReplayCore.SpecRow.sub 27 28
      (leViolationCert D d.classical.predictionUncertainty p.maxPredictionUncertainty)

  , ReplayCore.SpecRow.var d.classical.datasetShift.idx d.classical.datasetShift.cert
  , ReplayCore.SpecRow.const p.maxDatasetShift
  , ReplayCore.SpecRow.sub 30 31
      (leViolationCert D d.classical.datasetShift p.maxDatasetShift)

  , ReplayCore.SpecRow.var d.approval.approvalFlag.idx d.approval.approvalFlag.cert
  , ReplayCore.SpecRow.const (boolEnc D p.requireApproval)
  , ReplayCore.SpecRow.sub 34 33
      (approvalViolationCert' D d.approval p)

  , ReplayCore.SpecRow.const (pipelineLinkFlag D d.quantum d.classical)
  , ReplayCore.SpecRow.const ((D : Nat) : Int)
  , ReplayCore.SpecRow.sub 37 36
      (pipelineLinkViolationCert D d)

  , ReplayCore.SpecRow.const (provenanceCompleteFlag D d.quantum)
  , ReplayCore.SpecRow.const ((D : Nat) : Int)
  , ReplayCore.SpecRow.sub 40 39
      (provenanceRequiredCert D d)
  ]

-- List of root indices for the selected-candidate specification.
def qddSelectedRoots : List Nat :=
  [2, 5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 38, 41]

/-! ### Rejected-candidate specification -/

-- Build the specification rows for a rejected candidate.  Each triple of
-- rows corresponds to a rejection criterion (value, threshold, difference),
-- with the difference computed in the opposite direction to certify that the
-- criterion is violated.  We reuse the selection thresholds from the
-- selection policy.  The final rows check approval missing and pipeline broken.
def qddRejectionSpecRows
    (D : DPos)
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D) : List (ReplayCore.SpecRow D) :=
  [ ReplayCore.SpecRow.const p.maxEnergy
  , ReplayCore.SpecRow.var d.quantum.energyEstimate.idx d.quantum.energyEstimate.cert
  , ReplayCore.SpecRow.sub 0 1
      (highViolationCert D p.maxEnergy d.quantum.energyEstimate)

  , ReplayCore.SpecRow.var d.quantum.bindingEnergyProxy.idx d.quantum.bindingEnergyProxy.cert
  , ReplayCore.SpecRow.const p.minBindingEnergyProxy
  , ReplayCore.SpecRow.sub 3 4
      (lowViolationCert D d.quantum.bindingEnergyProxy p.minBindingEnergyProxy)

  , ReplayCore.SpecRow.var d.classical.predictionScore.idx d.classical.predictionScore.cert
  , ReplayCore.SpecRow.const p.minPredictionScore
  , ReplayCore.SpecRow.sub 6 7
      (lowViolationCert D d.classical.predictionScore p.minPredictionScore)

  , ReplayCore.SpecRow.const p.maxToxicity
  , ReplayCore.SpecRow.var d.admet.toxicityScore.idx d.admet.toxicityScore.cert
  , ReplayCore.SpecRow.sub 9 10
      (highViolationCert D p.maxToxicity d.admet.toxicityScore)

  , ReplayCore.SpecRow.var d.admet.solubilityScore.idx d.admet.solubilityScore.cert
  , ReplayCore.SpecRow.const p.minSolubility
  , ReplayCore.SpecRow.sub 12 13
      (lowViolationCert D d.admet.solubilityScore p.minSolubility)

  , ReplayCore.SpecRow.var d.admet.stabilityScore.idx d.admet.stabilityScore.cert
  , ReplayCore.SpecRow.const p.minStability
  , ReplayCore.SpecRow.sub 15 16
      (lowViolationCert D d.admet.stabilityScore p.minStability)

  , ReplayCore.SpecRow.const p.maxAdmetRisk
  , ReplayCore.SpecRow.var d.admet.admetRisk.idx d.admet.admetRisk.cert
  , ReplayCore.SpecRow.sub 18 19
      (highViolationCert D p.maxAdmetRisk d.admet.admetRisk)

  , ReplayCore.SpecRow.const p.maxQuantumError
  , ReplayCore.SpecRow.var d.quantum.quantumErrorBound.idx d.quantum.quantumErrorBound.cert
  , ReplayCore.SpecRow.sub 21 22
      (highViolationCert D p.maxQuantumError d.quantum.quantumErrorBound)

  , ReplayCore.SpecRow.var d.classical.modelConfidence.idx d.classical.modelConfidence.cert
  , ReplayCore.SpecRow.const p.minModelConfidence
  , ReplayCore.SpecRow.sub 24 25
      (lowViolationCert D d.classical.modelConfidence p.minModelConfidence)

  , ReplayCore.SpecRow.const p.maxPredictionUncertainty
  , ReplayCore.SpecRow.var d.classical.predictionUncertainty.idx d.classical.predictionUncertainty.cert
  , ReplayCore.SpecRow.sub 27 28
      (highViolationCert D p.maxPredictionUncertainty d.classical.predictionUncertainty)

  , ReplayCore.SpecRow.const p.maxDatasetShift
  , ReplayCore.SpecRow.var d.classical.datasetShift.idx d.classical.datasetShift.cert
  , ReplayCore.SpecRow.sub 30 31
      (highViolationCert D p.maxDatasetShift d.classical.datasetShift)

  , ReplayCore.SpecRow.var d.approval.approvalFlag.idx d.approval.approvalFlag.cert
  , ReplayCore.SpecRow.const (boolEnc D p.requireApproval)
  , ReplayCore.SpecRow.sub 33 34
      (approvalMissingCert D d.approval p.requireApproval)

  , ReplayCore.SpecRow.const (pipelineLinkFlag D d.quantum d.classical)
  , ReplayCore.SpecRow.const ((D : Nat) : Int)
  , ReplayCore.SpecRow.sub 36 37
      (pipelineBrokenCert D d)
  ]

-- Map each rejection reason to its corresponding root index.
def qddRejectionRoot : RejectionReason → Nat
  | RejectionReason.energyTooHigh        => 2
  | RejectionReason.bindingEnergyTooLow  => 5
  | RejectionReason.predictionTooLow     => 8
  | RejectionReason.toxicityTooHigh      => 11
  | RejectionReason.solubilityTooLow     => 14
  | RejectionReason.stabilityTooLow      => 17
  | RejectionReason.admetRiskTooHigh     => 20
  | RejectionReason.quantumErrorTooHigh  => 23
  | RejectionReason.confidenceTooLow     => 26
  | RejectionReason.uncertaintyTooHigh   => 29
  | RejectionReason.datasetShiftTooHigh  => 32
  | RejectionReason.approvalMissing      => 35
  | RejectionReason.pipelineBroken       => 38

-- Produce the list of rejection roots from an optional reason.
def qddRejectionRoots
    (r : Option RejectionReason) : List Nat :=
  match r with
  | some rr => [qddRejectionRoot rr]
  | none    => []

/-! ### Review-candidate specification -/

-- Build the specification rows for a review candidate.  Each triple of rows
-- corresponds to a review criterion based on the review policy.  The final
-- rows test approval pending, pipeline issues and provenance completeness.
def qddReviewSpecRows
    (D : DPos)
    (d : CandidateSelectionDecision D)
    (rp : QDDReviewPolicy D) : List (ReplayCore.SpecRow D) :=
  [ ReplayCore.SpecRow.const rp.reviewQuantumError
  , ReplayCore.SpecRow.var d.quantum.quantumErrorBound.idx d.quantum.quantumErrorBound.cert
  , ReplayCore.SpecRow.sub 0 1
      (highViolationCert D rp.reviewQuantumError d.quantum.quantumErrorBound)

  , ReplayCore.SpecRow.var d.classical.modelConfidence.idx d.classical.modelConfidence.cert
  , ReplayCore.SpecRow.const rp.reviewMinModelConfidence
  , ReplayCore.SpecRow.sub 3 4
      (lowViolationCert D d.classical.modelConfidence rp.reviewMinModelConfidence)

  , ReplayCore.SpecRow.const rp.reviewPredictionUncertainty
  , ReplayCore.SpecRow.var d.classical.predictionUncertainty.idx d.classical.predictionUncertainty.cert
  , ReplayCore.SpecRow.sub 6 7
      (highViolationCert D rp.reviewPredictionUncertainty d.classical.predictionUncertainty)

  , ReplayCore.SpecRow.const rp.reviewDatasetShift
  , ReplayCore.SpecRow.var d.classical.datasetShift.idx d.classical.datasetShift.cert
  , ReplayCore.SpecRow.sub 9 10
      (highViolationCert D rp.reviewDatasetShift d.classical.datasetShift)

  , ReplayCore.SpecRow.var d.approval.approvalFlag.idx d.approval.approvalFlag.cert
  , ReplayCore.SpecRow.const (boolEnc D rp.requireApproval)
  , ReplayCore.SpecRow.sub 12 13
      (approvalMissingCert D d.approval rp.requireApproval)

  , ReplayCore.SpecRow.const (pipelineLinkFlag D d.quantum d.classical)
  , ReplayCore.SpecRow.const ((D : Nat) : Int)
  , ReplayCore.SpecRow.sub 15 16
      (pipelineBrokenCert D d)

  , ReplayCore.SpecRow.const (provenanceCompleteFlag D d.quantum)
  , ReplayCore.SpecRow.const ((D : Nat) : Int)
  , ReplayCore.SpecRow.sub 18 19
      (provenanceIncompleteCert D d)
  ]

-- Map each review reason to its corresponding root index.
def qddReviewRoot : ReviewReason → Nat
  | ReviewReason.quantumErrorReview   => 2
  | ReviewReason.confidenceReview     => 5
  | ReviewReason.uncertaintyReview    => 8
  | ReviewReason.datasetShiftReview   => 11
  | ReviewReason.approvalPending      => 14
  | ReviewReason.pipelineReview       => 17
  | ReviewReason.provenanceIncomplete => 20

-- Produce the list of review roots from an optional reason.
def qddReviewRoots
    (r : Option ReviewReason) : List Nat :=
  match r with
  | some rr => [qddReviewRoot rr]
  | none    => []

/-! ### Validity predicates -/

-- Domain-level validity predicate for selected candidates.
def QDDSelectedReplayValid
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D) : Prop :=
  d.kind = DecisionKind.selected ∧
  ReplayCore.SemanticValid D rows
    (qddSelectionSpecRows D d p)
    qddSelectedRoots

-- Domain-level validity predicate for rejected candidates.
def QDDRejectedReplayValid
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D) : Prop :=
  d.kind = DecisionKind.rejected ∧
  d.rejectionReason.isSome ∧
  ReplayCore.SemanticValid D rows
    (qddRejectionSpecRows D d p)
    (qddRejectionRoots d.rejectionReason)

-- Domain-level validity predicate for review candidates.
def QDDNeedsReviewReplayValid
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (rp : QDDReviewPolicy D) : Prop :=
  d.kind = DecisionKind.needsReview ∧
  d.reviewReason.isSome ∧
  ReplayCore.SemanticValid D rows
    (qddReviewSpecRows D d rp)
    (qddReviewRoots d.reviewReason)

-- Overall declared validity: selection, rejection or review must hold.
def QDDDeclaredDecisionValid
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) : Prop :=
  QDDSelectedReplayValid D rows d p ∨
  QDDRejectedReplayValid D rows d p ∨
  QDDNeedsReviewReplayValid D rows d rp

/-! ### Certificates -/

-- Certificate for selected candidates.
def qddSelectedCert
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D) : ReplayCore.Cert D :=
  { rows := rows
    specRows := qddSelectionSpecRows D d p
    roots := qddSelectedRoots }

-- Certificate for rejected candidates.
def qddRejectedCert
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D) : ReplayCore.Cert D :=
  { rows := rows
    specRows := qddRejectionSpecRows D d p
    roots := qddRejectionRoots d.rejectionReason }

-- Certificate for needs-review candidates.
def qddNeedsReviewCert
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (rp : QDDReviewPolicy D) : ReplayCore.Cert D :=
  { rows := rows
    specRows := qddReviewSpecRows D d rp
    roots := qddReviewRoots d.reviewReason }

/-! ### Well-formedness -/

-- The candidate decision is well-formed if reasons are provided when
-- required.  For selected candidates we do not require that the optional
-- reason fields are none, since they are ignored.
def QDDDecisionWellFormed
    {D : DPos}
    (d : CandidateSelectionDecision D) : Prop :=
  match d.kind with
  | DecisionKind.selected     => True
  | DecisionKind.rejected     => d.rejectionReason.isSome
  | DecisionKind.needsReview  => d.reviewReason.isSome

/-! ### Kind-specific soundness theorems -/

-- Soundness for selected candidates: verifier acceptance implies semantic validity.
theorem qdd_selected_replay_sound
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D) :
    d.kind = DecisionKind.selected →
    ReplayCore.verifierBool D (qddSelectedCert D rows d p) = true →
    QDDSelectedReplayValid D rows d p := by
  intro hKind hAccept
  exact ⟨hKind,
    ReplayCore.verifierBool_sound D (qddSelectedCert D rows d p) hAccept⟩

-- Soundness for rejected candidates.
theorem qdd_rejected_replay_sound
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D) :
    d.kind = DecisionKind.rejected →
    d.rejectionReason.isSome →
    ReplayCore.verifierBool D (qddRejectedCert D rows d p) = true →
    QDDRejectedReplayValid D rows d p := by
  intro hKind hReason hAccept
  exact ⟨hKind, hReason,
    ReplayCore.verifierBool_sound D (qddRejectedCert D rows d p) hAccept⟩

-- Soundness for needs-review candidates.
theorem qdd_needsReview_replay_sound
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (rp : QDDReviewPolicy D) :
    d.kind = DecisionKind.needsReview →
    d.reviewReason.isSome →
    ReplayCore.verifierBool D (qddNeedsReviewCert D rows d rp) = true →
    QDDNeedsReviewReplayValid D rows d rp := by
  intro hKind hReason hAccept
  exact ⟨hKind, hReason,
    ReplayCore.verifierBool_sound D (qddNeedsReviewCert D rows d rp) hAccept⟩

/-! ### Unified certificates and soundness -/

-- Kind-dependent specification rows.
def qddDecisionSpecRows
    (D : DPos)
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) : List (ReplayCore.SpecRow D) :=
  match d.kind with
  | DecisionKind.selected    => qddSelectionSpecRows D d p
  | DecisionKind.rejected    => qddRejectionSpecRows D d p
  | DecisionKind.needsReview => qddReviewSpecRows D d rp

-- Kind-dependent root list.
def qddDecisionRoots
    {D : DPos}
    (d : CandidateSelectionDecision D) : List Nat :=
  match d.kind with
  | DecisionKind.selected    => qddSelectedRoots
  | DecisionKind.rejected    => qddRejectionRoots d.rejectionReason
  | DecisionKind.needsReview => qddReviewRoots d.reviewReason

-- Unified certificate for any decision.
def qddDecisionCert
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) : ReplayCore.Cert D :=
  { rows := rows
    specRows := qddDecisionSpecRows D d p rp
    roots := qddDecisionRoots d }

-- Unified replay-valid predicate.
def QDDDecisionReplayValid
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) : Prop :=
  ReplayCore.SemanticValid D rows
    (qddDecisionSpecRows D d p rp)
    (qddDecisionRoots d)

-- Unified soundness: verifier acceptance implies replay validity.
theorem qdd_decision_replay_sound
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    ReplayCore.verifierBool D (qddDecisionCert D rows d p rp) = true →
    QDDDecisionReplayValid D rows d p rp := by
  intro hAccept
  exact ReplayCore.verifierBool_sound D (qddDecisionCert D rows d p rp) hAccept

/-! ### Declared decision validity theorems -/

-- Soundness for declared selected candidates via the unified certificate.
theorem qdd_declared_selected_valid_of_replay
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    d.kind = DecisionKind.selected →
    ReplayCore.verifierBool D (qddDecisionCert D rows d p rp) = true →
    QDDDeclaredDecisionValid D rows d p rp := by
  intro hKind hAccept
  have hReplay : QDDDecisionReplayValid D rows d p rp :=
    qdd_decision_replay_sound D rows d p rp hAccept
  have hSpec : ReplayCore.SemanticValid D rows (qddSelectionSpecRows D d p) qddSelectedRoots := by
    simpa [QDDDecisionReplayValid, qddDecisionSpecRows, qddDecisionRoots, hKind] using hReplay
  have hSel : QDDSelectedReplayValid D rows d p := ⟨hKind, hSpec⟩
  exact Or.inl hSel

-- Soundness for declared rejected candidates via the unified certificate.
theorem qdd_declared_rejected_valid_of_replay
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    d.kind = DecisionKind.rejected →
    d.rejectionReason.isSome →
    ReplayCore.verifierBool D (qddDecisionCert D rows d p rp) = true →
    QDDDeclaredDecisionValid D rows d p rp := by
  intro hKind hReason hAccept
  have hReplay : QDDDecisionReplayValid D rows d p rp :=
    qdd_decision_replay_sound D rows d p rp hAccept
  have hSpec : ReplayCore.SemanticValid D rows
    (qddRejectionSpecRows D d p)
    (qddRejectionRoots d.rejectionReason) := by
    simpa [QDDDecisionReplayValid, qddDecisionSpecRows, qddDecisionRoots, hKind] using hReplay
  have hRej : QDDRejectedReplayValid D rows d p := ⟨hKind, hReason, hSpec⟩
  exact Or.inr (Or.inl hRej)

-- Soundness for declared review candidates via the unified certificate.
theorem qdd_declared_needsReview_valid_of_replay
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    d.kind = DecisionKind.needsReview →
    d.reviewReason.isSome →
    ReplayCore.verifierBool D (qddDecisionCert D rows d p rp) = true →
    QDDDeclaredDecisionValid D rows d p rp := by
  intro hKind hReason hAccept
  have hReplay : QDDDecisionReplayValid D rows d p rp :=
    qdd_decision_replay_sound D rows d p rp hAccept
  have hSpec : ReplayCore.SemanticValid D rows
    (qddReviewSpecRows D d rp)
    (qddReviewRoots d.reviewReason) := by
    simpa [QDDDecisionReplayValid, qddDecisionSpecRows, qddDecisionRoots, hKind] using hReplay
  have hRev : QDDNeedsReviewReplayValid D rows d rp := ⟨hKind, hReason, hSpec⟩
  exact Or.inr (Or.inr hRev)

-- Soundness for any declared decision given well-formedness.
theorem qdd_declared_decision_valid_of_replay
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    QDDDecisionWellFormed d →
    ReplayCore.verifierBool D (qddDecisionCert D rows d p rp) = true →
    QDDDeclaredDecisionValid D rows d p rp := by
  intro hWF hAccept
  cases hKind : d.kind with
  | selected =>
      exact qdd_declared_selected_valid_of_replay D rows d p rp hKind hAccept
  | rejected =>
      have hReason : d.rejectionReason.isSome := by
        simpa [QDDDecisionWellFormed, hKind] using hWF
      exact qdd_declared_rejected_valid_of_replay D rows d p rp hKind hReason hAccept
  | needsReview =>
      have hReason : d.reviewReason.isSome := by
        simpa [QDDDecisionWellFormed, hKind] using hWF
      exact qdd_declared_needsReview_valid_of_replay D rows d p rp hKind hReason hAccept

-- Product-verifier versions of the soundness theorems. These theorems state that
-- if a product verifier (matching the Lean verifier) accepts the certificate then
-- the corresponding replay-valid predicate holds.

-- Soundness for selected candidates under a product verifier.
theorem qdd_selected_productVerifier_sound
    (D : DPos)
    (checker : ReplayCore.Cert D → Bool)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D) :
    d.kind = DecisionKind.selected →
    ReplayCore.ProductVerifierMatches D checker →
    checker (qddSelectedCert D rows d p) = true →
    QDDSelectedReplayValid D rows d p := by
  intro hKind hMatch hAccept
  exact ⟨hKind,
    ReplayCore.productVerifier_sound D checker (qddSelectedCert D rows d p) hMatch hAccept⟩

-- Soundness for rejected candidates under a product verifier.
theorem qdd_rejected_productVerifier_sound
    (D : DPos)
    (checker : ReplayCore.Cert D → Bool)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D) :
    d.kind = DecisionKind.rejected →
    d.rejectionReason.isSome →
    ReplayCore.ProductVerifierMatches D checker →
    checker (qddRejectedCert D rows d p) = true →
    QDDRejectedReplayValid D rows d p := by
  intro hKind hReason hMatch hAccept
  exact ⟨hKind, hReason,
    ReplayCore.productVerifier_sound D checker (qddRejectedCert D rows d p) hMatch hAccept⟩

-- Soundness for needs-review candidates under a product verifier.
theorem qdd_needsReview_productVerifier_sound
    (D : DPos)
    (checker : ReplayCore.Cert D → Bool)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (rp : QDDReviewPolicy D) :
    d.kind = DecisionKind.needsReview →
    d.reviewReason.isSome →
    ReplayCore.ProductVerifierMatches D checker →
    checker (qddNeedsReviewCert D rows d rp) = true →
    QDDNeedsReviewReplayValid D rows d rp := by
  intro hKind hReason hMatch hAccept
  exact ⟨hKind, hReason,
    ReplayCore.productVerifier_sound D checker (qddNeedsReviewCert D rows d rp) hMatch hAccept⟩

-- Unified product-verifier soundness theorem: acceptance implies replay validity.
theorem qdd_decision_productVerifier_sound
    (D : DPos)
    (checker : ReplayCore.Cert D → Bool)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    ReplayCore.ProductVerifierMatches D checker →
    checker (qddDecisionCert D rows d p rp) = true →
    QDDDecisionReplayValid D rows d p rp := by
  intro hMatch hAccept
  exact ReplayCore.productVerifier_sound D checker (qddDecisionCert D rows d p rp) hMatch hAccept

-- Product-verifier versions of the declared decision validity theorems.

-- Declared selection validity under a product verifier.
theorem qdd_declared_selected_valid_of_productVerifier
    (D : DPos)
    (checker : ReplayCore.Cert D → Bool)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    d.kind = DecisionKind.selected →
    ReplayCore.ProductVerifierMatches D checker →
    checker (qddDecisionCert D rows d p rp) = true →
    QDDDeclaredDecisionValid D rows d p rp := by
  intro hKind hMatch hAccept
  have hReplay : QDDDecisionReplayValid D rows d p rp :=
    qdd_decision_productVerifier_sound D checker rows d p rp hMatch hAccept
  have hSpec : ReplayCore.SemanticValid D rows (qddSelectionSpecRows D d p) qddSelectedRoots := by
    simpa [QDDDecisionReplayValid, qddDecisionSpecRows, qddDecisionRoots, hKind]
      using hReplay
  have hSel : QDDSelectedReplayValid D rows d p := ⟨hKind, hSpec⟩
  exact Or.inl hSel

-- Declared rejection validity under a product verifier.
theorem qdd_declared_rejected_valid_of_productVerifier
    (D : DPos)
    (checker : ReplayCore.Cert D → Bool)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    d.kind = DecisionKind.rejected →
    d.rejectionReason.isSome →
    ReplayCore.ProductVerifierMatches D checker →
    checker (qddDecisionCert D rows d p rp) = true →
    QDDDeclaredDecisionValid D rows d p rp := by
  intro hKind hReason hMatch hAccept
  have hReplay : QDDDecisionReplayValid D rows d p rp :=
    qdd_decision_productVerifier_sound D checker rows d p rp hMatch hAccept
  have hSpec : ReplayCore.SemanticValid D rows
    (qddRejectionSpecRows D d p)
    (qddRejectionRoots d.rejectionReason) := by
    simpa [QDDDecisionReplayValid, qddDecisionSpecRows, qddDecisionRoots, hKind]
      using hReplay
  have hRej : QDDRejectedReplayValid D rows d p := ⟨hKind, hReason, hSpec⟩
  exact Or.inr (Or.inl hRej)

-- Declared review validity under a product verifier.
theorem qdd_declared_needsReview_valid_of_productVerifier
    (D : DPos)
    (checker : ReplayCore.Cert D → Bool)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    d.kind = DecisionKind.needsReview →
    d.reviewReason.isSome →
    ReplayCore.ProductVerifierMatches D checker →
    checker (qddDecisionCert D rows d p rp) = true →
    QDDDeclaredDecisionValid D rows d p rp := by
  intro hKind hReason hMatch hAccept
  have hReplay : QDDDecisionReplayValid D rows d p rp :=
    qdd_decision_productVerifier_sound D checker rows d p rp hMatch hAccept
  have hSpec : ReplayCore.SemanticValid D rows
    (qddReviewSpecRows D d rp)
    (qddReviewRoots d.reviewReason) := by
    simpa [QDDDecisionReplayValid, qddDecisionSpecRows, qddDecisionRoots, hKind]
      using hReplay
  have hRev : QDDNeedsReviewReplayValid D rows d rp := ⟨hKind, hReason, hSpec⟩
  exact Or.inr (Or.inr hRev)

-- Unified declared decision validity under a product verifier.
theorem qdd_declared_decision_valid_of_productVerifier
    (D : DPos)
    (checker : ReplayCore.Cert D → Bool)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    QDDDecisionWellFormed d →
    ReplayCore.ProductVerifierMatches D checker →
    checker (qddDecisionCert D rows d p rp) = true →
    QDDDeclaredDecisionValid D rows d p rp := by
  intro hWF hMatch hAccept
  cases hKind : d.kind with
  | selected =>
      have h : d.kind = DecisionKind.selected := hKind
      exact qdd_declared_selected_valid_of_productVerifier
        D checker rows d p rp h hMatch hAccept
  | rejected =>
      have h : d.kind = DecisionKind.rejected := hKind
      have hReason : d.rejectionReason.isSome := by
        simpa [QDDDecisionWellFormed, hKind] using hWF
      exact qdd_declared_rejected_valid_of_productVerifier
        D checker rows d p rp h hReason hMatch hAccept
  | needsReview =>
      have h : d.kind = DecisionKind.needsReview := hKind
      have hReason : d.reviewReason.isSome := by
        simpa [QDDDecisionWellFormed, hKind] using hWF
      exact qdd_declared_needsReview_valid_of_productVerifier
        D checker rows d p rp h hReason hMatch hAccept

/-! ### Boundary and claim -/

-- Opaque definition for therapeutic efficacy boundary.  We do not claim
-- any therapeutic effectiveness; the artifact only attests to replayable
-- evidence for candidate selection decisions.
opaque TherapeuticEffective
    (D : DPos)
    (d : CandidateSelectionDecision D) : Prop

-- Predicate summarizing what this artifact proves: replay-verifiable
-- candidate-selection validity.  It does not assert efficacy or safety.
def ReplayVerifiableCandidateSelection
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecision D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) : Prop :=
  QDDDeclaredDecisionValid D rows d p rp

end QuantumDrugDiscovery

end

end ADIC

/-!
## Extended QDD domain: experimental definitions

This section extends the existing quantum drug discovery replay domain with
additional structures and definitions proposed during our discussion.  These
additions do not replace the existing definitions above.  Instead, they live
in a separate namespace so that downstream developments can experiment with
more expressive domain models without disturbing the original interface.

The goal of this extension is to support multiple rejection and review reasons,
record richer provenance information (including evidence bindings), and build
specifications in a compositional way that avoids hard-coded root indices.
These definitions are *partial* and some proofs remain `sorry` or placeholders.
-/

namespace ADIC
namespace QuantumDrugDiscovery

open ReplayCore

/--
Identifiers linking evidence across multiple stages of the QDD pipeline.
Each field should be nonzero when present.  The `candidateEvidenceId` links
back to the candidate, while the other fields connect quantum, classical,
ADMET and approval evidence.  The link identifiers express data flow across
stages (quantum features feeding classical models, and candidate decisions
being approved).
-/
structure EvidenceBindingIds where
  candidateEvidenceId      : Nat
  quantumEvidenceId        : Nat
  classicalEvidenceId      : Nat
  admetEvidenceId          : Nat
  approvalEvidenceId       : Nat
  quantumToClassicalLinkId : Nat
  candidateToApprovalId    : Nat

/--
Augmented provenance information which records the usual hashes along with a
binding record that ties together the various pieces of evidence for a single
candidate.  A zero value in any field indicates missing data.
-/
structure BoundProvenanceIds extends ProvenanceIds where
  binding : EvidenceBindingIds

/--
Return `true` iff all binding identifiers in a record are nonzero.  This is a
boolean predicate used as part of the extended provenance completeness check.
-/
def evidenceBindingCompleteBool (b : EvidenceBindingIds) : Bool :=
  checkNotZero b.candidateEvidenceId &&
  checkNotZero b.quantumEvidenceId &&
  checkNotZero b.classicalEvidenceId &&
  checkNotZero b.admetEvidenceId &&
  checkNotZero b.approvalEvidenceId &&
  checkNotZero b.quantumToClassicalLinkId &&
  checkNotZero b.candidateToApprovalId

/--
Return `true` iff all fields of an extended provenance record are nonzero and
its binding identifiers are complete.  This predicate is intended to be used
as a replay root in the extended specification layer.
-/
def boundProvenanceCompleteBool (p : BoundProvenanceIds) : Bool :=
  checkNotZero p.datasetHash &&
  checkNotZero p.modelHash &&
  checkNotZero p.parameterHash &&
  checkNotZero p.quantumJobId &&
  checkNotZero p.backendCalibrationId &&
  checkNotZero p.randomSeed &&
  checkNotZero p.timestampId &&
  checkNotZero p.operatorId &&
  checkNotZero p.approvalId &&
  evidenceBindingCompleteBool p.binding

/--
A quantum evaluation record enriched with bound provenance.  This version
coincides with the original `QuantumEvaluationRecord` except for the
provenance type.  It is defined separately so that users can gradually
migrate without breaking existing code.
-/
structure QuantumEvaluationRecordV2 (D : DPos) where
  energyEstimate     : QDDVar D
  bindingEnergyProxy : QDDVar D
  quantumErrorBound  : QDDVar D
  quantumFeatureId   : Nat
  setupIds           : QuantumSetupIds
  provenance         : BoundProvenanceIds

/--
Check whether a quantum setup is fully declared.  This predicate returns
`true` exactly when all components of the setup record and the associated
backend calibration ID are nonzero.  It is used to certify that the user
has recorded sufficient information about the quantum calculation setup.
-/
def quantumSetupConsistentBool
    (s : QuantumSetupIds)
    (p : ProvenanceIds) : Bool :=
  checkNotZero s.quantumMethodId &&
  checkNotZero s.basisSetId &&
  checkNotZero s.hamiltonianId &&
  checkNotZero s.ansatzId &&
  checkNotZero s.optimizerId &&
  checkNotZero s.backendId &&
  checkNotZero p.backendCalibrationId

/--
A simple wrapper around the boolean encoding used by the underlying replay
engine.  This helper returns the encoded integer associated with a boolean
in the fixed-point scale `D`.
-/
def boolFlag (D : DPos) (b : Bool) : Int :=
  boolEnc D b

/--
Certificate asserting that a boolean condition must be true.  It encodes
the difference `(D - flag)` which is ≤ 0 exactly when `flag = D` (i.e. the
condition is satisfied).  The resulting interval is used in replay rows.
-/
def requireTrueCert
    (D : DPos)
    (b : Bool) : IEnc D :=
  Primitives.T_sub D
    (constI D ((D : Nat) : Int))
    (constI D (boolFlag D b))

/--
A replay clause is a small specification consisting of a list of local rows
and a single root index.  Each clause expresses exactly one inequality or
boolean condition.  Clauses can be concatenated into blocks; the root index
of each clause is relative to the local rows.
-/
structure QDDClause (D : DPos) where
  rows : List (ReplayCore.SpecRow D)
  root : Nat
  nonempty : rows ≠ []

/--
Build a replay clause asserting that a boolean condition holds.  The clause
consists of three rows (two constants and their difference) and a single root
index.  This construction allows boolean completeness checks to be composed
into larger specifications without manually tracking root offsets.
-/
def requireTrueClause
    (D : DPos)
    (b : Bool) : QDDClause D :=
  { rows :=
      [ ReplayCore.SpecRow.const ((D : Nat) : Int)
      , ReplayCore.SpecRow.const (boolFlag D b)
      , ReplayCore.SpecRow.sub 0 1
          (requireTrueCert D b)
      ]
    root := 2
    nonempty := by simp }

/--
A block of specification rows.  A block can be formed by concatenating many
clauses.  When concatenating blocks, root indices of the latter are shifted
by the length of the former.  This function is used by a left-fold
to build larger specifications from small clauses.
-/
structure QDDSpecBlock (D : DPos) where
  rows  : List (ReplayCore.SpecRow D)
  roots : List Nat

/-- Shift a single root by `k` positions. -/
def shiftRoot (k : Nat) (r : Nat) : Nat := r + k

/-- Shift all root indices in a list by `k`. -/
def shiftRoots (k : Nat) (rs : List Nat) : List Nat :=
  rs.map (fun r => shiftRoot k r)

/--
Concatenate two specification blocks.  The rows of the second block are
appended to those of the first, and the roots of the second are shifted by
the length of the first block's rows.  This function is used by a left-fold
to build larger specifications from small clauses.
-/
def appendBlock
    {D : DPos}
    (a b : QDDSpecBlock D) : QDDSpecBlock D :=
  { rows  := a.rows ++ b.rows
    roots := a.roots ++ shiftRoots a.rows.length b.roots }

/-- Create a block from a single clause. -/
def blockOfClause
    {D : DPos}
    (c : QDDClause D) : QDDSpecBlock D :=
  { rows := c.rows, roots := [c.root] }

/--
Concatenate a list of specification blocks.  This helper applies `appendBlock`
repeatedly, starting from the empty block.  It can be used to build complex
specifications without manually assigning root numbers.
-/
def concatBlocks
    {D : DPos}
    (bs : List (QDDSpecBlock D)) : QDDSpecBlock D :=
  bs.foldl appendBlock { rows := [], roots := [] }

/--
Construct a clause certifying that a variable does not exceed a given maximum.
The resulting clause has three rows: the variable, the constant threshold and
their difference (variable - max ≤ 0).  The root index points to the
difference row.
-/
def leClause
    (D : DPos)
    (x : QDDVar D)
    (maxVal : Int) : QDDClause D :=
  { rows :=
      [ ReplayCore.SpecRow.var x.idx x.cert
      , ReplayCore.SpecRow.const maxVal
      , ReplayCore.SpecRow.sub 0 1
          (leViolationCert D x maxVal)
      ]
    root := 2
    nonempty := by simp }

/--
Construct a clause certifying that a variable is at least a minimum value.
The rows compute (min - variable ≤ 0).  The root index references the
difference row.
-/
def geClause
    (D : DPos)
    (minVal : Int)
    (x : QDDVar D) : QDDClause D :=
  { rows :=
      [ ReplayCore.SpecRow.var x.idx x.cert
      , ReplayCore.SpecRow.const minVal
      , ReplayCore.SpecRow.sub 1 0
          (geViolationCert D minVal x)
      ]
    root := 2
    nonempty := by simp }

/--
Construct a clause certifying that a variable is strictly above a given
maximum.  The rows compute (max - variable ≤ 0).  This is used for rejection
criteria when a quantity is too large.
-/
def highRejectClause
    (D : DPos)
    (maxVal : Int)
    (x : QDDVar D) : QDDClause D :=
  { rows :=
      [ ReplayCore.SpecRow.const maxVal
      , ReplayCore.SpecRow.var x.idx x.cert
      , ReplayCore.SpecRow.sub 0 1
          (highViolationCert D maxVal x)
      ]
    root := 2
    nonempty := by simp }

/--
Construct a clause certifying that a variable is strictly below a given
minimum.  The rows compute (variable - min ≤ 0).  This is used for rejection
criteria when a quantity is too small.
-/
def lowRejectClause
    (D : DPos)
    (x : QDDVar D)
    (minVal : Int) : QDDClause D :=
  { rows :=
      [ ReplayCore.SpecRow.var x.idx x.cert
      , ReplayCore.SpecRow.const minVal
      , ReplayCore.SpecRow.sub 0 1
          (lowViolationCert D x minVal)
      ]
    root := 2
    nonempty := by simp }

/--
Construct a clause certifying that the quantum-to-classical pipeline is
properly linked.  We define the pipeline link flag for the extended record
as `D` when the quantum feature ID matches the classical input feature ID,
and zero otherwise.  A zero flag indicates a broken pipeline.  The
`requireTrueClause` ensures that the link flag equals `D`.
-/
def pipelineLinkFlagV2
    (D : DPos)
    (q : QuantumEvaluationRecordV2 D)
    (c : ClassicalScreeningRecord D) : Int :=
  if q.quantumFeatureId = c.classicalInputFeatureId then ((D : Nat) : Int) else 0

/-- Clause asserting that the quantum-to-classical pipeline link is valid. -/
def pipelineLinkClauseV2
    (D : DPos)
    (q : QuantumEvaluationRecordV2 D)
    (c : ClassicalScreeningRecord D) : QDDClause D :=
  requireTrueClause D (q.quantumFeatureId = c.classicalInputFeatureId)

/--
Clause asserting that the extended provenance record is complete.  This wraps
`boundProvenanceCompleteBool` into a replay clause via `requireTrueClause`.
-/
def provenanceCompleteClause
    (D : DPos)
    (q : QuantumEvaluationRecordV2 D) : QDDClause D :=
  requireTrueClause D (boundProvenanceCompleteBool q.provenance)

/--
Clause asserting that the quantum setup is fully specified.  This wraps
`quantumSetupConsistentBool` into a replay clause via `requireTrueClause`.
-/
def quantumSetupClauseV2
    (D : DPos)
    (q : QuantumEvaluationRecordV2 D) : QDDClause D :=
  requireTrueClause D
    (quantumSetupConsistentBool q.setupIds
      (BoundProvenanceIds.toProvenanceIds q.provenance))

/--
Decision payload distinguishes selected, rejected and review outcomes and
stores the reasons in a structured way.  Using this type rather than
separate optional fields enforces that the three outcomes are disjoint.
-/
structure SelectedDecisionPayload where
  marker : Unit := ()

structure RejectedDecisionPayload where
  reasons : List RejectionReason
  nonempty : reasons ≠ []

structure ReviewDecisionPayload where
  reasons : List ReviewReason
  nonempty : reasons ≠ []

inductive DecisionPayload
  | selected  : SelectedDecisionPayload → DecisionPayload
  | rejected  : RejectedDecisionPayload → DecisionPayload
  | review    : ReviewDecisionPayload → DecisionPayload

/--
An extended candidate selection decision.  All evidence and metadata for a
single candidate are carried along with a decision payload.  This version
uses the enriched quantum record and supports multiple rejection and review
reasons.
-/
structure CandidateSelectionDecisionV2 (D : DPos) where
  ids       : QDDIds
  quantum   : QuantumEvaluationRecordV2 D
  classical : ClassicalScreeningRecord D
  admet     : ADMETRecord D
  approval  : HumanApprovalRecord D
  payload   : DecisionPayload

/--
Recover the simple `DecisionKind` from a `DecisionPayload`.  This helper is
useful for reusing functions that dispatch on the decision kind.
-/
def decisionKindOfPayload : DecisionPayload → DecisionKind
  | DecisionPayload.selected _ => DecisionKind.selected
  | DecisionPayload.rejected _ => DecisionKind.rejected
  | DecisionPayload.review   _ => DecisionKind.needsReview

/--
Determine the `DecisionKind` for an extended decision.  This simply delegates
to `decisionKindOfPayload`.
-/
def CandidateSelectionDecisionV2.kind
    {D : DPos}
    (d : CandidateSelectionDecisionV2 D) : DecisionKind :=
  decisionKindOfPayload d.payload

/--
Check that the extended decision is well-formed.  A selected decision must
carry no reasons; a rejected decision must carry at least one rejection reason
and no review reasons; a review decision must carry at least one review reason
and no rejection reasons.  This predicate enforces the intended disjointness
of the three outcomes.
-/
def QDDDecisionWellFormedV2
    {D : DPos}
    (d : CandidateSelectionDecisionV2 D) : Prop :=
  match d.payload with
  | DecisionPayload.selected _ => True
  | DecisionPayload.rejected r => r.reasons ≠ [] ∧ True
  | DecisionPayload.review r   => r.reasons ≠ [] ∧ True

/--
Selection block for the extended candidate decision.  This block concatenates
clauses for each selection constraint and for the integrity of the evidence and
pipeline.  The resulting block of rows and roots can be embedded into a
certificate without hand-assigning root indices.  Note that this function
does not yet include quantum error dominance or other advanced checks; those
can be added by appending additional clauses.
-/
def selectedBlockV2
    (D : DPos)
    (d : CandidateSelectionDecisionV2 D)
    (p : QDDSelectionPolicy D) : QDDSpecBlock D :=
  concatBlocks
    [ blockOfClause (leClause D d.quantum.energyEstimate p.maxEnergy)
    , blockOfClause (geClause D p.minBindingEnergyProxy d.quantum.bindingEnergyProxy)
    , blockOfClause (geClause D p.minPredictionScore d.classical.predictionScore)
    , blockOfClause (leClause D d.admet.toxicityScore p.maxToxicity)
    , blockOfClause (geClause D p.minSolubility d.admet.solubilityScore)
    , blockOfClause (geClause D p.minStability d.admet.stabilityScore)
    , blockOfClause (leClause D d.admet.admetRisk p.maxAdmetRisk)
    , blockOfClause (leClause D d.quantum.quantumErrorBound p.maxQuantumError)
    , blockOfClause (geClause D p.minModelConfidence d.classical.modelConfidence)
    , blockOfClause (leClause D d.classical.predictionUncertainty p.maxPredictionUncertainty)
    , blockOfClause (leClause D d.classical.datasetShift p.maxDatasetShift)
    , blockOfClause (requireTrueClause D (boolEnc D p.requireApproval ≠ 0))
    , blockOfClause (pipelineLinkClauseV2 D d.quantum d.classical)
    , blockOfClause (provenanceCompleteClause D d.quantum)
    , blockOfClause (quantumSetupClauseV2 D d.quantum)
    ]

/--
Map a rejection reason to the corresponding clause.  The clauses enforce the
negated selection constraints.  Boolean clauses (e.g. pipeline broken or
approval missing) can also be expressed using `requireTrueClause` on the
appropriate boolean condition.  If a new rejection reason is added in the
future it should be handled here.
-/
def rejectionClauseV2
    (D : DPos)
    (d : CandidateSelectionDecisionV2 D)
    (p : QDDSelectionPolicy D) :
    RejectionReason → QDDClause D
  | RejectionReason.energyTooHigh        =>
      highRejectClause D p.maxEnergy d.quantum.energyEstimate
  | RejectionReason.bindingEnergyTooLow  =>
      lowRejectClause D d.quantum.bindingEnergyProxy p.minBindingEnergyProxy
  | RejectionReason.predictionTooLow     =>
      lowRejectClause D d.classical.predictionScore p.minPredictionScore
  | RejectionReason.toxicityTooHigh      =>
      highRejectClause D p.maxToxicity d.admet.toxicityScore
  | RejectionReason.solubilityTooLow     =>
      lowRejectClause D d.admet.solubilityScore p.minSolubility
  | RejectionReason.stabilityTooLow      =>
      lowRejectClause D d.admet.stabilityScore p.minStability
  | RejectionReason.admetRiskTooHigh     =>
      highRejectClause D p.maxAdmetRisk d.admet.admetRisk
  | RejectionReason.quantumErrorTooHigh  =>
      highRejectClause D p.maxQuantumError d.quantum.quantumErrorBound
  | RejectionReason.confidenceTooLow     =>
      lowRejectClause D d.classical.modelConfidence p.minModelConfidence
  | RejectionReason.uncertaintyTooHigh   =>
      highRejectClause D p.maxPredictionUncertainty d.classical.predictionUncertainty
  | RejectionReason.datasetShiftTooHigh  =>
      highRejectClause D p.maxDatasetShift d.classical.datasetShift
  | RejectionReason.approvalMissing      =>
      requireTrueClause D (! p.requireApproval)  -- placeholder: missing approval flag
  | RejectionReason.pipelineBroken       =>
      requireTrueClause D (d.quantum.quantumFeatureId ≠ d.classical.classicalInputFeatureId)

/--
Map a review reason to the corresponding clause.  Review reasons mirror some
of the rejection constraints but typically use different thresholds defined by
the review policy.  Boolean reasons are expressed via `requireTrueClause`.
If the reason refers to missing provenance the clause wraps the negation of
the provenance completeness predicate.
-/
def reviewClauseV2
    (D : DPos)
    (d : CandidateSelectionDecisionV2 D)
    (rp : QDDReviewPolicy D) :
    ReviewReason → QDDClause D
  | ReviewReason.quantumErrorReview   =>
      highRejectClause D rp.reviewQuantumError d.quantum.quantumErrorBound
  | ReviewReason.confidenceReview     =>
      lowRejectClause D d.classical.modelConfidence rp.reviewMinModelConfidence
  | ReviewReason.uncertaintyReview    =>
      highRejectClause D rp.reviewPredictionUncertainty d.classical.predictionUncertainty
  | ReviewReason.datasetShiftReview   =>
      highRejectClause D rp.reviewDatasetShift d.classical.datasetShift
  | ReviewReason.approvalPending      =>
      requireTrueClause D rp.requireApproval
  | ReviewReason.pipelineReview       =>
      requireTrueClause D (d.quantum.quantumFeatureId ≠ d.classical.classicalInputFeatureId)
  | ReviewReason.provenanceIncomplete =>
      requireTrueClause D (¬ boundProvenanceCompleteBool d.quantum.provenance)

/--
Construct the specification block for a rejected decision from its list of
reasons.  The resulting block is empty when the list is empty; well-formed
decisions require nonempty lists for rejected outcomes.
-/
def rejectionBlockV2
    (D : DPos)
    (d : CandidateSelectionDecisionV2 D)
    (p : QDDSelectionPolicy D)
    (rs : List RejectionReason) : QDDSpecBlock D :=
  concatBlocks (rs.map fun r => blockOfClause (rejectionClauseV2 D d p r))

/--
Construct the specification block for a review decision from its list of
reasons.  The resulting block is empty when the list is empty; well-formed
decisions require nonempty lists for review outcomes.
-/
def reviewBlockV2
    (D : DPos)
    (d : CandidateSelectionDecisionV2 D)
    (rp : QDDReviewPolicy D)
    (rs : List ReviewReason) : QDDSpecBlock D :=
  concatBlocks (rs.map fun r => blockOfClause (reviewClauseV2 D d rp r))

/--
Combine the selection, rejection or review blocks based on the decision
payload.  Selected decisions ignore any attached reasons.  Rejected and
reviewed decisions use their respective lists of reasons.
-/
def decisionBlockV2
    (D : DPos)
    (d : CandidateSelectionDecisionV2 D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) : QDDSpecBlock D :=
  match d.payload with
  | DecisionPayload.selected _ =>
      selectedBlockV2 D d p
  | DecisionPayload.rejected r =>
      rejectionBlockV2 D d p r.reasons
  | DecisionPayload.review r   =>
      reviewBlockV2 D d rp r.reasons

/--
Unified certificate for an extended decision.  This certificate packages the
global program rows with the rows and roots built from the decision block.
-/
def qddDecisionCertV2
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecisionV2 D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) : ReplayCore.Cert D :=
  let b := decisionBlockV2 D d p rp
  { rows := rows
    specRows := b.rows
    roots := b.roots }

/--
Replay-validity predicate for extended decisions.  This is defined in terms
of semantic validity of the rows and roots built from the decision block.
-/
def QDDDecisionReplayValidV2
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecisionV2 D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) : Prop :=
  let b := decisionBlockV2 D d p rp
  ReplayCore.SemanticValid D rows b.rows b.roots

/--
Soundness theorem for the extended decision certificate.  If the ADIC verifier
accepts the certificate, then the decision is replay-valid.  The proof relies
on the soundness of the underlying verifier.  Some details remain to be filled
in as indicated by `by`.
-/
theorem qdd_decision_replay_sound_v2
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecisionV2 D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) :
    ReplayCore.verifierBool D (qddDecisionCertV2 D rows d p rp) = true →
    QDDDecisionReplayValidV2 D rows d p rp := by
  intro h
  -- We delegate to the base soundness theorem for the verifier.
  -- The necessary lemmas about block concatenation should be proved separately.
  have hSound :
    ReplayCore.SemanticValid D rows
      (qddDecisionCertV2 D rows d p rp).specRows
      (qddDecisionCertV2 D rows d p rp).roots :=
    ReplayCore.verifierBool_sound D (qddDecisionCertV2 D rows d p rp) h
  -- The specification rows and roots coincide with those of the decision block.
  unfold QDDDecisionReplayValidV2
  simp [qddDecisionCertV2] at hSound
  simpa using hSound

/--
Declared decision validity in the extended domain.  A decision is declared
valid when it is well-formed and replay-valid.  Completeness of the reason
lists (i.e. that they enumerate all violated constraints) is not asserted
here; such completeness must be established by a separate totality policy.
-/
def QDDDeclaredDecisionValidV2
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecisionV2 D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) : Prop :=
  QDDDecisionWellFormedV2 d ∧
  QDDDecisionReplayValidV2 D rows d p rp

/--
Opaque predicate representing therapeutic effectiveness.  The extended artifact
does not prove or claim any statements about therapeutic efficacy.  We leave
this predicate abstract and outside the artifact claim boundary.
-/
opaque TherapeuticEffectiveV2
    (D : DPos)
    (d : CandidateSelectionDecisionV2 D) : Prop

/--
The artifact claim for the extended domain is the declared decision validity.
No claims are made about therapeutic efficacy; by structuring the claim type
this way we ensure that therapeutic goals cannot accidentally be inferred
from the replay evidence.
-/
def ReplayVerifiableCandidateSelectionV2
    (D : DPos)
    (rows : List (ReplayCore.ProgRow D))
    (d : CandidateSelectionDecisionV2 D)
    (p : QDDSelectionPolicy D)
    (rp : QDDReviewPolicy D) : Prop :=
  QDDDeclaredDecisionValidV2 D rows d p rp

end QuantumDrugDiscovery
end ADIC
