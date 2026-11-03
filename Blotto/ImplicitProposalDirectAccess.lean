import Blotto.ImplicitLeafPrefixDirectAccess
import Blotto.ImplicitProposalRejection

/-! The actual recursive proposal and importance evaluator use stored native
leaf access. In particular, leaf importance is an affine block-prefix query;
it never enumerates the code universe. Exact refinement to the old proposal
and acceptance formulas retains their feasibility and distribution proofs. -/

namespace Blotto.ImplicitLeafCounts

def TreeAccess : ProposalTree → Type
  | .leaf data _ _ => LeafAccess data
  | .fork _ _ left right => TreeAccess left × TreeAccess right

namespace TreeAccess

def sample : (tree : ProposalTree) → TreeAccess tree → (budget : ℚ) → (K attempts : ℕ) →
    (Fin (tree.bitBudget K attempts) → Bool) → Option tree.Record
  | .leaf _ _ _, access, budget, K, attempts, bits => LeafAccess.sample access budget K attempts bits
  | .fork _ _ left right, access, budget, K, attempts, bits =>
    let root := 3 * (left.projected.guideSize - 1 + K)
    let seed : Fin (root + (right.bitBudget K attempts + left.bitBudget K attempts)) → Bool :=
      fun index => bits (index.cast (by simp only [ProposalTree.bitBudget]; omega))
    let rootBits := firstBitBlock root (right.bitBudget K attempts + left.bitBudget K attempts) seed
    let remaining := secondBitBlock root (right.bitBudget K attempts + left.bitBudget K attempts) seed
    let rightBits := firstBitBlock (right.bitBudget K attempts) (left.bitBudget K attempts) remaining
    let leftBits := secondBitBlock (right.bitBudget K attempts) (left.bitBudget K attempts) remaining
    match left.projected.guide.syntheticSample right.projected.guide budget K (finiteBitReader rootBits) with
    | none => none
    | some index =>
      match sample right access.2 (budget - left.projected.guide.resource index) K attempts rightBits with
      | none => none
      | some rightRecord =>
        (sample left access.1 (budget - right.resource rightRecord) K attempts leftBits).map
          (fun leftRecord => (index, rightRecord, leftRecord))

def importance : (tree : ProposalTree) → TreeAccess tree → ℚ → tree.Record → ℚ
  | .leaf _ _ _, access, budget, _ => access.massPrefix budget
  | .fork _ _ left right, access, budget, record =>
    left.projected.guide.convolution right.projected.guide budget *
      importance left access.1 (budget - right.resource record.2.1) record.2.2 *
      importance right access.2 (budget - left.projected.guide.resource record.1) record.2.1 /
        (left.projected.guidePrefix (budget - right.resource record.2.1) *
          right.projected.guidePrefix (budget - left.projected.guide.resource record.1))

theorem sample_eq (tree : ProposalTree) (access : TreeAccess tree) (budget : ℚ) (K attempts : ℕ)
    (bits : Fin (tree.bitBudget K attempts) → Bool) : sample tree access budget K attempts bits = tree.sample budget K attempts bits := by
  induction tree generalizing budget with
  | leaf data guide gamma => exact LeafAccess.sample_eq access budget K attempts bits
  | fork guide gamma left right ihL ihR =>
    change TreeAccess left × TreeAccess right at access
    simp only [sample, ProposalTree.sample]
    simp_rw [ihL access.1, ihR access.2]
    rfl

theorem importance_eq (tree : ProposalTree) (access : TreeAccess tree) (budget : ℚ) (record : tree.Record) :
    importance tree access budget record = tree.projected.importance budget (tree.toProjected record) := by
  induction tree generalizing budget with
  | leaf data guide gamma => exact access.massPrefix_eq budget
  | fork guide gamma left right ihL ihR =>
    change TreeAccess left × TreeAccess right at access
    change Fin left.projected.guideSize × right.Record × left.Record at record
    change left.projected.guide.convolution right.projected.guide budget *
        importance left access.1 (budget - right.resource record.2.1) record.2.2 *
        importance right access.2 (budget - left.projected.guide.resource record.1) record.2.1 /
          (left.projected.guidePrefix (budget - right.resource record.2.1) * right.projected.guidePrefix (budget - left.projected.guide.resource record.1)) = _
    rw [ihL access.1, ihR access.2]
    change _ = left.projected.guide.convolution right.projected.guide budget *
      left.projected.importance (budget - right.projected.resource (right.toProjected record.2.1)) (left.toProjected record.2.2) *
      right.projected.importance (budget - left.projected.guide.resource record.1) (right.toProjected record.2.1) /
        (left.projected.guidePrefix (budget - right.projected.resource (right.toProjected record.2.1)) *
          right.projected.guidePrefix (budget - left.projected.guide.resource record.1))
    rw [right.projected_resource]

def acceptProbability (tree : ProposalTree) (access : TreeAccess tree) (budget : ℚ) (record : tree.Record) : ℚ :=
  importance tree access budget record / tree.projected.acceptanceBound budget

theorem acceptProbability_eq (tree : ProposalTree) (access : TreeAccess tree) (budget : ℚ) (record : tree.Record) :
    acceptProbability tree access budget record = tree.acceptProbability budget record := by
  unfold acceptProbability ProposalTree.acceptProbability RationalWeightedGuideTree.acceptanceProbability
  rw [importance_eq]

theorem acceptanceAttempt_congr (first second : ℚ) (hf : 0 ≤ first ∧ first ≤ 1) (hs : 0 ≤ second ∧ second ≤ 1)
    (h : first = second) : rationalAcceptanceAttempt first hf = rationalAcceptanceAttempt second hs := by
  cases h
  rfl

def attempt (tree : ProposalTree) (access : TreeAccess tree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ)
    (bits : Fin (tree.attemptBitBudget K leafAttempts) → Bool) : Option tree.Record :=
  match sample tree access budget K leafAttempts (firstBitBlock (tree.bitBudget K leafAttempts) (3 * (1 + K)) bits) with
  | none => none
  | some record => ((rationalAcceptanceAttempt (acceptProbability tree access budget record)
      (by rw [acceptProbability_eq]; exact tree.acceptProbability_unit hc budget hm record)).sample K
        (secondBitBlock (tree.bitBudget K leafAttempts) (3 * (1 + K)) bits)).map (fun _ => record)

theorem attempt_eq (tree : ProposalTree) (access : TreeAccess tree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ)
    (bits : Fin (tree.attemptBitBudget K leafAttempts) → Bool) :
    attempt tree access hc budget hm K leafAttempts bits = tree.attempt hc budget hm K leafAttempts bits := by
  unfold attempt ProposalTree.attempt
  simp only [sample_eq]
  split
  · rename_i he
    simp only [he]
  · rename_i record he
    rw [he]
    have hNew : 0 ≤ acceptProbability tree access budget record ∧ acceptProbability tree access budget record ≤ 1 := by
      rw [acceptProbability_eq]
      exact tree.acceptProbability_unit hc budget hm record
    rw [acceptanceAttempt_congr (acceptProbability tree access budget record) (tree.acceptProbability budget record)
      hNew (tree.acceptProbability_unit hc budget hm record) (acceptProbability_eq tree access budget record)]

def rejection (tree : ProposalTree) (access : TreeAccess tree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ) :
    (attempts : ℕ) → (Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) → Option tree.Record
  | 0, _ => none
  | attempts + 1, bits =>
    let width := tree.attemptBitBudget K leafAttempts
    let seed : Fin (width + attempts * width) → Bool := fun index => bits (index.cast (by dsimp only [width]; ring))
    match attempt tree access hc budget hm K leafAttempts (firstBitBlock width (attempts * width) seed) with
    | some record => some record
    | none => rejection tree access hc budget hm K leafAttempts attempts (secondBitBlock width (attempts * width) seed)

theorem rejection_eq (tree : ProposalTree) (access : TreeAccess tree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (bits : Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) :
    rejection tree access hc budget hm K leafAttempts attempts bits = tree.rejection hc budget hm K leafAttempts attempts bits := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    simp only [rejection, ProposalTree.rejection, attempt_eq]
    simp_rw [ih]
    rfl

end TreeAccess
end Blotto.ImplicitLeafCounts
