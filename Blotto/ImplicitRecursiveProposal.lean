import Blotto.ImplicitLeafProposalInterface
import Blotto.RationalProposalBlockSampler

/-! Actual recursive proposal execution uses succinct native leaf callbacks
and the existing guide-atom categorical at forks. A flat seed reserves one
fixed block per node; failures do not reuse another node's bits. Projection
preserves the original labelled rational tree. Guide orientation/certification
and complete rejection-target integration remain separate. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

inductive ProposalTree where
  | leaf (data : ProposalLeaf) {p : ℕ} (guide : RationalWeightedFamily p) (gamma : ℚ)
  | fork {p : ℕ} (guide : RationalWeightedFamily p) (gamma : ℚ) (left right : ProposalTree)

namespace ProposalTree

def projected : ProposalTree → RationalWeightedGuideTree
  | .leaf data guide gamma => .leaf data.family guide gamma
  | .fork guide gamma left right => .fork guide gamma left.projected right.projected

def Record : ProposalTree → Type
  | .leaf data _ _ => Fin (data.cap + 1)
  | .fork _ _ left right => Fin left.projected.guideSize × right.Record × left.Record

def toProjected : (tree : ProposalTree) → tree.Record → tree.projected.Record
  | .leaf _ _ _, record => record
  | .fork _ _ left right, record => (record.1, right.toProjected record.2.1, left.toProjected record.2.2)

def resource : (tree : ProposalTree) → tree.Record → ℚ
  | .leaf data _ _, record => data.decode record.val
  | .fork _ _ left right, record => left.resource record.2.2 + right.resource record.2.1

theorem projected_resource (tree : ProposalTree) (record : tree.Record) :
    tree.projected.resource (tree.toProjected record) = tree.resource record := by
  induction tree with
  | leaf data guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    change left.projected.resource (left.toProjected record.2.2) + right.projected.resource (right.toProjected record.2.1) = _
    rw [ihL, ihR]
    rfl

def bitBudget : ProposalTree → ℕ → ℕ → ℕ
  | .leaf data _ _, K, attempts => data.bitBudget K attempts
  | .fork _ _ left right, K, attempts =>
    3 * (left.projected.guideSize - 1 + K) + right.bitBudget K attempts + left.bitBudget K attempts

def sample : (tree : ProposalTree) → (budget : ℚ) → (K attempts : ℕ) →
    (Fin (tree.bitBudget K attempts) → Bool) → Option tree.Record
  | .leaf data _ _, budget, K, attempts, bits => data.sample budget K attempts bits
  | .fork _ _ left right, budget, K, attempts, bits =>
    let root := 3 * (left.projected.guideSize - 1 + K)
    let seed : Fin (root + (right.bitBudget K attempts + left.bitBudget K attempts)) → Bool :=
      fun index => bits (index.cast (by simp only [bitBudget]; omega))
    let rootBits := firstBitBlock root (right.bitBudget K attempts + left.bitBudget K attempts) seed
    let remaining := secondBitBlock root (right.bitBudget K attempts + left.bitBudget K attempts) seed
    let rightBits := firstBitBlock (right.bitBudget K attempts) (left.bitBudget K attempts) remaining
    let leftBits := secondBitBlock (right.bitBudget K attempts) (left.bitBudget K attempts) remaining
    match left.projected.guide.syntheticSample right.projected.guide budget K (finiteBitReader rootBits) with
    | none => none
    | some index =>
      match right.sample (budget - left.projected.guide.resource index) K attempts rightBits with
      | none => none
      | some rightRecord =>
        (left.sample (budget - right.resource rightRecord) K attempts leftBits).map
          (fun leftRecord => (index, rightRecord, leftRecord))

noncomputable def kernel (actual : Bool) : (tree : ProposalTree) → ℚ → ℕ → ℕ → BoundedExpectationKernel (Option tree.Record)
  | .leaf data _ _, budget, K, attempts => if actual then data.actualKernel budget K attempts else data.idealKernel budget
  | .fork _ _ left right, budget, K, attempts =>
    let choice := if actual then positiveChoiceKernel (RationalWeightedGuideTree.forkWeights left.projected right.projected budget)
      (RationalWeightedGuideTree.forkWeights_nonnegative left.projected right.projected budget) K
      else totalNormalizedKernel (RationalWeightedGuideTree.forkWeights left.projected right.projected budget)
        (RationalWeightedGuideTree.forkWeights_nonnegative left.projected right.projected budget)
    choice.bind (fun selected => match selected with
      | none => BoundedExpectationKernel.point none
      | some index => (right.kernel actual (budget - left.projected.guide.resource index) K attempts).bind (fun rightRecord => match rightRecord with
        | none => BoundedExpectationKernel.point none
        | some rightRecord => (left.kernel actual (budget - right.resource rightRecord) K attempts).map
          (fun leftRecord => leftRecord.map (fun leftRecord => (index, rightRecord, leftRecord)))))

noncomputable def error : ProposalTree → ℕ → ℕ → ℝ
  | .leaf _ _ _, K, attempts => 1 / (2 : ℝ) ^ K + 1 / (2 : ℝ) ^ attempts
  | .fork _ _ left right, K, attempts => 1 / (2 : ℝ) ^ K + right.error K attempts + left.error K attempts

theorem error_nonnegative (tree : ProposalTree) (K attempts : ℕ) : 0 ≤ tree.error K attempts := by
  induction tree with
  | leaf data guide gamma => dsimp only [error]; positivity
  | fork guide gamma left right ihL ihR => dsimp only [error]; positivity

theorem kernel_error (tree : ProposalTree) (budget : ℚ) (K attempts : ℕ) :
    (tree.kernel true budget K attempts).Close (tree.kernel false budget K attempts) (tree.error K attempts) := by
  induction tree generalizing budget with
  | leaf data guide gamma => exact data.actualKernel_close budget K attempts
  | fork guide gamma left right ihL ihR =>
    have hChoice := positiveChoiceKernel_total_close
      (RationalWeightedGuideTree.forkWeights left.projected right.projected budget)
      (RationalWeightedGuideTree.forkWeights_nonnegative left.projected right.projected budget) K
    have hNext : ∀ selected : Option (Fin left.projected.guideSize),
        (match selected with
        | none => BoundedExpectationKernel.point (none : Option (Fin left.projected.guideSize × right.Record × left.Record))
        | some index => (right.kernel true (budget - left.projected.guide.resource index) K attempts).bind (fun r => match r with
          | none => BoundedExpectationKernel.point none
          | some r => (left.kernel true (budget - right.resource r) K attempts).map (fun l => l.map (fun l => (index, r, l))))).Close
        (match selected with
        | none => BoundedExpectationKernel.point none
        | some index => (right.kernel false (budget - left.projected.guide.resource index) K attempts).bind (fun r => match r with
          | none => BoundedExpectationKernel.point none
          | some r => (left.kernel false (budget - right.resource r) K attempts).map (fun l => l.map (fun l => (index, r, l)))))
        (right.error K attempts + left.error K attempts) := by
      intro selected
      cases selected with
      | none => intro f hf; simp only [sub_self, abs_zero]; exact add_nonneg (right.error_nonnegative K attempts) (left.error_nonnegative K attempts)
      | some index =>
        apply BoundedExpectationKernel.bind_close _ _ _ _ _ _ (ihR _)
        intro r
        cases r with
        | none => intro f hf; simp only [sub_self, abs_zero]; exact left.error_nonnegative K attempts
        | some r => exact BoundedExpectationKernel.map_close _ _ _ _ (ihL _)
    have he := BoundedExpectationKernel.bind_close _ _ _ _ _ _ hChoice hNext
    simpa only [kernel, Record, Bool.false_eq_true, ite_false, ite_true, error, add_assoc] using he

theorem sample_feasible (tree : ProposalTree) (budget : ℚ) (K attempts : ℕ)
    (bits : Fin (tree.bitBudget K attempts) → Bool) (record : tree.Record)
    (h : tree.sample budget K attempts bits = some record) : tree.resource record ≤ budget := by
  induction tree generalizing budget with
  | leaf data guide gamma => exact (data.sample_some_contract budget K attempts bits record h).1
  | fork guide gamma left right ihL ihR =>
    change Fin left.projected.guideSize × right.Record × left.Record at record
    change left.resource record.2.2 + right.resource record.2.1 ≤ budget
    change (fork guide gamma left right).sample budget K attempts bits = some record at h
    unfold sample at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i index hIndex r hRight
        cases hLeft : left.sample (budget - right.resource r) K attempts _ with
        | none =>
          rw [hLeft] at h
          change (none : Option (Fin left.projected.guideSize × right.Record × left.Record)) = some record at h
          cases h
        | some l =>
          rw [hLeft] at h
          change some (_, r, l) = some record at h
          cases Option.some.inj h
          have hl := ihL (budget - right.resource r) _ l hLeft
          change left.resource l + right.resource r ≤ budget
          linarith

theorem sample_mean (tree : ProposalTree) (budget : ℚ) (K attempts : ℕ)
    (f : Option tree.Record → ℝ) :
    (fairBitKernel (tree.bitBudget K attempts)).mean (fun bits => f (tree.sample budget K attempts bits)) =
      (tree.kernel true budget K attempts).mean f := by
  induction tree generalizing budget with
  | leaf data guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    change Option (Fin left.projected.guideSize × right.Record × left.Record) → ℝ at f
    let root := 3 * (left.projected.guideSize - 1 + K)
    have hSize : (fork guide gamma left right).bitBudget K attempts =
        root + (right.bitBudget K attempts + left.bitBudget K attempts) := by dsimp [root, bitBudget]; omega
    have hCast := fairBitKernel_cast (root + (right.bitBudget K attempts + left.bitBudget K attempts))
      ((fork guide gamma left right).bitBudget K attempts) hSize.symm
      (fun bits => f ((fork guide gamma left right).sample budget K attempts bits))
    apply hCast.symm.trans
    have hRun : ∀ bits : Fin (root + (right.bitBudget K attempts + left.bitBudget K attempts)) → Bool,
        (fork guide gamma left right).sample budget K attempts (fun j => bits (j.cast hSize)) =
        match left.projected.guide.syntheticSample right.projected.guide budget K
          (finiteBitReader (firstBitBlock root (right.bitBudget K attempts + left.bitBudget K attempts) bits)) with
        | none => none
        | some i => match right.sample (budget - left.projected.guide.resource i) K attempts
            (firstBitBlock (right.bitBudget K attempts) (left.bitBudget K attempts)
              (secondBitBlock root (right.bitBudget K attempts + left.bitBudget K attempts) bits)) with
          | none => none
          | some r => (left.sample (budget - right.resource r) K attempts
              (secondBitBlock (right.bitBudget K attempts) (left.bitBudget K attempts)
                (secondBitBlock root (right.bitBudget K attempts + left.bitBudget K attempts) bits))).map (fun l => (i, r, l)) := by
      intro bits
      rfl
    simp_rw [hRun]
    have hSplit := fairBitKernel_blocks root (right.bitBudget K attempts + left.bitBudget K attempts)
      (fun first rest => f (match left.projected.guide.syntheticSample right.projected.guide budget K (finiteBitReader first) with
        | none => none
        | some i => match right.sample (budget - left.projected.guide.resource i) K attempts
            (firstBitBlock (right.bitBudget K attempts) (left.bitBudget K attempts) rest) with
          | none => none
          | some r => (left.sample (budget - right.resource r) K attempts
              (secondBitBlock (right.bitBudget K attempts) (left.bitBudget K attempts) rest)).map (fun l => (i, r, l))))
    apply hSplit.trans
    have hRest : ∀ selected : Option (Fin left.projected.guideSize),
        (fairBitKernel (right.bitBudget K attempts + left.bitBudget K attempts)).mean (fun bits =>
          f (match selected with
          | none => none
          | some i => match right.sample (budget - left.projected.guide.resource i) K attempts
              (firstBitBlock (right.bitBudget K attempts) (left.bitBudget K attempts) bits) with
            | none => none
            | some r => (left.sample (budget - right.resource r) K attempts
                (secondBitBlock (right.bitBudget K attempts) (left.bitBudget K attempts) bits)).map (fun l => (i, r, l)))) =
        (match selected with
        | none => BoundedExpectationKernel.point none
        | some i => (right.kernel true (budget - left.projected.guide.resource i) K attempts).bind (fun r => match r with
          | none => BoundedExpectationKernel.point none
          | some r => (left.kernel true (budget - right.resource r) K attempts).map (fun l => l.map (fun l => (i, r, l))))).mean f := by
      intro selected
      cases selected with
      | none => dsimp only; exact (fairBitKernel _).constant _
      | some i =>
        dsimp only
        have hChildren := fairBitKernel_blocks (right.bitBudget K attempts) (left.bitBudget K attempts)
          (fun rightBits leftBits => f (match right.sample (budget - left.projected.guide.resource i) K attempts rightBits with
            | none => none
            | some r => (left.sample (budget - right.resource r) K attempts leftBits).map (fun l => (i, r, l))))
        apply hChildren.trans
        have hLeft : ∀ r : Option right.Record,
            (fairBitKernel (left.bitBudget K attempts)).mean (fun bits => f (match r with
              | none => none | some r => (left.sample (budget - right.resource r) K attempts bits).map (fun l => (i, r, l)))) =
            (match r with
            | none => BoundedExpectationKernel.point none
            | some r => (left.kernel true (budget - right.resource r) K attempts).map (fun l => l.map (fun l => (i, r, l)))).mean f := by
          intro r
          cases r with
          | none => dsimp only; exact (fairBitKernel _).constant _
          | some r =>
            dsimp only [BoundedExpectationKernel.map, BoundedExpectationKernel.bind, BoundedExpectationKernel.point]
            exact ihL (budget - right.resource r) (fun x => f (x.map (fun l => (i, r, l))))
        simp_rw [hLeft]
        exact ihR (budget - left.projected.guide.resource i) (fun result =>
          (match result with
          | none => BoundedExpectationKernel.point none
          | some r => (left.kernel true (budget - right.resource r) K attempts).map (fun l => l.map (fun l => (i, r, l)))).mean f)
    simp_rw [hRest]
    rfl

theorem sample_mean_error (tree : ProposalTree) (budget : ℚ) (K attempts : ℕ)
    (f : Option tree.Record → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(fairBitKernel (tree.bitBudget K attempts)).mean (fun bits => f (tree.sample budget K attempts bits)) -
      (tree.kernel false budget K attempts).mean f| ≤ tree.error K attempts := by
  rw [sample_mean]
  exact tree.kernel_error budget K attempts f hf

end ProposalTree
end ImplicitLeafCounts
end Blotto
