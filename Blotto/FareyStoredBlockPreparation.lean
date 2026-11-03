import Blotto.FareyNativeBlockState

/-! Direct Farey preparation consumes already materialized block tables.
History is absent from native preparation. Equality with history-based
preparation follows from the proof-only state invariant, preserving exact
rows, whole Gibbs targets, seed widths and source guarantees. Full tree
rebuilding/pair enumeration and physical array-copy costs remain separate. -/

namespace Blotto.FareyImplicitTrainer
open scoped BigOperators
open Farey ImplicitLeafCounts ProductSecurityTrainer
namespace NativeBlockState

def firstLeaf {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (field : Fin m) : ProposalLeaf :=
  fareyLeaf input.first (input.scaleA field) (input.scaleA_nonnegative field) (state.first.read field)
    (state.first_partition field) (state.first_positive field)

def secondLeaf {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (field : Fin m) : ProposalLeaf :=
  fareyLeaf input.second (input.scaleB field) (input.scaleB_nonnegative field) (state.second.read field)
    (state.second_partition field) (state.second_positive field)

def firstAccess {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (field : Fin m) : LeafAccess (state.firstLeaf field) :=
  fareyLeafAccess input.first (input.scaleA field) (input.scaleA_nonnegative field) (state.first.read field)
    (state.first_partition field) (state.first_positive field)

def secondAccess {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (field : Fin m) : LeafAccess (state.secondLeaf field) :=
  fareyLeafAccess input.second (input.scaleB field) (input.scaleB_nonnegative field) (state.second.read field)
    (state.second_partition field) (state.second_positive field)

theorem firstLeaf_nonnegative {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (field : Fin m)
    (code : Fin ((state.firstLeaf field).cap + 1)) : 0 ≤ (state.firstLeaf field).decode code.val := by
  change 0 ≤ FareyDirectBlockHistory.decode input.first (input.scaleA field) code.val
  have hc : code.val ≤ rankCap input.first.order := by have h := code.isLt; change code.val < rankCap input.first.order + 1 at h; omega
  rw [FareyDirectBlockHistory.decode_valid _ _ _ hc]
  exact mul_nonneg (input.scaleA_nonnegative field) (decode_nonnegative input.first code.val)

theorem secondLeaf_nonnegative {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (field : Fin m)
    (code : Fin ((state.secondLeaf field).cap + 1)) : 0 ≤ (state.secondLeaf field).decode code.val := by
  change 0 ≤ FareyDirectBlockHistory.decode input.second (input.scaleB field) code.val
  have hc : code.val ≤ rankCap input.second.order := by have h := code.isLt; change code.val < rankCap input.second.order + 1 at h; omega
  rw [FareyDirectBlockHistory.decode_valid _ _ _ hc]
  exact mul_nonneg (input.scaleB_nonnegative field) (decode_nonnegative input.second code.val)

theorem firstLeaf_zero {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (field : Fin m) :
    (state.firstLeaf field).decode 0 = 0 := by
  change FareyDirectBlockHistory.decode input.first (input.scaleA field) 0 = 0
  rw [FareyDirectBlockHistory.decode_valid _ _ _ (Nat.zero_le _), decode_zero, mul_zero]

theorem secondLeaf_zero {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (field : Fin m) :
    (state.secondLeaf field).decode 0 = 0 := by
  change FareyDirectBlockHistory.decode input.second (input.scaleB field) 0 = 0
  rw [FareyDirectBlockHistory.decode_valid _ _ _ (Nat.zero_le _), decode_zero, mul_zero]

def preparedA {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input) : ExactSizedDraw (n + 1) :=
  prepareAccessLeafComb n state.firstLeaf state.firstAccess state.firstLeaf_nonnegative state.firstLeaf_zero
    input.budgetA input.budgetA_nonnegative

def preparedB {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input) : ExactSizedDraw (n + 1) :=
  prepareAccessLeafComb n state.secondLeaf state.secondAccess state.secondLeaf_nonnegative state.secondLeaf_zero
    input.budgetB input.budgetB_nonnegative

theorem firstLeaf_eq_history {m : ℕ} {input : DirectInput m} (state : NativeBlockState input)
    (past : List (RawObservation m)) (h : state.Matches past) (field : Fin m) :
    state.firstLeaf field = fareyHistoryLeaf input.first input.scaleA input.scaleA_nonnegative rawSelected
      (fun _ x => x.2.1 x.2.2) input.eta input.theta input.eta_unit input.theta_unit past field := by
  unfold firstLeaf fareyHistoryLeaf
  congr 1
  exact h.1 field

theorem secondLeaf_eq_history {m : ℕ} {input : DirectInput m} (state : NativeBlockState input)
    (past : List (RawObservation m)) (h : state.Matches past) (field : Fin m) :
    state.secondLeaf field = fareyHistoryLeaf input.second input.scaleB input.scaleB_nonnegative rawSelected
      (fun _ x => x.1 x.2.2) input.eta input.theta input.eta_unit input.theta_unit past field := by
  unfold secondLeaf fareyHistoryLeaf
  congr 1
  exact h.2 field

theorem fareyAccessPair_congr (spec : RankUniverse) (scale : ℚ) (hs : 0 ≤ scale) (first second : List Block)
    (hpf : Partition (rankCap spec.order) first) (hps : Partition (rankCap spec.order) second)
    (hwf : Positive first) (hws : Positive second) (he : first = second) :
    (⟨fareyLeaf spec scale hs first hpf hwf, fareyLeafAccess spec scale hs first hpf hwf⟩ :
      (leaf : ProposalLeaf) × LeafAccess leaf) =
      ⟨fareyLeaf spec scale hs second hps hws, fareyLeafAccess spec scale hs second hps hws⟩ := by
  cases he
  rfl

def prepareAccessPairs (n : ℕ) (pairs : Fin (n + 1) → (leaf : ProposalLeaf) × LeafAccess leaf)
    (hn : ∀ field (code : Fin ((pairs field).1.cap + 1)), 0 ≤ (pairs field).1.decode code.val)
    (hz : ∀ field, (pairs field).1.decode 0 = 0) (budget : ℚ) (hb : 0 ≤ budget) : ExactSizedDraw (n + 1) :=
  prepareAccessLeafComb n (fun field => (pairs field).1) (fun field => (pairs field).2) hn hz budget hb

theorem prepareAccessPairs_congr (n : ℕ) (first second : Fin (n + 1) → (leaf : ProposalLeaf) × LeafAccess leaf)
    (he : first = second)
    (hnf : ∀ field (code : Fin ((first field).1.cap + 1)), 0 ≤ (first field).1.decode code.val)
    (hns : ∀ field (code : Fin ((second field).1.cap + 1)), 0 ≤ (second field).1.decode code.val)
    (hzf : ∀ field, (first field).1.decode 0 = 0) (hzs : ∀ field, (second field).1.decode 0 = 0)
    (budget : ℚ) (hb : 0 ≤ budget) : prepareAccessPairs n first hnf hzf budget hb = prepareAccessPairs n second hns hzs budget hb := by
  cases he
  rfl

theorem preparedA_eq_history {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (past : List (RawObservation (n + 1))) (h : state.Matches past) : state.preparedA = input.preparedA past := by
  let first : Fin (n + 1) → (leaf : ProposalLeaf) × LeafAccess leaf := fun field => ⟨state.firstLeaf field, state.firstAccess field⟩
  let second : Fin (n + 1) → (leaf : ProposalLeaf) × LeafAccess leaf := fun field =>
    ⟨fareyHistoryLeaf input.first input.scaleA input.scaleA_nonnegative rawSelected (fun _ x => x.2.1 x.2.2)
      input.eta input.theta input.eta_unit input.theta_unit past field,
    fareyHistoryAccess input.first input.scaleA input.scaleA_nonnegative rawSelected (fun _ x => x.2.1 x.2.2)
      input.eta input.theta input.eta_unit input.theta_unit past field⟩
  have he : first = second := by
    funext field
    exact fareyAccessPair_congr input.first (input.scaleA field) (input.scaleA_nonnegative field) _ _ _ _ _ _ (h.1 field)
  exact prepareAccessPairs_congr n first second he _ _ _ _ input.budgetA input.budgetA_nonnegative

theorem preparedB_eq_history {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (past : List (RawObservation (n + 1))) (h : state.Matches past) : state.preparedB = input.preparedB past := by
  let first : Fin (n + 1) → (leaf : ProposalLeaf) × LeafAccess leaf := fun field => ⟨state.secondLeaf field, state.secondAccess field⟩
  let second : Fin (n + 1) → (leaf : ProposalLeaf) × LeafAccess leaf := fun field =>
    ⟨fareyHistoryLeaf input.second input.scaleB input.scaleB_nonnegative rawSelected (fun _ x => x.1 x.2.2)
      input.eta input.theta input.eta_unit input.theta_unit past field,
    fareyHistoryAccess input.second input.scaleB input.scaleB_nonnegative rawSelected (fun _ x => x.1 x.2.2)
      input.eta input.theta input.eta_unit input.theta_unit past field⟩
  have he : first = second := by
    funext field
    exact fareyAccessPair_congr input.second (input.scaleB field) (input.scaleB_nonnegative field) _ _ _ _ _ _ (h.2 field)
  exact prepareAccessPairs_congr n first second he _ _ _ _ input.budgetB input.budgetB_nonnegative

theorem preparedA_model {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (past : List (RawObservation (n + 1))) (h : state.Matches past) :
    state.preparedA.model = input.trainer.compactPreparedA input.config past := by
  rw [state.preparedA_eq_history past h]
  exact input.preparedA_model past

theorem preparedB_model {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (past : List (RawObservation (n + 1))) (h : state.Matches past) :
    state.preparedB.model = input.trainer.compactPreparedB input.config past := by
  rw [state.preparedB_eq_history past h]
  exact input.preparedB_model past

theorem preparedA_budget {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input) :
    state.preparedA.budget = input.budgetA := rfl

theorem preparedB_budget {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input) :
    state.preparedB.budget = input.budgetB := rfl

theorem preparedA_target_mean {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (past : List (RawObservation (n + 1))) (h : state.Matches past) (test : (Fin (n + 1) → ℚ) → ℝ) :
    state.preparedA.model.targetKernel.mean test = (input.trainer.rawPreparedA past).rationalTargetKernel.mean test := by
  rw [state.preparedA_eq_history past h]
  exact input.preparedA_target_mean past test

theorem preparedB_target_mean {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (past : List (RawObservation (n + 1))) (h : state.Matches past) (test : (Fin (n + 1) → ℚ) → ℝ) :
    state.preparedB.model.targetKernel.mean test = (input.trainer.rawPreparedB past).rationalTargetKernel.mean test := by
  rw [state.preparedB_eq_history past h]
  exact input.preparedB_target_mean past test

theorem first_total_blocks {m : ℕ} {input : DirectInput m} (state : NativeBlockState input)
    (past : List (RawObservation m)) (h : state.Matches past) :
    (∑ field, (state.first.read field).length) ≤ m + 2 * past.length := by
  calc
    _ ≤ ∑ field : Fin m, (1 + 2 * genericCount rawSelected past field) :=
      Finset.sum_le_sum (fun field _ => state.first_history_length past h field)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, genericCount_sum]; simp

theorem second_total_blocks {m : ℕ} {input : DirectInput m} (state : NativeBlockState input)
    (past : List (RawObservation m)) (h : state.Matches past) :
    (∑ field, (state.second.read field).length) ≤ m + 2 * past.length := by
  calc
    _ ≤ ∑ field : Fin m, (1 + 2 * genericCount rawSelected past field) :=
      Finset.sum_le_sum (fun field _ => state.second_history_length past h field)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, genericCount_sum]; simp

end NativeBlockState
end Blotto.FareyImplicitTrainer
