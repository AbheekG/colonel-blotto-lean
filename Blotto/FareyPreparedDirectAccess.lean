import Blotto.PreparedImplicitDirectAccess
import Blotto.ImplicitGibbsPreparedSampler

/-! Concrete Farey history preparation stores direct weak/strict/cap access,
uses direct-cut rounded blocks, and computes exact guide data once. All
execution equalities to the retained compact Gibbs sampler are derived. -/

namespace Blotto.ImplicitLeafCounts
open Farey

def leafCombAccess : (n : ℕ) → (data : Fin (n + 1) → ProposalLeaf) →
    ((field : Fin (n + 1)) → LeafAccess (data field)) → TreeAccess (leafComb n data)
  | 0, _, access => access 0
  | n + 1, data, access => (access 0, leafCombAccess n (fun field => data field.succ) (fun field => access field.succ))

def prepareAccessLeafComb (n : ℕ) (data : Fin (n + 1) → ProposalLeaf)
    (access : (field : Fin (n + 1)) → LeafAccess (data field))
    (hn : ∀ field (code : Fin ((data field).cap + 1)), 0 ≤ (data field).decode code.val)
    (hz : ∀ field, (data field).decode 0 = 0) (budget : ℚ) (hb : 0 ≤ budget) : ExactSizedDraw (n + 1) :=
  let prepared := PreparedAccessSampler.prepareZero (leafComb n data) (leafCombAccess n data access)
    (leafComb_nonnegative n data hn) (leafComb_zero n data hz) budget hb
  prepared.sized (by
    rw [PreparedAccessSampler.prepareZero_model_eq]
    exact ((leafComb n data).rebuild_allocation_fields (leafComb_nonnegative n data hn)
      (leafComb n data).constructionGamma (leafComb n data).constructionGamma_ge_one).trans (leafComb_fields n data hn))

theorem sized_model_congr {m : ℕ} (first second : PreparedImplicitSampler) (he : first = second)
    (hf : (first.tree.allocationTree first.nonnegative).fields = m)
    (hs : (second.tree.allocationTree second.nonnegative).fields = m) :
    (⟨first, hf⟩ : SizedImplicitSampler m) = ⟨second, hs⟩ := by
  cases he
  rfl

theorem prepareAccessLeafComb_model (n : ℕ) (data : Fin (n + 1) → ProposalLeaf)
    (access : (field : Fin (n + 1)) → LeafAccess (data field))
    (hn : ∀ field (code : Fin ((data field).cap + 1)), 0 ≤ (data field).decode code.val)
    (hz : ∀ field, (data field).decode 0 = 0) (budget : ℚ) (hb : 0 ≤ budget) :
    (prepareAccessLeafComb n data access hn hz budget hb).model = prepareLeafComb n data hn hz budget hb := by
  exact sized_model_congr _ _ (PreparedAccessSampler.prepareZero_model_eq
    (leafComb n data) (leafCombAccess n data access) (leafComb_nonnegative n data hn) (leafComb_zero n data hz) budget hb) _ _

def fareyHistoryLeaf {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) (field : Fin m) : ProposalLeaf :=
  fareyLeaf spec (scale field) (hs field) (FareyDirectBlockHistory.blocks spec scale selected opponent eta theta past field)
    (FareyDirectBlockHistory.blocks_partition spec scale hs selected opponent eta theta past field)
    (FareyDirectBlockHistory.blocks_positive spec scale hs selected opponent eta theta heta htheta past field)

def fareyHistoryAccess {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) (field : Fin m) :
    LeafAccess (fareyHistoryLeaf spec scale hs selected opponent eta theta heta htheta past field) :=
  fareyLeafAccess spec (scale field) (hs field) _
    (FareyDirectBlockHistory.blocks_partition spec scale hs selected opponent eta theta past field)
    (FareyDirectBlockHistory.blocks_positive spec scale hs selected opponent eta theta heta htheta past field)

theorem fareyHistoryLeaf_eq {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) (field : Fin m) :
    fareyHistoryLeaf spec scale hs selected opponent eta theta heta htheta past field =
      genericLeaf (fun _ => rankCap spec.order) (fun field => FareyDirectBlockHistory.decode spec (scale field))
        (fun field => FareyDirectBlockHistory.decode_ordered spec _ (hs field)) selected opponent eta theta heta htheta past field := by
  unfold fareyHistoryLeaf fareyLeaf genericLeaf
  congr 1
  exact congrFun (FareyDirectBlockHistory.blocks_eq_generic spec scale hs selected opponent eta theta past) field

theorem fareyHistoryLeaf_nonnegative {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α)
    (field : Fin m) (code : Fin ((fareyHistoryLeaf spec scale hs selected opponent eta theta heta htheta past field).cap + 1)) :
    0 ≤ (fareyHistoryLeaf spec scale hs selected opponent eta theta heta htheta past field).decode code.val := by
  change 0 ≤ FareyDirectBlockHistory.decode spec (scale field) code.val
  have hc : code.val ≤ rankCap spec.order := by have h := code.isLt; change code.val < rankCap spec.order + 1 at h; omega
  rw [FareyDirectBlockHistory.decode_valid spec _ _ hc]
  exact mul_nonneg (hs field) (decode_nonnegative spec code.val)

theorem fareyHistoryLeaf_zero {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) (field : Fin m) :
    (fareyHistoryLeaf spec scale hs selected opponent eta theta heta htheta past field).decode 0 = 0 := by
  change FareyDirectBlockHistory.decode spec (scale field) 0 = 0
  rw [FareyDirectBlockHistory.decode_valid spec _ _ (Nat.zero_le _), decode_zero, mul_zero]

def prepareFareyHistory {α : Type*} (n : ℕ) (spec : RankUniverse) (scale : Fin (n + 1) → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) (budget : ℚ) (hb : 0 ≤ budget) :
    ExactSizedDraw (n + 1) :=
  prepareAccessLeafComb n (fareyHistoryLeaf spec scale hs selected opponent eta theta heta htheta past)
    (fareyHistoryAccess spec scale hs selected opponent eta theta heta htheta past)
    (fareyHistoryLeaf_nonnegative spec scale hs selected opponent eta theta heta htheta past)
    (fareyHistoryLeaf_zero spec scale hs selected opponent eta theta heta htheta past) budget hb

theorem fareyHistoryLeaf_bid_eq {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) (field : Fin m) :
    fareyHistoryLeaf spec scale hs selected opponent eta theta heta htheta past field =
      genericLeaf (fun _ => rankCap spec.order) (ProductSecurityTrainer.bidDecoder (FareyImplicitTrainer.bids spec scale))
        (FareyImplicitTrainer.decoder_ordered spec scale hs) selected opponent eta theta heta htheta past field := by
  rw [fareyHistoryLeaf_eq]
  have he : (fun field => FareyDirectBlockHistory.decode spec (scale field)) =
      ProductSecurityTrainer.bidDecoder (FareyImplicitTrainer.bids spec scale) := by
    funext field
    exact FareyDirectBlockHistory.decoder_is_actual_bids spec scale field
  congr 1


theorem prepareLeafComb_data_congr (n : ℕ) (first second : Fin (n + 1) → ProposalLeaf) (he : first = second)
    (hnf : ∀ field (code : Fin ((first field).cap + 1)), 0 ≤ (first field).decode code.val)
    (hns : ∀ field (code : Fin ((second field).cap + 1)), 0 ≤ (second field).decode code.val)
    (hzf : ∀ field, (first field).decode 0 = 0) (hzs : ∀ field, (second field).decode 0 = 0)
    (budget : ℚ) (hb : 0 ≤ budget) : prepareLeafComb n first hnf hzf budget hb = prepareLeafComb n second hns hzs budget hb := by
  cases he
  rfl

theorem prepareFareyHistory_model {α : Type*} (n : ℕ) (spec : RankUniverse) (scale : Fin (n + 1) → ℚ)
    (hs : ∀ field, 0 ≤ scale field) (selected : List α → α → Fin (n + 1)) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2) (past : List α) (budget : ℚ) (hb : 0 ≤ budget)
    (hn : ∀ field (code : Fin (rankCap spec.order + 1)), 0 ≤
      ProductSecurityTrainer.bidDecoder (FareyImplicitTrainer.bids spec scale) field code.val)
    (hz : ∀ field, ProductSecurityTrainer.bidDecoder (FareyImplicitTrainer.bids spec scale) field 0 = 0) :
    (prepareFareyHistory n spec scale hs selected opponent eta theta heta htheta past budget hb).model =
      prepareLeafComb n (genericLeaf (fun _ => rankCap spec.order)
        (ProductSecurityTrainer.bidDecoder (FareyImplicitTrainer.bids spec scale))
        (FareyImplicitTrainer.decoder_ordered spec scale hs) selected opponent eta theta heta htheta past) hn hz budget hb := by
  unfold prepareFareyHistory
  rw [prepareAccessLeafComb_model]
  have he : fareyHistoryLeaf spec scale hs selected opponent eta theta heta htheta past =
      genericLeaf (fun _ => rankCap spec.order) (ProductSecurityTrainer.bidDecoder (FareyImplicitTrainer.bids spec scale))
        (FareyImplicitTrainer.decoder_ordered spec scale hs) selected opponent eta theta heta htheta past := by
    funext field
    exact fareyHistoryLeaf_bid_eq spec scale hs selected opponent eta theta heta htheta past field
  exact prepareLeafComb_data_congr n _ _ he _ _ _ _ budget hb

end Blotto.ImplicitLeafCounts

namespace Blotto.FareyImplicitTrainer
open ImplicitLeafCounts Farey ProductSecurityTrainer

structure DirectInput (fields : ℕ) where
  first : RankUniverse
  second : RankUniverse
  scaleA : Fin fields → ℚ
  scaleB : Fin fields → ℚ
  scaleA_nonnegative : ∀ field, 0 ≤ scaleA field
  scaleB_nonnegative : ∀ field, 0 ≤ scaleB field
  budgetA : ℚ
  budgetB : ℚ
  budgetA_nonnegative : 0 ≤ budgetA
  budgetB_nonnegative : 0 ≤ budgetB
  values : RationalFieldSelector fields
  eta : ℚ
  theta : ℚ
  eta_unit : 0 < eta ∧ eta ≤ 1/4
  theta_unit : 0 < theta ∧ theta ≤ 1/2

def DirectInput.trainer {m : ℕ} (input : DirectInput m) : ProductSecurityTrainer m :=
  create input.first input.second input.scaleA input.scaleB input.scaleA_nonnegative input.scaleB_nonnegative
    input.budgetA input.budgetB input.budgetA_nonnegative input.budgetB_nonnegative input.values
    input.eta input.theta input.eta_unit input.theta_unit

def DirectInput.config {m : ℕ} (input : DirectInput m) : input.trainer.ImplicitCodeConfig :=
  FareyImplicitTrainer.config input.first input.second input.scaleA input.scaleB input.scaleA_nonnegative input.scaleB_nonnegative
    input.budgetA input.budgetB input.budgetA_nonnegative input.budgetB_nonnegative input.values
    input.eta input.theta input.eta_unit input.theta_unit

def DirectInput.preparedA {n : ℕ} (input : DirectInput (n + 1)) (past : List (RawObservation (n + 1))) : ExactSizedDraw (n + 1) :=
  prepareFareyHistory n input.first input.scaleA input.scaleA_nonnegative rawSelected (fun _ x => x.2.1 x.2.2)
    input.eta input.theta input.eta_unit input.theta_unit past input.budgetA input.budgetA_nonnegative

def DirectInput.preparedB {n : ℕ} (input : DirectInput (n + 1)) (past : List (RawObservation (n + 1))) : ExactSizedDraw (n + 1) :=
  prepareFareyHistory n input.second input.scaleB input.scaleB_nonnegative rawSelected (fun _ x => x.1 x.2.2)
    input.eta input.theta input.eta_unit input.theta_unit past input.budgetB input.budgetB_nonnegative

theorem DirectInput.preparedA_model {n : ℕ} (input : DirectInput (n + 1)) (past : List (RawObservation (n + 1))) :
    (input.preparedA past).model = input.trainer.compactPreparedA input.config past := by
  exact prepareFareyHistory_model n input.first input.scaleA input.scaleA_nonnegative rawSelected (fun _ x => x.2.1 x.2.2)
    input.eta input.theta input.eta_unit input.theta_unit past input.budgetA input.budgetA_nonnegative _ _

theorem DirectInput.preparedB_model {n : ℕ} (input : DirectInput (n + 1)) (past : List (RawObservation (n + 1))) :
    (input.preparedB past).model = input.trainer.compactPreparedB input.config past := by
  exact prepareFareyHistory_model n input.second input.scaleB input.scaleB_nonnegative rawSelected (fun _ x => x.1 x.2.2)
    input.eta input.theta input.eta_unit input.theta_unit past input.budgetB input.budgetB_nonnegative _ _

theorem DirectInput.preparedA_budget {n : ℕ} (input : DirectInput (n + 1)) (past : List (RawObservation (n + 1))) :
    (input.preparedA past).budget = input.budgetA := by
  change (input.preparedA past).model.budget = _
  rw [input.preparedA_model]
  rfl

theorem DirectInput.preparedB_budget {n : ℕ} (input : DirectInput (n + 1)) (past : List (RawObservation (n + 1))) :
    (input.preparedB past).budget = input.budgetB := by
  change (input.preparedB past).model.budget = _
  rw [input.preparedB_model]
  rfl

theorem DirectInput.preparedA_target_mean {n : ℕ} (input : DirectInput (n + 1)) (past : List (RawObservation (n + 1)))
    (test : (Fin (n + 1) → ℚ) → ℝ) :
    (input.preparedA past).model.targetKernel.mean test = (input.trainer.rawPreparedA past).rationalTargetKernel.mean test := by
  rw [input.preparedA_model]
  exact input.trainer.compactPreparedA_target_mean input.config past test

theorem DirectInput.preparedB_target_mean {n : ℕ} (input : DirectInput (n + 1)) (past : List (RawObservation (n + 1)))
    (test : (Fin (n + 1) → ℚ) → ℝ) :
    (input.preparedB past).model.targetKernel.mean test = (input.trainer.rawPreparedB past).rationalTargetKernel.mean test := by
  rw [input.preparedB_model]
  exact input.trainer.compactPreparedB_target_mean input.config past test

theorem DirectInput.preparedA_native_mean_error {n : ℕ} (input : DirectInput (n + 1)) (past : List (RawObservation (n + 1)))
    (epsilon : ℚ) (he : 0 < epsilon) (test : (Fin (n + 1) → ℚ) → ℝ) (hTest : ∀ row, 0 ≤ test row ∧ test row ≤ 1) :
    |((input.preparedA past).nativeKernel epsilon).mean test - (input.trainer.rawPreparedA past).rationalTargetKernel.mean test| ≤ (epsilon : ℝ) := by
  have h := (input.preparedA past).nativeKernel_close epsilon he test hTest
  rw [input.preparedA_target_mean past test] at h
  exact h

theorem DirectInput.preparedB_native_mean_error {n : ℕ} (input : DirectInput (n + 1)) (past : List (RawObservation (n + 1)))
    (epsilon : ℚ) (he : 0 < epsilon) (test : (Fin (n + 1) → ℚ) → ℝ) (hTest : ∀ row, 0 ≤ test row ∧ test row ≤ 1) :
    |((input.preparedB past).nativeKernel epsilon).mean test - (input.trainer.rawPreparedB past).rationalTargetKernel.mean test| ≤ (epsilon : ℝ) := by
  have h := (input.preparedB past).nativeKernel_close epsilon he test hTest
  rw [input.preparedB_target_mean past test] at h
  exact h

def DirectInput.withAccuracy {m : ℕ} (input : DirectInput m) (epsilon : ℚ)
    (he : 0 < epsilon ∧ epsilon ≤ 1) : DirectInput m :=
  { input with
    eta := epsilon / 2048
    theta := (epsilon / 2048) * epsilon / 32768
    eta_unit := (input.trainer.withAccuracy epsilon he).eta_unit
    theta_unit := (input.trainer.withAccuracy epsilon he).theta_unit }

theorem DirectInput.withAccuracy_trainer {m : ℕ} (input : DirectInput m) (epsilon : ℚ)
    (he : 0 < epsilon ∧ epsilon ≤ 1) : (input.withAccuracy epsilon he).trainer = input.trainer.withAccuracy epsilon he := rfl

theorem DirectInput.withAccuracy_config {m : ℕ} (input : DirectInput m) (epsilon : ℚ)
    (he : 0 < epsilon ∧ epsilon ≤ 1) : (input.withAccuracy epsilon he).config = input.config.withAccuracy epsilon he := rfl

end Blotto.FareyImplicitTrainer
