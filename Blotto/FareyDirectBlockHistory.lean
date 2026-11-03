import Blotto.FareyDirectCuts
import Blotto.FareyImplicitTrainer
import Blotto.GenericImplicitBlockHistory

/-! Actual sparse rounded Farey field updates use direct Farey cuts, without
decoder binary search. Positive scales divide the threshold; zero scales use
the exact constant-bid weak/strict condition. Complete raw observation histories
refine the retained generic block/field process. The access/update observer is
an arithmetic-path model; sampler-cap replacement and full bit prices remain
separate. -/

namespace Blotto.FareyDirectBlockHistory
open Farey ImplicitLeafCounts

def decode (spec : RankUniverse) (scale : ℚ) (code : ℕ) : ℚ :=
  if code < rankCap spec.order + 1 then scale * spec.decode code else 0

def aboveZero (strict : Bool) (threshold : ℚ) : Bool :=
  if strict then decide (threshold < 0) else decide (threshold ≤ 0)

def first (spec : RankUniverse) (scale : ℚ) (strict : Bool) (threshold : ℚ) : ℕ × ℕ :=
  if 0 < scale then
    let cut := directFirst spec strict (threshold / scale)
    (cut.1, cut.2 + 1)
  else if aboveZero strict threshold then (0, 0) else (rankCap spec.order + 1, 0)

theorem decode_valid (spec : RankUniverse) (scale : ℚ) (code : ℕ) (hc : code ≤ rankCap spec.order) :
    decode spec scale code = scale * spec.decode code := by
  simp only [decode, show code < rankCap spec.order + 1 by omega, ite_true]

theorem decode_ordered (spec : RankUniverse) (scale : ℚ) (hs : 0 ≤ scale) :
    MonotoneResourceCuts.MonotoneDecode (rankCap spec.order) (decode spec scale) := by
  intro i j hij hj
  rw [decode_valid spec scale i (hij.trans hj), decode_valid spec scale j hj]
  exact mul_le_mul_of_nonneg_left (decode_mono spec i j hij hj) hs

theorem scaled_above (strict : Bool) (scale threshold bid : ℚ) (hs : 0 < scale) :
    Above strict threshold (scale * bid) ↔ Above strict (threshold / scale) bid := by
  cases strict <;> unfold Above <;> dsimp
  · rw [div_le_iff₀ hs, mul_comm bid scale]
  · rw [div_lt_iff₀ hs, mul_comm bid scale]

theorem aboveZero_true (strict : Bool) (threshold : ℚ) : aboveZero strict threshold = true ↔ Above strict threshold 0 := by
  cases strict <;> simp [aboveZero, Above]

theorem first_bound (spec : RankUniverse) (scale : ℚ) (strict : Bool) (threshold : ℚ) :
    (first spec scale strict threshold).1 ≤ rankCap spec.order + 1 := by
  unfold first
  split_ifs
  · exact directFirst_bound spec strict _
  · omega
  · exact le_rfl

theorem first_queries (spec : RankUniverse) (scale : ℚ) (strict : Bool) (threshold : ℚ) :
    (first spec scale strict threshold).2 ≤ 12 * binaryWordWidth spec.order + 3 := by
  unfold first
  split_ifs
  · have h := directFirst_queries spec strict (threshold / scale)
    dsimp only
    omega
  · omega
  · omega

theorem first_contract (spec : RankUniverse) (scale : ℚ) (hs : 0 ≤ scale) (strict : Bool) (threshold : ℚ)
    (code : ℕ) (hc : code ≤ rankCap spec.order) :
    Above strict threshold (decode spec scale code) ↔ (first spec scale strict threshold).1 ≤ code := by
  rw [decode_valid spec scale code hc]
  unfold first
  by_cases hp : 0 < scale
  · simp only [hp, ite_true]
    rw [scaled_above strict scale threshold (spec.decode code) hp]
    exact directFirst_contract spec strict _ code hc
  · have hz : scale = 0 := by linarith
    simp only [hp, ite_false]
    rw [hz]
    simp only [zero_mul]
    by_cases ha : aboveZero strict threshold = true
    · simp only [ha, ite_true]
      exact ⟨fun _ => Nat.zero_le code, fun _ => (aboveZero_true strict threshold).mp ha⟩
    · simp only [ha, Bool.false_eq_true, ite_false]
      constructor
      · intro h
        exact False.elim (ha ((aboveZero_true strict threshold).mpr h))
      · intro h
        omega

def binaryFirst (spec : RankUniverse) (scale : ℚ) (strict : Bool) (threshold : ℚ) : ℕ × ℕ :=
  if strict then MonotoneResourceCuts.strict (rankCap spec.order) (decode spec scale) threshold
    else MonotoneResourceCuts.weak (rankCap spec.order) (decode spec scale) threshold

theorem binaryFirst_contract (spec : RankUniverse) (scale : ℚ) (hs : 0 ≤ scale) (strict : Bool) (threshold : ℚ) :
    (binaryFirst spec scale strict threshold).1 ≤ rankCap spec.order + 1 ∧
      ∀ code ≤ rankCap spec.order, Above strict threshold (decode spec scale code) ↔
        (binaryFirst spec scale strict threshold).1 ≤ code := by
  cases strict
  · exact MonotoneResourceCuts.weak_contract _ _ (decode_ordered spec scale hs) threshold
  · exact MonotoneResourceCuts.strict_contract _ _ (decode_ordered spec scale hs) threshold

theorem first_eq_binary (spec : RankUniverse) (scale : ℚ) (hs : 0 ≤ scale) (strict : Bool) (threshold : ℚ) :
    (first spec scale strict threshold).1 = (binaryFirst spec scale strict threshold).1 := by
  have hn := first_bound spec scale strict threshold
  have ho := binaryFirst_contract spec scale hs strict threshold
  apply le_antisymm
  · by_cases he : (binaryFirst spec scale strict threshold).1 = rankCap spec.order + 1
    · rwa [he]
    · have hc : (binaryFirst spec scale strict threshold).1 ≤ rankCap spec.order := by omega
      exact (first_contract spec scale hs strict threshold _ hc).mp ((ho.2 _ hc).mpr le_rfl)
  · by_cases he : (first spec scale strict threshold).1 = rankCap spec.order + 1
    · rw [he]
      exact ho.1
    · have hc : (first spec scale strict threshold).1 ≤ rankCap spec.order := by omega
      exact (ho.2 _ hc).mp ((first_contract spec scale hs strict threshold _ hc).mpr le_rfl)

theorem zero_scale_loss (opponent : ℚ) (code : ℕ) (spec : RankUniverse) :
    SparseMW.rationalShare opponent (decode spec 0 code) =
      if 0 < opponent then 1 else if opponent = 0 then 1/2 else 0 := by
  have hz : decode spec 0 code = 0 := by unfold decode; split_ifs <;> simp
  rw [hz]
  unfold SparseMW.rationalShare
  rfl

def update (spec : RankUniverse) (scale opponent eta theta : ℚ) (old : List Block) : List Block :=
  updateBlocks (first spec scale false opponent).1 (first spec scale true opponent).1 eta theta old

def updateWithWork (spec : RankUniverse) (scale opponent eta theta : ℚ) (old : List Block) : List Block × ℕ :=
  let weak := first spec scale false opponent
  let strict := first spec scale true opponent
  (updateBlocks weak.1 strict.1 eta theta old, weak.2 + strict.2 + updateVisits weak.1 strict.1 old)

theorem updateWithWork_output (spec : RankUniverse) (scale opponent eta theta : ℚ) (old : List Block) :
    (updateWithWork spec scale opponent eta theta old).1 = update spec scale opponent eta theta old := rfl

theorem updateWithWork_bound (spec : RankUniverse) (scale opponent eta theta : ℚ) (old : List Block) :
    (updateWithWork spec scale opponent eta theta old).2 ≤ 24 * binaryWordWidth spec.order + 3 * old.length + 9 := by
  have hw := first_queries spec scale false opponent
  have hs := first_queries spec scale true opponent
  have hu := updateVisits_bound old ((first spec scale false opponent).1 : ℤ) ((first spec scale true opponent).1 : ℤ)
  unfold updateWithWork
  dsimp only
  omega

def blocks {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ) : List α → Fin m → List Block
  | [] => fun _ => [⟨0, rankCap spec.order, 1⟩]
  | x :: past =>
    let old := blocks spec scale selected opponent eta theta past
    let field := selected past x
    Function.update old field (update spec (scale field) (opponent past x) eta theta (old field))

theorem blocks_eq_generic {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ) (past : List α) :
    blocks spec scale selected opponent eta theta past =
      genericBlocks (fun _ => rankCap spec.order) (fun field => decode spec (scale field)) selected opponent eta theta past := by
  induction past with
  | nil => rfl
  | cons x past ih =>
    simp only [blocks, genericBlocks, update, ih]
    rw [first_eq_binary spec _ (hs _) false, first_eq_binary spec _ (hs _) true]
    rfl

theorem blocks_refines {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ) (past : List α)
    (field : Fin m) (code : Fin (rankCap spec.order + 1)) :
    labelMass (blocks spec scale selected opponent eta theta past field) code.val =
      genericFields (fun _ => rankCap spec.order) (fun field => decode spec (scale field)) selected opponent eta theta past field code := by
  rw [blocks_eq_generic spec scale hs selected opponent eta theta past]
  exact genericBlocks_refines _ _ (fun field => decode_ordered spec _ (hs field)) _ _ _ _ _ field code

theorem blocks_partition {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ) (past : List α) (field : Fin m) :
    Partition (rankCap spec.order) (blocks spec scale selected opponent eta theta past field) := by
  rw [blocks_eq_generic spec scale hs selected opponent eta theta past]
  exact genericBlocks_partition (fun _ => rankCap spec.order) (fun field => decode spec (scale field))
    selected opponent eta theta past field

theorem blocks_positive {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ)
    (heta : 0 < eta ∧ eta ≤ 1/4) (htheta : 0 < theta ∧ theta ≤ 1/2) (past : List α) (field : Fin m) :
    Positive (blocks spec scale selected opponent eta theta past field) := by
  rw [blocks_eq_generic spec scale hs selected opponent eta theta past]
  exact genericBlocks_positive _ _ _ _ _ _ heta htheta _ field

theorem blocks_length {α : Type*} {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hs : ∀ field, 0 ≤ scale field)
    (selected : List α → α → Fin m) (opponent : List α → α → ℚ) (eta theta : ℚ) (past : List α) (field : Fin m) :
    (blocks spec scale selected opponent eta theta past field).length ≤ 1 + 2 * genericCount selected past field := by
  rw [blocks_eq_generic spec scale hs selected opponent eta theta past]
  exact genericBlocks_length _ _ _ _ _ _ _ field

theorem decoder_is_actual_bids {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (field : Fin m) :
    decode spec (scale field) = ProductSecurityTrainer.bidDecoder (FareyImplicitTrainer.bids spec scale) field := by
  funext code
  unfold decode ProductSecurityTrainer.bidDecoder FareyImplicitTrainer.bids
  split_ifs <;> rfl

end Blotto.FareyDirectBlockHistory
