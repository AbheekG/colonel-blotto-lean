import Blotto.GeneralPaperEqualRealCompaction

/-! Complete grouped-equal real-model preparation after the dyadic exponent
is available. Positive rounding, lengths, packing, routes, segment formulas,
positive compaction and midpoint power execute once. No bit-only sizing or
categorical integer/Boolean construction is on this path. -/
namespace Blotto.GeneralPaperEqualRealPreparation
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualRealCache (Cache project)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def segments {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (p : RationalTerminalPacking (terminal v small)) : PreparedSegmentDescriptor (lottery v small) × ℕ :=
  let actual := GeneralPaperEqualRealSegmentFactory.prepare
    (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction v small))
    p.groups.data.size p.groups.size (terminal v small).groups_count
  (cast (congrArg PreparedSegmentDescriptor (GeneralPaperEqualNativeSegmentPreparation.source_eq v small p)) actual.1, actual.2)

theorem segments_work {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (p : RationalTerminalPacking (terminal v small)) : (segments v small p).2 ≤ 2097216 := by
  unfold segments
  dsimp only
  exact GeneralPaperEqualRealSegmentFactory.prepare_work _ _ _ _

def make {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (lengths : FixedArrayTable n ℚ) (hL : ∀ j, lengths.read j = (terminal v small).length j)
    (k : ℕ) (budget : ℚ) : Cache (terminal v small).partition (lottery v small) × ℕ :=
  let items := GeneralPaperEqualRouteConstruction.indices lengths.data.size lengths.size
  let hItems : items = (terminal v small).uniformItems :=
    (GeneralPaperEqualRouteConstruction.indices_eq _ _).trans (GeneralPaperEqualPreparationPrefix.uniform_items v small).symm
  let packed := GeneralPaperEqualRealPrefix.prepare (terminal v small) lengths hL items hItems
  let routes := GeneralPaperEqualRealRoutes.prepare packed.1 lengths hL
  let full := segments v small packed.1
  let compacted := GeneralPaperEqualRealCompaction.run full.1
  let power := GeneralPaperPhysicalPowerArithmetic.run 2 (k + 5)
  let cache : Cache (terminal v small).partition (lottery v small) :=
    ⟨routes.1, compacted.1, k + 5, power.1, GeneralPaperPhysicalPowerArithmetic.data 2 (k + 5), budget⟩
  (cache, packed.2 + routes.2 + full.2 + compacted.2 + power.2 + 8 * (n + 1) + 128)

theorem make_work {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (lengths : FixedArrayTable n ℚ) (hL : ∀ j, lengths.read j = (terminal v small).length j)
    (k : ℕ) (budget : ℚ) :
    (make v small lengths hL k budget).2 ≤ 512 * (n + 1) + 64 * (binaryWordWidth (k + 5) + 1) ^ 2 + 2150000 := by
  let packed := GeneralPaperEqualRealPrefix.prepare (terminal v small) lengths hL (List.finRange n)
    (GeneralPaperEqualPreparationPrefix.uniform_items v small).symm
  have hp := GeneralPaperEqualRealPrefix.prepare_work (terminal v small) lengths hL (List.finRange n)
    (GeneralPaperEqualPreparationPrefix.uniform_items v small).symm
  have hr := GeneralPaperEqualRealRoutes.work packed.1 lengths
  have hs := segments_work v small packed.1
  have hc := GeneralPaperEqualRealCompaction.work (segments v small packed.1).1
  have hw := GeneralPaperPhysicalPowerArithmetic.work 2 (k + 5)
  change (GeneralPaperEqualRealCompaction.run (segments v small packed.1).1).2 ≤ 512 * (9 + 1) ^ 2 at hc
  change packed.2 ≤ _ at hp
  dsimp only [make, GeneralPaperEqualRealRoutes.prepare]
  simp only [GeneralPaperEqualRouteConstruction.indices_eq]
  change packed.2 + (GeneralPaperEqualRealRoutes.run packed.1 lengths).2 +
    (segments v small packed.1).2 + (GeneralPaperEqualRealCompaction.run (segments v small packed.1).1).2 +
    (GeneralPaperPhysicalPowerArithmetic.run 2 (k + 5)).2 + 8 * (n + 1) + 128 ≤ _
  omega

def run {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 k values v hv).weight j ≤ 1) (budget : ℚ) :
    Cache (terminal (rounded false model 1 k values v hv) small).partition
      (lottery (rounded false model 1 k values v hv) small) × ℕ :=
  let raw := GeneralPaperValueRoundingPaperContract.run false model 1 128 k values
  let hp := GeneralPaperValueRoundingPaperContract.positivity false model 1 128 k (by decide) values v hv
  let r := GeneralPaperNativeRationalValues.selector raw.1.2 hp.1 raw.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum false model 1 128 k values)
  let lengths := GeneralPaperEqualRealPrefix.lengths raw.1.1 raw.1.2
  let hL : ∀ j, lengths.1.read j = (terminal r small).length j := by
    intro j
    rw [GeneralPaperEqualRealPrefix.lengths_data, FixedArrayTable.read_ofFn]
    rfl
  let actual := make r small lengths.1 hL k budget
  (actual.1, raw.2 + lengths.2 + actual.2 + 128)

theorem data {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run model k values v hv small budget).1 =
      project (GeneralPaperEqualNativeCache.prepare false model 1 k values v hv small budget) := by
  apply GeneralPaperEqualRealCache.unique
  · rfl
  · rfl

def bound (n k : ℕ) : ℕ :=
  GeneralPaperValueRoundingDriver.arithmeticProfile n (GeneralPaperValueRoundingPaperContract.scale 128 n k) +
    1024 * (n + 1) + 128 * (binaryWordWidth (k + 5) + 1) ^ 2 + 2150528

theorem work {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run model k values v hv small budget).2 ≤ bound n k := by
  have hRound := GeneralPaperValueRoundingPaperContract.arithmetic_work model 128 k values v hv
  let raw := GeneralPaperValueRoundingPaperContract.run false model 1 128 k values
  have hLength := GeneralPaperEqualRealPrefix.lengths_work raw.1.1 raw.1.2
  have hk := Nat.pow_le_pow_left (Nat.add_le_add_right (binaryWordWidth_mono (by omega : k ≤ k + 5)) 1) 2
  have hTail : ∀ (lengths : FixedArrayTable n ℚ)
      (hL : ∀ j, lengths.read j = (terminal (rounded false model 1 k values v hv) small).length j),
      (make (rounded false model 1 k values v hv) small lengths hL k budget).2 ≤
        512 * (n + 1) + 64 * (binaryWordWidth (k + 5) + 1) ^ 2 + 2150000 :=
    fun lengths hL => make_work _ small lengths hL k budget
  unfold run bound
  dsimp only
  have ht := hTail (GeneralPaperEqualRealPrefix.lengths raw.1.1 raw.1.2).1 (by
    intro j
    rw [GeneralPaperEqualRealPrefix.lengths_data, FixedArrayTable.read_ofFn]
    rfl)
  change raw.2 + (GeneralPaperEqualRealPrefix.lengths raw.1.1 raw.1.2).2 +
    (make _ small (GeneralPaperEqualRealPrefix.lengths raw.1.1 raw.1.2).1 _ k budget).2 + 128 ≤ _
  change raw.2 ≤ _ at hRound
  omega

end Blotto.GeneralPaperEqualRealPreparation
