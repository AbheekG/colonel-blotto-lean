import Blotto.GeneralPaperEpochNumeratorEnvelope
import Blotto.GeneralPaperAdaptiveEpoch

/-! Four blocks from one pre-update state. Each block queries its own level
array once, scans its integer prefixes once, and retains the resulting pair.
-/
namespace Blotto.GeneralPaperEpochSnapshotPrice
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def block (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    {k : ℕ} (levels : Summary k) : Block k × ℕ :=
  let numerators := GeneralPaperEpochNumeratorArrayPrice.run bits index price W c levels
  let cached := GeneralPaperEpochPrefixPrice.run bits index (if bits then price else fun _ => 1) W numerators.1
  (⟨numerators.1,cached.1⟩,numerators.2+cached.2+64*W)

def blockProfile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  GeneralPaperEpochNumeratorArrayPrice.profile price W m lambda k Qv s+
    GeneralPaperEpochPrefixPrice.profile price W s (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*W

def arithmeticBlockProfile (m lambda k Qv : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  GeneralPaperEpochNumeratorArrayPrice.arithmeticProfile m lambda k Qv s+
    GeneralPaperEpochPrefixPrice.arithmeticProfile s+64

theorem block_data (bits : Bool) (index price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : Summary k) : (block bits index price W c levels).1=GeneralPaperEpochSnapshot.block c.powers levels := by
  unfold block GeneralPaperEpochSnapshot.block
  dsimp only
  rw [GeneralPaperEpochPrefixPrice.data,GeneralPaperEpochNumeratorArrayPrice.data bits index price W m lambda k Qv c hc]

theorem block_bit_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : Summary k) (hLevels : ∀ r,levels.read r≤c.controls.precision.levelBound) :
    (block true (fun w => w) price W c levels).2≤blockProfile price W m lambda k Qv := by
  let numerators := GeneralPaperEpochNumeratorArrayPrice.run true (fun w => w) price W c levels
  have hn := GeneralPaperEpochNumeratorArrayPrice.bit_work price hMono W m lambda k Qv c hc levels hLevels
  have ht := GeneralPaperEpochNumeratorEnvelope.returned_total true (fun w => w) price W m lambda k Qv c hc levels hLevels
  have hw : 1+binaryWordWidth ((GeneralPaperSourceParameters.prepare k).summarySize*(4*c.powers.format.unit))≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    rw [hc]
    exact GeneralPaperEpochNumeratorEnvelope.total_word m lambda k Qv
  have hp := GeneralPaperEpochPrefixPrice.bit_work price hMono W _ _ numerators.1 ht hw
  exact Nat.add_le_add_right (Nat.add_le_add hn hp) _

theorem block_arithmetic_work (price : ℕ → ℕ) (m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : Summary k) (hLevels : ∀ r,levels.read r≤c.controls.precision.levelBound) :
    (block false (fun _ => 1) price 1 c levels).2≤arithmeticBlockProfile m lambda k Qv := by
  have hn := GeneralPaperEpochNumeratorArrayPrice.arithmetic_work price m lambda k Qv c hc levels hLevels
  have hp := GeneralPaperEpochPrefixPrice.arithmetic_work (GeneralPaperEpochNumeratorArrayPrice.run false (fun _ => 1) price 1 c levels).1
  exact Nat.add_le_add_right (Nat.add_le_add hn hp) _

def take (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    {k : ℕ} (state : State k) : Snapshot k × ℕ :=
  let p := block bits index price W c state.pOccurrences
  let q := block bits index price W c state.qOccurrences
  let l := block bits index price W c state.lambdaOccurrences
  let u := block bits index price W c state.muOccurrences
  (⟨p.1,q.1,l.1,u.1⟩,p.2+q.2+l.2+u.2+128*W)

def profile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ := 4*blockProfile price W m lambda k Qv+128*W
def arithmeticProfile (m lambda k Qv : ℕ) : ℕ := 4*arithmeticBlockProfile m lambda k Qv+128

theorem data (bits : Bool) (index price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (state : State k) : (take bits index price W c state).1=GeneralPaperEpochSnapshot.take c.powers state := by
  unfold take GeneralPaperEpochSnapshot.take
  dsimp only
  rw [block_data bits index price W m lambda k Qv c hc,block_data bits index price W m lambda k Qv c hc,
    block_data bits index price W m lambda k Qv c hc,block_data bits index price W m lambda k Qv c hc]

theorem four_prices (a b c d C E : ℕ) (ha : a≤C) (hb : b≤C) (hc : c≤C) (hd : d≤C) :
    a+b+c+d+E≤4*C+E := by omega

theorem bit_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (state : State k) (hState : Bounded state c.controls.precision.levelBound) :
    (take true (fun w => w) price W c state).2≤profile price W m lambda k Qv :=
  four_prices _ _ _ _ _ _ (block_bit_work price hMono W m lambda k Qv c hc _ hState.1)
    (block_bit_work price hMono W m lambda k Qv c hc _ hState.2.1)
    (block_bit_work price hMono W m lambda k Qv c hc _ hState.2.2.1)
    (block_bit_work price hMono W m lambda k Qv c hc _ hState.2.2.2.1)

theorem arithmetic_work (price : ℕ → ℕ) (m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (state : State k) (hState : Bounded state c.controls.precision.levelBound) :
    (take false (fun _ => 1) price 1 c state).2≤arithmeticProfile m lambda k Qv :=
  four_prices _ _ _ _ _ _ (block_arithmetic_work price m lambda k Qv c hc _ hState.1)
    (block_arithmetic_work price m lambda k Qv c hc _ hState.2.1)
    (block_arithmetic_work price m lambda k Qv c hc _ hState.2.2.1)
    (block_arithmetic_work price m lambda k Qv c hc _ hState.2.2.2.1)

theorem same_data (price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (state : State k) :
    (take true (fun w => w) price W c state).1=(take false (fun _ => 1) price 1 c state).1 := by
  rw [data true (fun w => w) price W m lambda k Qv c hc,data false (fun _ => 1) price 1 m lambda k Qv c hc]

end Blotto.GeneralPaperEpochSnapshotPrice
