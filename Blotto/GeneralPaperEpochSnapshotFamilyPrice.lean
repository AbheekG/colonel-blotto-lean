import Blotto.GeneralPaperEpochSnapshotPrice

/-! One indexed pass materializes all battlefield snapshots. Field loads,
four-block records, array writes and index/control operations are included.
-/
namespace Blotto.GeneralPaperEpochSnapshotFamilyPrice
open GeneralPaperAdaptiveEpoch GeneralPaperEpochFieldState GeneralPaperEpochSnapshot
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def element {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (fields : Fields m k) (j : Fin m) : Snapshot k × ℕ :=
  let snapshot := GeneralPaperEpochSnapshotPrice.take bits index price W c (fields.read j)
  (snapshot.1,snapshot.2+32*W)

def run {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (fields : Fields m k) : FixedArrayTable m (Snapshot k) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W) (element bits index price W c fields)

def profile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  m*(GeneralPaperEpochSnapshotPrice.profile price W m lambda k Qv+32*W)+44*(m+1)*arrayWord W m

def arithmeticProfile (m lambda k Qv : ℕ) : ℕ :=
  m*(GeneralPaperEpochSnapshotPrice.arithmeticProfile m lambda k Qv+32)+44*(m+1)

theorem element_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (fields : Fields m k) (j : Fin m) :
    (element bits index price W c fields j).1=GeneralPaperEpochSnapshot.take c.powers (fields.read j) :=
  GeneralPaperEpochSnapshotPrice.data bits index price W m lambda k Qv c hc (fields.read j)

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (fields : Fields m k) : (run bits index price W c fields).1=GeneralPaperAdaptiveEpoch.snapshots c.powers fields := by
  rw [run,PaperIndexedArrayConstruction.run_data]
  unfold GeneralPaperAdaptiveEpoch.snapshots
  congr 1
  funext j
  exact element_data bits index price W lambda Qv c hc fields j

theorem bit_work {m k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (fields : Fields m k) (hFields : ∀ j,Bounded (fields.read j) c.controls.precision.levelBound) :
    (run true (fun w => w) price W c fields).2≤profile price W m lambda k Qv :=
  GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) _ (element true (fun w => w) price W c fields)
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
    (fun j => Nat.add_le_add_right (GeneralPaperEpochSnapshotPrice.bit_work price hMono W m lambda k Qv c hc _ (hFields j)) _)

theorem arithmetic_work {m k : ℕ} (price : ℕ → ℕ) (lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (fields : Fields m k) (hFields : ∀ j,Bounded (fields.read j) c.controls.precision.levelBound) :
    (run false (fun _ => 1) price 1 c fields).2≤arithmeticProfile m lambda k Qv := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 _ (element false (fun _ => 1) price 1 c fields)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (fun j => Nat.add_le_add_right (GeneralPaperEpochSnapshotPrice.arithmetic_work price m lambda k Qv c hc _ (hFields j)) _)
  simpa only [run,Bool.false_eq_true,ite_false,Nat.mul_one,arithmeticProfile] using h

theorem same_data {m k : ℕ} (price : ℕ → ℕ) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (fields : Fields m k) :
    (run true (fun w => w) price W c fields).1=(run false (fun _ => 1) price 1 c fields).1 := by
  rw [data true (fun w => w) price W lambda Qv c hc,data false (fun _ => 1) price 1 lambda Qv c hc]

theorem every_prefix {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (fields : Fields m k) (count : ℕ) (hCount : count≤m) :
    (PaperIndexedArrayConstruction.fill index (if bits then arrayWord W m else W)
      (element bits index price W c fields) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperEpochSnapshotFamilyPrice
