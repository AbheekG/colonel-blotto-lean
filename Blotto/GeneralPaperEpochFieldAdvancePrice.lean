import Blotto.GeneralPaperEpochLevelPrice
import Blotto.GeneralPaperEpochFieldState

/-! All eight level additions reuse the same retained plan and deltas.
No delta is regenerated and no prefix or power cache is rebuilt here.
-/
namespace Blotto.GeneralPaperEpochFieldAdvancePrice
open GeneralPaperEpochFieldState
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def total (a b c d e f g h : ℕ) : ℕ := a+b+c+d+e+f+g+h

theorem total_mono (a b c d e f g h A B C D E F G H : ℕ)
    (ha : a≤A) (hb : b≤B) (hc : c≤C) (hd : d≤D) (he : e≤E) (hf : f≤F) (hg : g≤G) (hh : h≤H) :
    total a b c d e f g h≤total A B C D E F G H := by unfold total; omega

def run {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (state : State k) (delta : Deltas state) : State k × ℕ :=
  let p := GeneralPaperEpochLevelPrice.run bits index price W state.pOccurrences delta.pOccurrences
  let q := GeneralPaperEpochLevelPrice.run bits index price W state.qOccurrences delta.qOccurrences
  let l := GeneralPaperEpochLevelPrice.run bits index price W state.lambdaOccurrences delta.lambdaOccurrences
  let u := GeneralPaperEpochLevelPrice.run bits index price W state.muOccurrences delta.muOccurrences
  let pc := GeneralPaperEpochLevelPrice.run bits index price W state.pCells delta.pCells
  let qc := GeneralPaperEpochLevelPrice.run bits index price W state.qCells delta.qCells
  let lc := GeneralPaperEpochLevelPrice.run bits index price W state.lambdaCells delta.lambdaCells
  let uc := GeneralPaperEpochLevelPrice.run bits index price W state.muCells delta.muCells
  (⟨state.plan,p.1,q.1,l.1,u.1,pc.1,qc.1,lc.1,uc.1⟩,total p.2 q.2 l.2 u.2 pc.2 qc.2 lc.2 uc.2+256*W)

def profile {k : ℕ} (price : ℕ → ℕ) (W m lambda Qv : ℕ) (state : State k) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let P := GeneralPaperEpochLevelPrice.profile price W m lambda k Qv
  total (P s) (P s) (P s) (P s) (P state.plan.pCells.partition.count) (P state.plan.qCells.partition.count)
    (P state.plan.lambdaCells.partition.count) (P state.plan.muCells.partition.count)+256*W

def arithmeticProfile {k : ℕ} (state : State k) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let P := GeneralPaperEpochLevelPrice.arithmeticProfile
  total (P s) (P s) (P s) (P s) (P state.plan.pCells.partition.count) (P state.plan.qCells.partition.count)
    (P state.plan.lambdaCells.partition.count) (P state.plan.muCells.partition.count)+256

theorem data {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (state : State k) (delta : Deltas state) :
    (run bits index price W state delta).1=advance state delta := by
  unfold run advance
  dsimp only
  simp only [GeneralPaperEpochLevelPrice.data]

theorem bit_work {k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv : ℕ)
    (state : State k) (delta : Deltas state) (hState : Bounded state (GeneralPaperPowerPrecision.levelBound lambda k))
    (hDelta : delta.Bounded (8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) :
    (run true (fun w => w) price W state delta).2≤profile price W m lambda Qv state := by
  exact Nat.add_le_add_right (total_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (GeneralPaperEpochLevelPrice.bit_work price hMono W m lambda k Qv _ _ hState.1 hDelta.1)
    (GeneralPaperEpochLevelPrice.bit_work price hMono W m lambda k Qv _ _ hState.2.1 hDelta.2.1)
    (GeneralPaperEpochLevelPrice.bit_work price hMono W m lambda k Qv _ _ hState.2.2.1 hDelta.2.2.1)
    (GeneralPaperEpochLevelPrice.bit_work price hMono W m lambda k Qv _ _ hState.2.2.2.1 hDelta.2.2.2.1)
    (GeneralPaperEpochLevelPrice.bit_work price hMono W m lambda k Qv _ _ hState.2.2.2.2.1 hDelta.2.2.2.2.1)
    (GeneralPaperEpochLevelPrice.bit_work price hMono W m lambda k Qv _ _ hState.2.2.2.2.2.1 hDelta.2.2.2.2.2.1)
    (GeneralPaperEpochLevelPrice.bit_work price hMono W m lambda k Qv _ _ hState.2.2.2.2.2.2.1 hDelta.2.2.2.2.2.2.1)
    (GeneralPaperEpochLevelPrice.bit_work price hMono W m lambda k Qv _ _ hState.2.2.2.2.2.2.2 hDelta.2.2.2.2.2.2.2)) _

theorem arithmetic_work {k : ℕ} (state : State k) (delta : Deltas state) :
    (run false (fun _ => 1) (fun _ => 1) 1 state delta).2≤arithmeticProfile state := by
  exact Nat.add_le_add_right (total_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (GeneralPaperEpochLevelPrice.arithmetic_work state.pOccurrences delta.pOccurrences)
    (GeneralPaperEpochLevelPrice.arithmetic_work state.qOccurrences delta.qOccurrences)
    (GeneralPaperEpochLevelPrice.arithmetic_work state.lambdaOccurrences delta.lambdaOccurrences)
    (GeneralPaperEpochLevelPrice.arithmetic_work state.muOccurrences delta.muOccurrences)
    (GeneralPaperEpochLevelPrice.arithmetic_work state.pCells delta.pCells)
    (GeneralPaperEpochLevelPrice.arithmetic_work state.qCells delta.qCells)
    (GeneralPaperEpochLevelPrice.arithmetic_work state.lambdaCells delta.lambdaCells)
    (GeneralPaperEpochLevelPrice.arithmetic_work state.muCells delta.muCells)) _

theorem same_data {k : ℕ} (price : ℕ → ℕ) (W : ℕ) (state : State k) (delta : Deltas state) :
    (run true (fun w => w) price W state delta).1=(run false (fun _ => 1) (fun _ => 1) 1 state delta).1 := by rw [data,data]

theorem retained_plan {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (state : State k) (delta : Deltas state) :
    (run bits index price W state delta).1.plan=state.plan := rfl

theorem returned_bounded {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W a b : ℕ) (state : State k) (delta : Deltas state)
    (hState : Bounded state a) (hDelta : delta.Bounded b) : Bounded (run bits index price W state delta).1 (a+b) := by
  rw [data]
  exact advance_bounded state delta a b hState hDelta

end Blotto.GeneralPaperEpochFieldAdvancePrice
