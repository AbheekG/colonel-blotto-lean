import Blotto.GeneralPaperSignedCellUpdates

/-! Execute and charge both delta generation and level-array addition.
The earlier array accumulator took materialized deltas as inputs. This loop
includes their construction costs and refines its exact data semantics.
-/
namespace Blotto.GeneralPaperDeltaAccumulation
open scoped BigOperators
open GeneralPaperUnsignedCellConstancy (Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {n : ℕ} (delta : ℕ → FixedArrayTable n ℕ × ℕ) : ℕ → FixedArrayTable n ℕ × ℕ
  | 0 => GeneralPaperEpochLevelArray.initial n
  | t+1 =>
    let previous := run delta t
    let generated := delta t
    let advanced := GeneralPaperEpochLevelArray.advance previous.1 generated.1
    (advanced.1,previous.2+generated.2+advanced.2+8)

theorem data_eq {n : ℕ} (delta : ℕ → FixedArrayTable n ℕ × ℕ) (count : ℕ) :
    (run delta count).1=(GeneralPaperEpochLevelArray.execute (fun t => (delta t).1) count).1 := by
  induction count with
  | zero => rfl
  | succ t ih =>
    change (GeneralPaperEpochLevelArray.advance (run delta t).1 (delta t).1).1=
      (GeneralPaperEpochLevelArray.advance (GeneralPaperEpochLevelArray.execute (fun t => (delta t).1) t).1 (delta t).1).1
    rw [ih]

theorem read_run {n : ℕ} (delta : ℕ → FixedArrayTable n ℕ × ℕ) (count : ℕ) (r : Fin n) :
    (run delta count).1.read r=GeneralPaperGeometricLevels.levels (fun t r => (delta t).1.read r) count r := by
  rw [data_eq,GeneralPaperEpochLevelArray.execute_read]

theorem work {n : ℕ} (delta : ℕ → FixedArrayTable n ℕ × ℕ) (count : ℕ) :
    (run delta count).2=50*n+18+count*(54*n+26)+∑ t∈Finset.range count, (delta t).2 := by
  induction count with
  | zero => simpa only [run,Nat.zero_mul,Nat.add_zero,Finset.sum_range_zero] using GeneralPaperEpochLevelArray.initialize_work n
  | succ t ih =>
    change (run delta t).2+(delta t).2+(GeneralPaperEpochLevelArray.advance _ _).2+8=_
    rw [GeneralPaperEpochLevelArray.advance_work,ih,Finset.sum_range_succ]
    ring

theorem constant_work {n : ℕ} (delta : ℕ → FixedArrayTable n ℕ × ℕ) (W count : ℕ)
    (h : ∀ t<count, (delta t).2=W) : (run delta count).2=50*n+18+count*(W+54*n+26) := by
  rw [work]
  have hs : (∑ t∈Finset.range count, (delta t).2)=count*W := by
    calc
      _ = ∑ _t∈Finset.range count, W := by
        apply Finset.sum_congr rfl
        intro t ht
        exact h t (Finset.mem_range.mp ht)
      _ = _ := by simp
  rw [hs]
  ring

theorem unsigned_work {m : ℕ} (k : ℕ) (response : Bool) (cdfPrefix signedPrefix : ℕ → Prefix k)
    (plan : GeneralPaperQueryLossCounts.Plan k m) (count : ℕ) :
    (run (fun t => GeneralPaperNativeDeltaArrays.unsigned k response (cdfPrefix t) (signedPrefix t) plan) count).2=
      50*m+18+count*(m*(48*(30+k)+352)+44) := by
  rw [constant_work _ (m*(48*(30+k)+298)+18) count
    (fun t _ => GeneralPaperNativeDeltaArrays.unsigned_work k response (cdfPrefix t) (signedPrefix t) plan)]
  ring

theorem signed_work {m : ℕ} (k U : ℕ) (bid : ℕ → ℕ) (preparedPrefix : ℕ → Prefix k)
    (plan : GeneralPaperSignedUpdatePlan.Plan k m) (count : ℕ) :
    (run (fun t => GeneralPaperNativeDeltaArrays.signed k U (bid t) (preparedPrefix t) plan) count).2=
      50*m+18+count*(m*(12*(30+k)+162)+44) := by
  rw [constant_work _ (m*(12*(30+k)+108)+18) count
    (fun t _ => GeneralPaperNativeDeltaArrays.signed_work k U (bid t) (preparedPrefix t) plan)]
  ring

end Blotto.GeneralPaperDeltaAccumulation
