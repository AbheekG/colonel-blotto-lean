import Blotto.BinaryCanonicalFrameLifetime
import Blotto.BinaryStoredCountdownLifetime
import Blotto.BinaryStoredDimensionRow

/-! Actual stored-dimension row parsing uses traced zero tests, reached
canonical word parsing and Boolean borrow propagation. Recursion decreases
remaining frame length, never the untrusted decoded dimension. Successful
list construction, old counter versions and all activations stay reserved. -/
namespace Blotto.BinaryStoredDimensionRowLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGFrame
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryStoredCountdownLifetime
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

def readWithTrace (counter bits : List Bool) : Option (Words (BinaryBigEndian.littleValue counter) × List Bool) × Trace :=
  let tested := BinaryBooleanPrimitiveLifetime.scanWithTrace counter
  if hPositive : tested.1 = true then
    let first := BinaryCanonicalFrameLifetime.readWithTrace bits
    match hf : first.1 with
    | none => (none,wrap 24 2 [tested.2,first.2])
    | some parsed =>
        let smaller := predecessorWithTrace counter
        let later := readWithTrace smaller.1 parsed.2
        have hCount : BinaryBigEndian.littleValue smaller.1+1 = BinaryBigEndian.littleValue counter :=
          predecessorWithTrace_value counter ((BinaryEuclideanGCD.nonzero_true_iff _).mp
            ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).symm.trans hPositive))
        let result := later.1.map (fun rest =>
          (⟨parsed.1.val::rest.1.row,(by simp only [List.length_cons,rest.1.length]; exact hCount),
            (by intro word hw; rcases List.mem_cons.mp hw with he | ht
                · subst word; exact parsed.1.property
                · exact rest.1.canonical word ht)⟩,rest.2))
        (result,wrapList 1 48 2 [tested.2,first.2,smaller.2,later.2])
  else
    have hZero : BinaryBigEndian.littleValue counter = 0 := by
      apply BinaryStoredCountdown.nonzeroWithWork_false counter
      apply Bool.eq_false_iff.mpr
      exact fun h => hPositive ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).trans h)
    (some (⟨[],hZero.symm,by simp⟩,bits),wrap 16 2 [tested.2])
termination_by bits.length
decreasing_by exact BinaryCanonicalFrameLifetime.read_suffix_lt bits parsed hf

theorem readWithTrace_raw_state (counter bits : List Bool) :
    (readWithTrace counter bits).1.map BinaryStoredDimensionRow.erase =
      (BinaryStoredDimensionRow.read counter bits).1.map BinaryStoredDimensionRow.erase := by
  unfold readWithTrace BinaryStoredDimensionRow.read
  dsimp only
  by_cases hPositive : (BinaryBooleanPrimitiveLifetime.scanWithTrace counter).1 = true
  · have hOld : (BinaryStoredCountdown.nonzeroWithWork counter).1 = true :=
      (BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).symm.trans hPositive
    rw [dite_eq_left hPositive,dite_eq_left hOld]
    rw [← BinaryCanonicalFrameLifetime.readWithTrace_state]
    cases hf : (BinaryCanonicalFrameLifetime.readWithTrace bits).1 with
    | none => rfl
    | some parsed =>
        dsimp only
        have ih := readWithTrace_raw_state (predecessorWithTrace counter).1 parsed.2
        have hI : (readWithTrace (predecessorWithTrace counter).1 parsed.2).1.map
            (fun rest => (parsed.1.val::rest.1.row,rest.2)) =
          (BinaryStoredDimensionRow.read (predecessorWithTrace counter).1 parsed.2).1.map
            (fun rest => (parsed.1.val::rest.1.row,rest.2)) := by
          simpa only [Option.map_map,Function.comp_def,BinaryStoredDimensionRow.erase] using
            congrArg (Option.map (fun rest => (parsed.1.val::rest.1,rest.2))) ih
        have hOldRows := congrArg (fun smaller : List Bool => (BinaryStoredDimensionRow.read smaller parsed.2).1.map
          (fun rest => (parsed.1.val::rest.1.row,rest.2))) (predecessorWithTrace_state counter)
        simpa only [BinaryStoredCountdown.predecessorWithWork_state,Option.map_map,
          Function.comp_def,BinaryStoredDimensionRow.erase] using hI.trans hOldRows
  · have hOld : ¬ (BinaryStoredCountdown.nonzeroWithWork counter).1 = true :=
      fun h => hPositive ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases counter).trans h)
    rw [dite_eq_right hPositive,dite_eq_right hOld]
termination_by bits.length
decreasing_by exact BinaryCanonicalFrameLifetime.read_suffix_lt _ _ (by assumption)

theorem readWithTrace_state (counter bits : List Bool) :
    (readWithTrace counter bits).1 = (BinaryStoredDimensionRow.read counter bits).1 := by
  have h := readWithTrace_raw_state counter bits
  cases hn : (readWithTrace counter bits).1 with
  | none =>
      rw [hn,Option.map_none] at h
      cases ho : (BinaryStoredDimensionRow.read counter bits).1 with
      | none => rfl
      | some parsed => rw [ho,Option.map_some] at h; cases h
  | some parsed =>
      rw [hn,Option.map_some] at h
      cases ho : (BinaryStoredDimensionRow.read counter bits).1 with
      | none => rw [ho,Option.map_none] at h; cases h
      | some old =>
          rw [ho,Option.map_some] at h
          exact congrArg some (BinaryStoredDimensionRow.erase_injective (Option.some.inj h))

theorem read_count_bound (counter bits : List Bool) (parsed : Words (BinaryBigEndian.littleValue counter) × List Bool)
    (h : (readWithTrace counter bits).1 = some parsed) : BinaryBigEndian.littleValue counter ≤ bits.length :=
  BinaryStoredDimensionRow.read_count_bound counter bits parsed ((readWithTrace_state counter bits).symm.trans h)

theorem read_consumed (counter bits : List Bool) (parsed : Words (BinaryBigEndian.littleValue counter) × List Bool)
    (h : (readWithTrace counter bits).1 = some parsed) :
    (parsed.1.row.map width).sum+parsed.2.length ≤ bits.length :=
  BinaryStoredDimensionRow.read_consumed counter bits parsed ((readWithTrace_state counter bits).symm.trans h)

def envelope (counterWidth length : ℕ) : ℕ :=
  (length+1)*(BinaryCanonicalFrameLifetime.envelope length+32*(counterWidth+1)+128)

theorem envelope_mono {a b c d : ℕ} (hW : a ≤ b) (hL : c ≤ d) : envelope a c ≤ envelope b d := by
  have h := BinaryCanonicalFrameLifetime.envelope_mono hL
  unfold envelope
  gcongr

theorem readWithTrace_usage (counter bits : List Bool) :
    usage (readWithTrace counter bits).2 ≤ envelope counter.length bits.length := by
  have hScan := BinaryBooleanPrimitiveLifetime.scanWithTrace_bounds counter
  have hTest : usage (BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2 ≤ 5*(counter.length+1) := by
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  have hFirst := BinaryCanonicalFrameLifetime.readWithTrace_usage bits
  unfold readWithTrace
  dsimp only
  split
  · split
    · have hw := wrap_usage 24 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2,
        (BinaryCanonicalFrameLifetime.readWithTrace bits).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2,
        (BinaryCanonicalFrameLifetime.readWithTrace bits).2]) ≤ _
      unfold envelope
      nlinarith
    · rename_i parsed hf
      have hLength := BinaryCanonicalFrameLifetime.read_suffix_lt bits parsed hf
      have hDec := predecessorWithTrace_usage counter
      have ih := readWithTrace_usage (predecessorWithTrace counter).1 parsed.2
      rw [predecessorWithTrace_length] at ih
      change usage (readWithTrace (predecessorWithTrace counter).1 parsed.2).2 ≤
        (parsed.2.length+1)*(BinaryCanonicalFrameLifetime.envelope parsed.2.length+32*(counter.length+1)+128) at ih
      have hCanon := BinaryCanonicalFrameLifetime.envelope_mono hLength.le
      have ht : usage (readWithTrace (predecessorWithTrace counter).1 parsed.2).2 ≤
          bits.length*(BinaryCanonicalFrameLifetime.envelope bits.length+32*(counter.length+1)+128) :=
        ih.trans (Nat.mul_le_mul (show parsed.2.length+1 ≤ bits.length by omega)
          (Nat.add_le_add_right (Nat.add_le_add_right hCanon (32*(counter.length+1))) 128))
      have hw := wrapList_usage 1 48 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2,
        (BinaryCanonicalFrameLifetime.readWithTrace bits).2,(predecessorWithTrace counter).2,
        (readWithTrace (predecessorWithTrace counter).1 parsed.2).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrapList 1 48 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2,
        (BinaryCanonicalFrameLifetime.readWithTrace bits).2,(predecessorWithTrace counter).2,
        (readWithTrace (predecessorWithTrace counter).1 parsed.2).2]) ≤ _
      unfold envelope
      rw [Nat.add_mul,one_mul]
      omega
  · have hw := wrap_usage 16 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2]) ≤ _
    unfold envelope
    nlinarith
termination_by bits.length
decreasing_by exact BinaryCanonicalFrameLifetime.read_suffix_lt _ _ (by assumption)

theorem envelope_polynomial (counterWidth length : ℕ) : envelope counterWidth length ≤ 4000*(counterWidth+length+2)^4 := by
  let T := counterWidth+length
  have hMono := envelope_mono (show counterWidth ≤ T by dsimp [T]; omega) (show length ≤ T by dsimp [T]; omega)
  have hDiagonal : envelope T T ≤ 4000*(T+2)^4 := by
    unfold envelope BinaryCanonicalFrameLifetime.envelope
    nlinarith only [sq_nonneg (T:ℤ)]
  exact hMono.trans hDiagonal

theorem all_prefix (counter bits : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+counter.length+bits.length) (readWithTrace counter bits).2 steps ≤
      borrowed+counter.length+bits.length+envelope counter.length bits.length ∧
    framePeak ((readWithTrace counter bits).2.take steps) ≤ envelope counter.length bits.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage counter bits) _ steps

end Blotto.BinaryStoredDimensionRowLifetime
