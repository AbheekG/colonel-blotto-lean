import Blotto.BinaryTerminalPhysicalGeneratedWork
import Blotto.BinarySeedTraceBounds

/-! Exact potential accounting for the actual measured countdown. Long
borrows create one-bits that pay for later cheap decrements. Together with
retained-ruler counting, complete seed generation has linear source work.
This does not price observer evaluation or fresh-primitive internals. -/

namespace Blotto.BooleanFreshSeedAmortized
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem scan_visits (counter : List Bool) :
    BooleanFreshCounterWork.scanVisits counter = BinaryStoredCountdown.predecessorVisits counter := by
  induction counter with
  | nil => rfl
  | cons bit rest ih => cases bit <;>
      simp only [BooleanFreshCounterWork.scanVisits,BinaryStoredCountdown.predecessorVisits,ih]

theorem predecessor_potential (counter : List Bool) (hp : 0 < BinaryBigEndian.littleValue counter) :
    BinaryStoredCountdown.predecessorVisits counter+BinaryCarryCounter.ones counter =
      2+BinaryCarryCounter.ones (BinaryStoredCountdown.predecessor counter) := by
  induction counter with
  | nil => cases hp
  | cons bit rest ih => cases bit with
    | false =>
        have hr : 0 < BinaryBigEndian.littleValue rest := by
          change 0 < 2*BinaryBigEndian.littleValue rest+0 at hp
          omega
        have h := ih hr
        simp only [BinaryStoredCountdown.predecessorVisits,BinaryStoredCountdown.predecessor,
          BinaryCarryCounter.ones]
        omega
    | true =>
        simp only [BinaryStoredCountdown.predecessorVisits,BinaryStoredCountdown.predecessor,
          BinaryCarryCounter.ones]
        omega

theorem zero_profile (counter : List Bool) (hz : BinaryBigEndian.littleValue counter = 0) :
    BinaryCarryCounter.ones counter = 0 ∧
      BooleanFreshCounterWork.scanVisits counter = counter.length+1 := by
  induction counter with
  | nil => exact ⟨rfl,rfl⟩
  | cons bit rest ih => cases bit with
    | false =>
        have hr : BinaryBigEndian.littleValue rest = 0 := by
          change 2*BinaryBigEndian.littleValue rest+0 = 0 at hz
          omega
        have h := ih hr
        simp only [BinaryCarryCounter.ones,BooleanFreshCounterWork.scanVisits,List.length_cons]
        exact ⟨h.1,by omega⟩
    | true =>
        change 2*BinaryBigEndian.littleValue rest+1 = 0 at hz
        omega

theorem loopAt_work_potential {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    (BooleanFreshSeedMeasured.loopAt next counter reversed state depth).2+
        8*BinaryCarryCounter.ones counter =
      28*BinaryBigEndian.littleValue counter+4*reversed.length+4*counter.length+10 := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      ∀ (reversed : List Bool) (state : S) (depth : ℕ),
      (BooleanFreshSeedMeasured.loopAt next counter reversed state depth).2+
          8*BinaryCarryCounter.ones counter = 28*count+4*reversed.length+4*counter.length+10 := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount reversed state depth
        have hScan := BooleanFreshSeedMeasured.scanAt_work counter (depth+2)
        rw [BooleanFreshSeedMeasured.loopAt]
        dsimp only
        split
        · rename_i hTest
          have hp : 0 < BinaryBigEndian.littleValue counter := by
            apply (BinaryEuclideanGCD.nonzero_true_iff counter).mp
            simpa only [BooleanFreshSeedMeasured.scanAt_erases,
              BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using hTest
          have hd := BinaryStoredCountdown.predecessor_value counter hp
          have hLess : BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor counter) < count := by omega
          have hl := ih _ hLess _ rfl ((next state).1::reversed) (next state).2 (depth+2)
          have hPred := BooleanFreshSeedMeasured.predecessorAt_work counter (depth+2)
          have hPotential := predecessor_potential counter hp
          rw [scan_visits] at hScan
          rw [BooleanFreshSeedMeasured.predecessorAt_erases,
            BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
          rw [BinaryStoredCountdown.predecessor_length] at hl
          simp only [List.length_cons] at hl
          omega
        · rename_i hTest
          have hz : BinaryBigEndian.littleValue counter = 0 := by
            have hn : ¬ 0 < BinaryBigEndian.littleValue counter := by
              intro hp
              apply hTest
              rw [BooleanFreshSeedMeasured.scanAt_erases,BinaryBooleanPrimitiveLifetime.scanWithTrace_erases]
              exact (BinaryEuclideanGCD.nonzero_true_iff counter).mpr hp
            omega
          have hZero := zero_profile counter hz
          have hr := BinarySeedCursorMeasured.reverseAt_work reversed [] (depth+2)
          rw [BinaryMidpointTapeLifetime.reverse_work] at hr
          omega
  exact hAll _ counter rfl reversed state depth


theorem loop_work_potential {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) :
    (BooleanFreshSeedMeasured.loop next counter reversed state).2+
        8*BinaryCarryCounter.ones counter =
      28*BinaryBigEndian.littleValue counter+4*reversed.length+4*counter.length+10 :=
  loopAt_work_potential next counter reversed state 0

theorem loopAt_work_eq {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    (BooleanFreshSeedMeasured.loopAt next counter reversed state depth).2 =
      (BooleanFreshSeedMeasured.loop next counter reversed state).2 := by
  have ha := loopAt_work_potential next counter reversed state depth
  have hb := loop_work_potential next counter reversed state
  omega

theorem generate_linear {S : Type*} (next : S → Bool × S) (counter : List Bool) (state : S) :
    (BooleanFreshSeedMeasured.generate next counter state).2 ≤
      28*BinaryBigEndian.littleValue counter+4*counter.length+10 := by
  have h := loop_work_potential next counter [] state
  change (BooleanFreshSeedMeasured.loop next counter [] state).2 ≤ _
  simp only [List.length_nil,mul_zero,Nat.add_zero] at h
  omega

theorem loopAt_trace_linear {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    (BooleanFreshSeedMeasured.loopAt next counter reversed state depth).1.2.length ≤
      28*BinaryBigEndian.littleValue counter+4*reversed.length+4*counter.length+10 := by
  have ht := (BinarySeedTraceBounds.loop_observers next counter reversed state depth).1
  have hw := loopAt_work_potential next counter reversed state depth
  omega

theorem generate_trace_linear {S : Type*} (next : S → Bool × S)
    (counter : List Bool) (state : S) :
    (BooleanFreshSeedMeasured.generate next counter state).1.2.length ≤
      28*BinaryBigEndian.littleValue counter+4*counter.length+10 := by
  simpa only [BooleanFreshSeedMeasured.generate,BooleanFreshSeedMeasured.loop,
    List.length_nil,mul_zero,Nat.add_zero] using loopAt_trace_linear next counter [] state 0

theorem ruler_generation_linear {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (BinaryPRGRulerSeedMeasured.generate next request state).2 ≤
      100*(sampleBitBudget n request.request.precision+1) := by
  have hp := BinaryPRGRulerSeedMeasured.prepare_work request
  have hs := generate_linear next (BinaryPRGRulerSeedMeasured.prepare request).1.1 state
  rw [BinaryPRGRulerSeedMeasured.prepare_value] at hs
  have hw := (BinaryPRGRulerSeedMeasured.prepare_width request).trans
    (BinaryPRGSeedOutputLifetimePolynomial.wordWidth_le _)
  change (BinaryPRGRulerSeedMeasured.prepare request).2+
    (BooleanFreshSeedMeasured.generate next (BinaryPRGRulerSeedMeasured.prepare request).1.1 state).2+4 ≤ _
  omega

theorem physical_generation_linear {S : Type*} (next : S → Bool × S) (frame : List Bool)
    (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (state : S) :
    (BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state).2 ≤
      400000*(frame.length+1) := by
  have hRef := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hRead,Option.map_some] at hRef
  have hn := BinaryPRGSeedRequestBound.read_seedCount_bound frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hRef.symm
  change sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision ≤
    BinaryPRGSeedRequestBound.seedCountBound frame.length at hn
  unfold BinaryPRGSeedRequestBound.seedCountBound at hn
  have hw := ruler_generation_linear next parsed.1.2.logical state
  omega

theorem complete_uniform_work : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S),
    (BinaryTerminalPhysicalGeneratedWork.run next rich frame state).2+
      BinaryBigEndian.littleValue
        (BinaryTerminalPhysicalGeneratedWork.run next rich frame state).1.1.2 ≤
      C*(frame.length+1)^d := by
  obtain ⟨C,d,hOutput⟩ := BinaryTerminalPhysicalPreparationWork.accepted_uniform_work
  let D := max d 1
  refine ⟨C+400008,D,?_⟩
  intro S next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (show d ≤ D by dsimp only [D]; omega))
  have hLinear : frame.length+1 ≤ (frame.length+1)^D := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ D by dsimp only [D]; omega)
  have hScaled := Nat.mul_le_mul_left 400000 hLinear
  have hOne := Nat.one_le_pow D (frame.length+1) (by omega)
  unfold BinaryTerminalPhysicalGeneratedWork.run
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hParsed
    split
    · let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
      let output := BinaryTerminalPhysicalPreparationWork.run
        frame parsed hParsed rich generated.1.1.1
      have ho := hOutput frame parsed hParsed rich generated.1.1.1
      have hg := physical_generation_linear next frame parsed hParsed state
      change output.2+generated.2+8+BinaryBigEndian.littleValue output.1.1.2 ≤ _
      change output.2+BinaryBigEndian.littleValue output.1.1.2 ≤ _ at ho
      change generated.2 ≤ _ at hg
      nlinarith only [ho,hg,hd,hScaled,hOne]
    · exact Nat.zero_le _

theorem pair_uniform_work : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (frame : List Bool) (state : S),
    (BinaryTerminalPhysicalGeneratedWork.pair next frame state).2+
      BinaryBigEndian.littleValue
        (BinaryTerminalPhysicalGeneratedWork.pair next frame state).1.1.2.1+
      BinaryBigEndian.littleValue
        (BinaryTerminalPhysicalGeneratedWork.pair next frame state).1.1.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := complete_uniform_work
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have hr := hBound next true frame state
  have hp := hBound next false frame (BinaryTerminalPhysicalGeneratedWork.run next true frame state).1.1.1.2
  unfold BinaryTerminalPhysicalGeneratedWork.pair
  dsimp only
  nlinarith only [hr,hp]

end Blotto.BooleanFreshSeedAmortized
