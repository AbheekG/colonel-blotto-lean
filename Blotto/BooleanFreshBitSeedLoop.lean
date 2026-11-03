import Blotto.FreshBitSeedLifetime

/-! Fresh-seed production with an actual stored Boolean countdown. Testing
and predecessor use the existing Boolean producers, not natural decoding or
subtraction. Numerical value is used solely by erased termination/refinement
proofs. Padded counters are allowed. This closes this loop's scalar-control
representation; finite reference/activation layout remains separate. -/
namespace Blotto.BooleanFreshBitSeedLoop
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage FreshBitSeedLifetime
set_option maxHeartbeats 2000000

def loopWithTrace {S : Type*} (fresh : S → Bool × S) (counter reversed : List Bool) (state : S) :
    (List Bool × S) × Trace :=
  let tested := BinaryBooleanPrimitiveLifetime.scanWithTrace counter
  if _h : tested.1 = true then
    let bit := fresh state
    let decremented := BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace counter
    let later := loopWithTrace fresh decremented.1 (bit.1::reversed) bit.2
    (later.1,wrapList 1 32 2 [tested.2,decremented.2,later.2])
  else
    let result := reverseWithTrace reversed []
    ((result.1,state),wrap 24 2 [tested.2,result.2])
termination_by BinaryBigEndian.littleValue counter
decreasing_by
  have hp : 0 < BinaryBigEndian.littleValue counter := by
    apply (BinaryEuclideanGCD.nonzero_true_iff counter).mp
    change (BinaryBooleanPrimitiveLifetime.scanWithTrace counter).1 = true at _h
    simpa only [BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using _h
  rw [BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
  have hd := BinaryStoredCountdown.predecessor_value counter hp
  omega

def generateWithTrace {S : Type*} (fresh : S → Bool × S) (counter : List Bool) (state : S) :
    (List Bool × S) × Trace := loopWithTrace fresh counter [] state

theorem loop_state {S : Type*} (fresh : S → Bool × S) (counter reversed : List Bool) (state : S) :
    (loopWithTrace fresh counter reversed state).1 =
      (FreshBitSeedLifetime.loopWithTrace fresh (BinaryBigEndian.littleValue counter) reversed state).1 := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      ∀ (reversed : List Bool) (state : S),
      (loopWithTrace fresh counter reversed state).1 =
        (FreshBitSeedLifetime.loopWithTrace fresh count reversed state).1 := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount reversed state
        rw [loopWithTrace]
        dsimp only
        split
        · rename_i hTest
          have hp := (BinaryEuclideanGCD.nonzero_true_iff counter).mp
            (by simpa only [BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using hTest)
          have hd := BinaryStoredCountdown.predecessor_value counter hp
          have hLess : BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor counter) < count := by omega
          rw [BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
          rw [ih _ hLess _ rfl]
          have hc : count = BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor counter)+1 := by omega
          rw [hc,FreshBitSeedLifetime.loopWithTrace]
        · rename_i hTest
          have hz : BinaryBigEndian.littleValue counter = 0 := by
            have hn : ¬ 0 < BinaryBigEndian.littleValue counter := by
              intro hp
              apply hTest
              rw [BinaryBooleanPrimitiveLifetime.scanWithTrace_erases]
              exact (BinaryEuclideanGCD.nonzero_true_iff counter).mpr hp
            omega
          have hc : count = 0 := by omega
          rw [hc,FreshBitSeedLifetime.loopWithTrace]
  exact hAll _ counter rfl reversed state

theorem generate_state {S : Type*} (fresh : S → Bool × S) (counter : List Bool) (state : S) :
    (generateWithTrace fresh counter state).1 =
      (FreshBitSeedLifetime.generateWithTrace fresh (BinaryBigEndian.littleValue counter) state).1 :=
  loop_state fresh counter [] state

theorem scan_usage (counter : List Bool) :
    usage (BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2 ≤ 5*(counter.length+1) := by
  have h := BinaryBooleanPrimitiveLifetime.scanWithTrace_bounds counter
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

theorem predecessor_usage (counter : List Bool) :
    usage (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace counter).2 ≤ 10*(counter.length+1) := by
  have h := BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_bound counter
  unfold usage
  omega

def envelope (count width reversed : ℕ) : ℕ := 128*(width+1)*(count+1)+2*reversed+64

theorem loop_usage {S : Type*} (fresh : S → Bool × S) (counter reversed : List Bool) (state : S) :
    usage (loopWithTrace fresh counter reversed state).2 ≤
      envelope (BinaryBigEndian.littleValue counter) counter.length reversed.length := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      ∀ (reversed : List Bool) (state : S),
      usage (loopWithTrace fresh counter reversed state).2 ≤ envelope count counter.length reversed.length := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount reversed state
        have hScan := scan_usage counter
        rw [loopWithTrace]
        dsimp only
        split
        · rename_i hTest
          have hp := (BinaryEuclideanGCD.nonzero_true_iff counter).mp
            (by simpa only [BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using hTest)
          have hd := BinaryStoredCountdown.predecessor_value counter hp
          have hLess : BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor counter) < count := by omega
          have hLater := ih _ hLess _ rfl ((fresh state).1::reversed) (fresh state).2
          have hPred := predecessor_usage counter
          have hw := wrapList_usage 1 32 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2,
            (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace counter).2,
            (loopWithTrace fresh (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace counter).1 ((fresh state).1::reversed) (fresh state).2).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          rw [BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure] at hw ⊢
          simp only [envelope,List.length_cons,BinaryStoredCountdown.predecessor_length] at hLater ⊢
          nlinarith
        · have hReverse := FreshBitSeedLifetime.reverse_usage reversed
          have hw := wrap_usage 24 2 [(BinaryBooleanPrimitiveLifetime.scanWithTrace counter).2,(reverseWithTrace reversed []).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          unfold envelope
          nlinarith
  exact hAll _ counter rfl reversed state

theorem generate_usage {S : Type*} (fresh : S → Bool × S) (counter : List Bool) (state : S) :
    usage (generateWithTrace fresh counter state).2 ≤ envelope (BinaryBigEndian.littleValue counter) counter.length 0 :=
  loop_usage fresh counter [] state

theorem generate_counted {S : Type*} (fresh : S → Bool × S) (counter : List Bool) (state : S) (calls : ℕ) :
    (generateWithTrace (countedFresh fresh) counter (state,calls)).1 =
      ((generateWithTrace fresh counter state).1.1,((generateWithTrace fresh counter state).1.2,
        calls+BinaryBigEndian.littleValue counter)) := by
  simp only [generate_state,FreshBitSeedLifetime.generate_counted]

end Blotto.BooleanFreshBitSeedLoop
