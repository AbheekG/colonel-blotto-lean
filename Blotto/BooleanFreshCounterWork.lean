import Blotto.BinaryPRGSeedCountLifetime

/-! Exact reached Boolean scan/borrow visits and all countdown word versions.
These are observers of the actual Boolean loop, never additional producer
work. They expose the internally derived logarithmic live scalar width and
control visits. Reference transport, calls/activations and the remaining
full native-machine interpretation are deliberately separate. -/
namespace Blotto.BooleanFreshCounterWork
open BinaryPRGSeedCountLifetime

def scanVisits : List Bool → ℕ
  | [] => 1
  | true::_ => 1
  | false::rest => scanVisits rest+1

theorem scanVisits_bound (counter : List Bool) : scanVisits counter ≤ counter.length+1 := by
  induction counter with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [scanVisits,List.length_cons] <;> omega

def visits (counter : List Bool) : ℕ :=
  if _h : BinaryEuclideanGCD.nonzero counter = true then
    scanVisits counter+BinaryStoredCountdown.predecessorVisits counter+
      visits (BinaryStoredCountdown.predecessor counter)
  else scanVisits counter
termination_by BinaryBigEndian.littleValue counter
decreasing_by
  have hd := BinaryStoredCountdown.predecessor_value counter ((BinaryEuclideanGCD.nonzero_true_iff counter).mp _h)
  omega

theorem visits_bound (counter : List Bool) :
    visits counter ≤ 2*(counter.length+1)*(BinaryBigEndian.littleValue counter+1) := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      visits counter ≤ 2*(counter.length+1)*(count+1) := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount
        have hScan := scanVisits_bound counter
        rw [visits]
        split
        · rename_i hNonzero
          have hd := BinaryStoredCountdown.predecessor_value counter ((BinaryEuclideanGCD.nonzero_true_iff counter).mp hNonzero)
          have hl : BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor counter) < count := by omega
          have hLater := ih _ hl _ rfl
          rw [BinaryStoredCountdown.predecessor_length] at hLater
          have hPred := BinaryStoredCountdown.predecessorVisits_bound counter
          nlinarith
        · nlinarith
  exact hAll _ counter rfl

def history (counter : List Bool) : List (List Bool) :=
  counter :: if _h : BinaryEuclideanGCD.nonzero counter = true then
    history (BinaryStoredCountdown.predecessor counter) else []
termination_by BinaryBigEndian.littleValue counter
decreasing_by
  have hd := BinaryStoredCountdown.predecessor_value counter ((BinaryEuclideanGCD.nonzero_true_iff counter).mp _h)
  omega

theorem history_contract (counter : List Bool) :
    (history counter).length = BinaryBigEndian.littleValue counter+1 ∧
      ∀ word ∈ history counter,word.length = counter.length ∧
        BinaryBigEndian.littleValue word ≤ BinaryBigEndian.littleValue counter := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      (history counter).length = count+1 ∧
        ∀ word ∈ history counter,word.length = counter.length ∧ BinaryBigEndian.littleValue word ≤ count := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount
        rw [history]
        split
        · rename_i hNonzero
          have hd := BinaryStoredCountdown.predecessor_value counter ((BinaryEuclideanGCD.nonzero_true_iff counter).mp hNonzero)
          have hl : BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor counter) < count := by omega
          obtain ⟨hLength,hWords⟩ := ih _ hl _ rfl
          refine ⟨by simp only [List.length_cons,hLength]; omega,?_⟩
          intro word hWord
          rcases List.mem_cons.mp hWord with hWord | hWord
          · subst word
            exact ⟨rfl,hCount.le⟩
          · have h := hWords word hWord
            rw [BinaryStoredCountdown.predecessor_length] at h
            exact ⟨h.1,by omega⟩
        · rename_i hNonzero
          have hz : BinaryBigEndian.littleValue counter = 0 := by
            have hn := (BinaryEuclideanGCD.nonzero_true_iff counter).not.mp hNonzero
            omega
          refine ⟨by simp only [List.length_cons,List.length_nil]; omega,?_⟩
          intro word hWord
          have he : word = counter := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hWord
          subst word
          exact ⟨rfl,hCount.le⟩
  exact hAll _ counter rfl

theorem raw_width (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    (prepareWithTrace parsed.1.2.request).1.length ≤ binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length) := by
  exact (prepare_width parsed.1.2.request).trans (binaryWordWidth_mono
    (BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed
      ((BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead)))

theorem raw_visits (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    visits (prepareWithTrace parsed.1.2.request).1 ≤
      2*(binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length)+1)*
        (BinaryPRGSeedRequestBound.seedCountBound frame.length+1) := by
  have h := visits_bound (prepareWithTrace parsed.1.2.request).1
  rw [prepare_value] at h
  apply h.trans
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_left 2 (Nat.add_le_add_right (raw_width frame parsed hRead) 1)
  · exact Nat.add_le_add_right (BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed
      ((BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead)) 1

theorem raw_history (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    ∀ word ∈ history (prepareWithTrace parsed.1.2.request).1,
      word.length ≤ binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length) ∧
        BinaryBigEndian.littleValue word ≤ BinaryPRGSeedRequestBound.seedCountBound frame.length := by
  intro word hWord
  have h := (history_contract (prepareWithTrace parsed.1.2.request).1).2 word hWord
  rw [prepare_value] at h
  exact ⟨h.1.le.trans (raw_width frame parsed hRead),h.2.trans
    (BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed
      ((BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead))⟩

end Blotto.BooleanFreshCounterWork
