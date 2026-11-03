import Blotto.BinaryWordCoinPrimitivesMeasured
import Blotto.BinaryPRGHeapTraceUsage

/-! A complete Boolean-PC coin consumes reached measured scans, seed lookup,
restoring step and increment once. Work follows executed branches and remaining
seed positions. Full preceding outcome/cursor/allocation trace is preserved.
Width/count/value/trace/work observers are ghost; native reference, metadata,
index arithmetic and allocator realization remain separate. -/

namespace Blotto.BinaryWordCoinMeasured
open BinarySeedPreparationSpace BinarySeedLookupTree BinaryRationalNormalization BinaryPRGHeapTraceUsage
open BinaryWordCoinPrimitivesMeasured
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem advance_value (store : Store) (pc : FixedBinaryWord store.width)
    (hRead : (lt pc store.cap).1.1 = true) : (increment pc).1.1.1.value = pc.value+1 := by
  rw [increment_erases,BinaryWordStoreLifetime.incrementWithTrace_erases]
  exact BinaryWordIndexCoinController.advance_value store pc
    (by simpa only [lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead)

theorem advance_bound (store : Store) (pc : FixedBinaryWord store.width)
    (hRead : (lt pc store.cap).1.1 = true) : (increment pc).1.1.1.value ≤ store.cap.value := by
  rw [increment_erases,BinaryWordStoreLifetime.incrementWithTrace_erases]
  exact BinaryWordIndexCoinController.advance_bound store pc
    (by simpa only [lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead)

def run {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ :=
  let tested := zero a.bits
  let first := [.frames 2,.arrayAllocation 16]++under 2 tested.1.2
  if tested.1.1 then (((some false,pc),first),tested.2+4) else
    let compared := same a.bits b.bits
    let second := first++under 2 compared.1.2
    if compared.1.1 then (((some true,pc),second),tested.2+compared.2+8) else
      let guarded := lt pc store.cap
      let third := second++under 2 guarded.1.2
      if hRead : guarded.1.1 = true then
        let read := lookup store pc
        let next := step a b
        let advanced := increment pc
        let localTrace := third++under 2 read.1.2++under 2 next.1.2++under 2 advanced.1.2
        let work := tested.2+compared.2+guarded.2+read.2+next.2+advanced.2+16
        if read.1.1 = next.1.1.1 then
          let later := run store next.1.1.2 b advanced.1.1.1 (advance_bound store pc hRead)
          ((later.1.1,localTrace++under 1 later.1.2),work+later.2)
        else (((some (!read.1.1),advanced.1.1.1),localTrace),work)
      else (((none,pc),third),tested.2+compared.2+guarded.2+12)
termination_by store.cap.value-pc.value
decreasing_by
  have hn := advance_value store pc hRead
  have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [guarded,lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases] using hRead)
  omega

theorem run_erases {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store a b pc hp).1 = BinaryWordCoinLifetime.runWithTrace store a b pc hp := by
  conv_lhs => unfold run
  conv_rhs => unfold BinaryWordCoinLifetime.runWithTrace
  dsimp only
  simp only [zero_erases,same_erases,lt_erases,lookup_erases,step_erases,increment_erases,
    BinaryWordCoinLifetime.earlyTrace,BinaryWordCoinLifetime.equalTrace,
    BinaryWordCoinLifetime.guardTrace,BinaryWordCoinLifetime.readTrace]
  split_ifs with hz he hRead hd
  all_goals first
    | rfl
    | have hpNext : (BinaryWordStoreLifetime.incrementWithTrace pc).1.1.value ≤ store.cap.value := by
        rw [BinaryWordStoreLifetime.incrementWithTrace_erases]
        exact BinaryWordIndexCoinController.advance_bound store pc
          (by simpa only [BinaryWordStoreLifetime.ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead)
      have hLater := run_erases store (BinaryWordCoinLifetime.stepWithTrace a b).1.2 b
        (BinaryWordStoreLifetime.incrementWithTrace pc).1.1 hpNext
      exact congrArg (fun output : (Option Bool × FixedBinaryWord store.width) × Trace =>
        (output.1,BinaryWordCoinLifetime.readTrace store a b pc++under 1 output.2)) hLater
termination_by store.cap.value-pc.value
decreasing_by
  have hRead' : (BinaryWordStoreLifetime.ltWithTrace pc store.cap).1 = true := by assumption
  have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [BinaryWordStoreLifetime.ltWithTrace_erases] using hRead')
  have hn := BinaryWordIndexCoinController.advance_value store pc
    (by simpa only [BinaryWordStoreLifetime.ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead')
  change (BinaryIndexWord.increment pc).1.value = pc.value+1 at hn
  rw [BinaryWordStoreLifetime.incrementWithTrace_erases]
  omega

def localPrice (w i : ℕ) : ℕ := 100*(w+i+2)

theorem local_work {w : ℕ} (store : Store) (a b : FixedBinaryWord w) (pc : FixedBinaryWord store.width) :
    (zero a.bits).2+(same a.bits b.bits).2+(lt pc store.cap).2+(lookup store pc).2+
      (step a b).2+(increment pc).2+16 ≤ localPrice w store.width := by
  have hz := zero_work a.bits
  have he := same_work a.bits b.bits
  rw [a.size] at hz he
  have hl := lookup_work store pc
  have hs := step_work a b
  have hi := increment_work pc
  change _+_+16*(store.width+1)+_+_+_+16 ≤ _
  unfold localPrice
  omega

theorem run_work {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store a b pc hp).2 ≤ (store.cap.value-pc.value+1)*localPrice w store.width := by
  have hLocal := local_work store a b pc
  have hScale : localPrice w store.width ≤ (store.cap.value-pc.value+1)*localPrice w store.width := by nlinarith
  unfold run
  dsimp only
  split
  · omega
  · split
    · omega
    · split
      · rename_i hRead
        have hn := advance_value store pc hRead
        have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
          (by simpa only [lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases] using hRead)
        split
        · have hLater := run_work store (step a b).1.1.2 b (increment pc).1.1.1 (advance_bound store pc hRead)
          have hDiff : store.cap.value-(increment pc).1.1.1.value+1 = store.cap.value-pc.value := by omega
          rw [hDiff] at hLater
          nlinarith only [hLocal,hLater]
        · omega
      · omega
termination_by store.cap.value-pc.value
decreasing_by
  have hRead' : (lt pc store.cap).1.1 = true := by assumption
  have hn := advance_value store pc hRead'
  have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases] using hRead')
  omega

def sample (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ :=
  let W := width word
  let a := pad W word.numerator
  let b := pad W word.denominator
  have ha : a.1.1.length = W := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_left _ _)
  have hb : b.1.1.length = W := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_right _ _)
  let later := run store ⟨a.1.1,ha⟩ ⟨b.1.1,hb⟩ pc hp
  ((later.1.1,[.frames (W+8),.arrayAllocation 16]++under 2 a.1.2++under 2 b.1.2++under 2 later.1.2),
    a.2+b.2+later.2+8*(W+1))

theorem sample_erases (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (sample store word pc hp).1 = BinaryWordCoinLifetime.sampleWithTrace store word pc hp := by
  simp only [sample,BinaryWordCoinLifetime.sampleWithTrace,run_erases,pad_erases]

def samplePrice (W i remaining : ℕ) : ℕ := 20*W+24+(remaining+1)*localPrice W i

theorem sample_work (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (W : ℕ) (hW : width word ≤ W) :
    (sample store word pc hp).2 ≤ samplePrice W store.width (store.cap.value-pc.value) := by
  let a := pad (width word) word.numerator
  let b := pad (width word) word.denominator
  have ha : a.1.1.length = width word := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length _ _ (Nat.le_max_left _ _)
  have hb : b.1.1.length = width word := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length _ _ (Nat.le_max_right _ _)
  have hA := pad_work (width word) word.numerator (Nat.le_max_left _ _)
  have hB := pad_work (width word) word.denominator (Nat.le_max_right _ _)
  have hRun := run_work store (⟨a.1.1,ha⟩ : FixedBinaryWord (width word)) ⟨b.1.1,hb⟩ pc hp
  have hm : localPrice (width word) store.width ≤ localPrice W store.width := by unfold localPrice; omega
  have ht := Nat.mul_le_mul_left (store.cap.value-pc.value+1) hm
  change a.2+b.2+_+8*(width word+1) ≤ _
  unfold samplePrice
  dsimp only [a,b] at hRun ⊢
  omega

theorem sample_position (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (sample store word pc hp).1.1.2.value ∧
      (sample store word pc hp).1.1.2.value ≤ store.cap.value := by
  rw [sample_erases]
  exact BinaryWordCoinLifetime.sampleWithTrace_position store word pc hp

theorem sample_all_prefix (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (W : ℕ) (hW : width word ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (sample store word pc hp).1.2 steps ≤ borrowed+
      (BinaryWordCoinLifetime.sampleBound W store.width (store.cap.value-pc.value)+
        (store.cap.value-pc.value)+2*W+2*store.width+24) ∧
    framePeak ((sample store word pc hp).1.2.take steps) ≤
      BinaryWordCoinLifetime.sampleBound W store.width (store.cap.value-pc.value)+
        (store.cap.value-pc.value)+2*W+2*store.width+24 := by
  rw [sample_erases]
  have h := BinaryWordCoinLifetime.sampleWithTrace_bounds store word pc hp W hW
  apply BinaryPRGHeapTraceUsage.all_prefix
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

end Blotto.BinaryWordCoinMeasured
