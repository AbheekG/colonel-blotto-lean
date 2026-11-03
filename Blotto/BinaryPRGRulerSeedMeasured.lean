import Blotto.BooleanFreshSeedMeasured
import Blotto.BinaryWordStoreMeasured
import Blotto.BinaryPRGPhysicalRawRequestLifetime

/-! Retained request rulers produce the fresh-seed countdown directly.
Three carry passes count choice/scalar/outer cells without a row-array
projection, repeated accuracy preparation, append copies or numeric decoder.
Work and traces are source observers; their native evaluation is separate. -/

namespace Blotto.BinaryPRGRulerSeedMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem count_data {α : Type*} (items : List α) (counter : List Bool) :
    (BinaryWordStoreMeasured.count items counter).1.1 = BinaryCarryCounter.count items counter := by
  rw [BinaryWordStoreMeasured.count_data,BinaryWordStoreLifetime.countWithTrace_erases]

theorem count_value {α : Type*} (items : List α) (counter : List Bool) :
    BinaryBigEndian.littleValue (BinaryWordStoreMeasured.count items counter).1.1 =
      BinaryBigEndian.littleValue counter+items.length := by
  calc
    _ = BinaryCarryCounter.value (BinaryCarryCounter.count items counter) :=
      congrArg BinaryBigEndian.littleValue (count_data items counter)
    _ = BinaryCarryCounter.value counter+items.length := BinaryCarryCounter.count_value items counter

theorem count_bound {α : Type*} (items : List α) (counter : List Bool) :
    (BinaryWordStoreMeasured.count items counter).2 ≤ 9*items.length+4*counter.length+2 := by
  rw [BinaryWordStoreMeasured.count_work,BinaryWordStoreWork.count_work]
  have hc := BinaryCarryCounter.countCarryCells_bound items counter
  have ho := BooleanSampleCountLifetime.ones_le_length counter
  omega

theorem count_usage {α : Type*} (items : List α) (counter : List Bool) :
    usage (BinaryWordStoreMeasured.count items counter).1.2 ≤
      20*(items.length+counter.length+1) := by
  rw [BinaryWordStoreMeasured.count_erases]
  have ht := BinaryWordStoreLifetime.countWithTrace_bounds items counter
  have hc := BinaryCarryCounter.countCarryCells_bound items counter
  have ho := BooleanSampleCountLifetime.ones_le_length counter
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

theorem count_length {α : Type*} (items : List α) (counter : List Bool)
    (hC : BinaryCarryCounter.Canonical counter) :
    (BinaryWordStoreMeasured.count items counter).1.1.length ≤
      BinaryCarryCounter.value counter+items.length+1 := by
  rw [count_data]
  have h := BinaryCarryCounter.canonical_length_bound _
    (BinaryCarryCounter.count_canonical items counter hC)
  rw [BinaryCarryCounter.count_value] at h
  exact h.trans (BinaryPRGSeedOutputLifetimePolynomial.wordWidth_le _)

theorem stages_width (choice precision : List Bool) :
    let first := (BinaryWordStoreMeasured.count choice []).1.1
    let second := (BinaryWordStoreMeasured.count precision first).1.1
    first.length ≤ choice.length+1 ∧ second.length ≤ choice.length+precision.length+1 := by
  have hf := count_length choice [] (by trivial)
  have hfc : BinaryCarryCounter.Canonical
      (BinaryWordStoreMeasured.count choice []).1.1 := by
    rw [count_data]
    exact BinaryCarryCounter.count_canonical choice [] (by trivial)
  have hs := count_length precision (BinaryWordStoreMeasured.count choice []).1.1 hfc
  have hv : BinaryCarryCounter.value (BinaryWordStoreMeasured.count choice []).1.1 =
      choice.length := by
    change BinaryBigEndian.littleValue (BinaryWordStoreMeasured.count choice []).1.1 = choice.length
    simpa only [BinaryBigEndian.littleValue,Nat.zero_add] using count_value choice []
  rw [hv] at hs
  exact ⟨by simpa only [BinaryCarryCounter.value,BinaryBigEndian.littleValue,Nat.zero_add] using hf,hs⟩

def prepare {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) : (List Bool × Trace) × ℕ :=
  let first := BinaryWordStoreMeasured.count request.choiceRuler []
  let second := BinaryWordStoreMeasured.count request.precisionRuler first.1.1
  let third := BinaryWordStoreMeasured.count request.precisionRuler second.1.1
  ((third.1.1,wrap 48 2 [first.1.2,second.1.2,third.1.2]),first.2+second.2+third.2+8)

theorem prepare_data {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) :
    (prepare request).1.1 = BinaryCarryCounter.count request.precisionRuler
      (BinaryCarryCounter.count request.precisionRuler (BinaryCarryCounter.count request.choiceRuler [])) := by
  simp only [prepare,count_data]

theorem prepare_value {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) :
    BinaryBigEndian.littleValue (prepare request).1.1 = sampleBitBudget n request.request.precision := by
  simp only [prepare,count_value,BinaryBigEndian.littleValue,
    Nat.zero_add,request.choiceRuler_length,request.precisionRuler_length]
  unfold sampleBitBudget innerBitBudget
  omega

theorem prepare_width {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) :
    (prepare request).1.1.length ≤ binaryWordWidth (sampleBitBudget n request.request.precision) := by
  have hc : BinaryCarryCounter.Canonical (prepare request).1.1 := by
    rw [prepare_data]
    exact BinaryCarryCounter.count_canonical _ _ (BinaryCarryCounter.count_canonical _ _
      (BinaryCarryCounter.count_canonical _ [] (by trivial)))
  have h := BinaryCarryCounter.canonical_length_bound _ hc
  change (prepare request).1.1.length ≤ binaryWordWidth (BinaryBigEndian.littleValue _) at h
  rw [prepare_value] at h
  exact h

theorem prepare_work {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) :
    (prepare request).2 ≤ 64*(sampleBitBudget n request.request.precision+1) := by
  let first := BinaryWordStoreMeasured.count request.choiceRuler []
  let second := BinaryWordStoreMeasured.count request.precisionRuler first.1.1
  let third := BinaryWordStoreMeasured.count request.precisionRuler second.1.1
  have h1 := count_bound request.choiceRuler []
  have h2 := count_bound request.precisionRuler first.1.1
  have h3 := count_bound request.precisionRuler second.1.1
  have hw := stages_width request.choiceRuler request.precisionRuler
  change first.1.1.length ≤ _ ∧ second.1.1.length ≤ _ at hw
  change first.2 ≤ _ at h1
  change second.2 ≤ _ at h2
  change third.2 ≤ _ at h3
  change first.2+second.2+third.2+8 ≤ _
  simp only [List.length_nil] at h1
  simp only [request.choiceRuler_length,request.precisionRuler_length] at h1 h2 h3 hw
  unfold sampleBitBudget innerBitBudget
  omega

theorem prepare_usage {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) :
    usage (prepare request).1.2 ≤ 256*(sampleBitBudget n request.request.precision+1) := by
  let first := BinaryWordStoreMeasured.count request.choiceRuler []
  let second := BinaryWordStoreMeasured.count request.precisionRuler first.1.1
  let third := BinaryWordStoreMeasured.count request.precisionRuler second.1.1
  have h1 := count_usage request.choiceRuler []
  have h2 := count_usage request.precisionRuler first.1.1
  have h3 := count_usage request.precisionRuler second.1.1
  have hw := stages_width request.choiceRuler request.precisionRuler
  change first.1.1.length ≤ _ ∧ second.1.1.length ≤ _ at hw
  change usage first.1.2 ≤ _ at h1
  change usage second.1.2 ≤ _ at h2
  change usage third.1.2 ≤ _ at h3
  have ht := wrap_usage 48 2 [first.1.2,second.1.2,third.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at ht
  change usage (prepare request).1.2 ≤ _ at ht
  simp only [List.length_nil] at h1
  simp only [request.choiceRuler_length,request.precisionRuler_length] at h1 h2 h3 hw
  unfold sampleBitBudget innerBitBudget
  omega

def generate {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    ((List Bool × S) × Trace) × ℕ :=
  let counter := prepare request
  let seed := BooleanFreshSeedMeasured.generate next counter.1.1 state
  ((seed.1.1,wrap 32 2 [counter.1.2,seed.1.2]),counter.2+seed.2+4)

theorem generate_reference {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (generate next request state).1.1 =
      (FreshBitSeedLifetime.generateWithTrace next (sampleBitBudget n request.request.precision) state).1 := by
  simp only [generate,BooleanFreshSeedMeasured.generate_erases,
    BooleanFreshBitSeedLoop.generate_state,prepare_value]

theorem generate_data {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (generate next request state).1.1 =
      (BinaryPRGSeedCountLifetime.generateWithTrace next request.request state).1 :=
  (generate_reference next request state).trans
    (BinaryPRGSeedCountLifetime.generate_state next request.request state).symm

theorem generate_counted {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) (calls : ℕ) :
    (generate (FreshBitSeedLifetime.countedFresh next) request (state,calls)).1.1 =
      ((generate next request state).1.1.1,((generate next request state).1.1.2,
        calls+sampleBitBudget n request.request.precision)) := by
  simp only [generate_reference,FreshBitSeedLifetime.generate_counted]

theorem generate_work {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (generate next request state).2 ≤
      128*(binaryWordWidth (sampleBitBudget n request.request.precision)+1)*
        (sampleBitBudget n request.request.precision+1)+32 := by
  have hp := prepare_work request
  have hs := BooleanFreshSeedMeasured.generate_work next (prepare request).1.1 state
  rw [prepare_value] at hs
  have hw := Nat.mul_le_mul_right (sampleBitBudget n request.request.precision+1)
    (Nat.mul_le_mul_left 32 (Nat.add_le_add_right (prepare_width request) 1))
  change (prepare request).2+
    (BooleanFreshSeedMeasured.generate next (prepare request).1.1 state).2+4 ≤ _
  nlinarith only [hp,hs,hw]

theorem generate_usage {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    usage (generate next request state).1.2 ≤
      512*(binaryWordWidth (sampleBitBudget n request.request.precision)+1)*
        (sampleBitBudget n request.request.precision+1)+128 := by
  have hp := prepare_usage request
  have hs : usage (BooleanFreshSeedMeasured.generate next (prepare request).1.1 state).1.2 ≤
      128*((prepare request).1.1.length+1)*(sampleBitBudget n request.request.precision+1)+64 := by
    rw [BooleanFreshSeedMeasured.generate_erases]
    simpa only [BooleanFreshBitSeedLoop.envelope,prepare_value,Nat.mul_zero,Nat.add_zero] using
      BooleanFreshBitSeedLoop.generate_usage next (prepare request).1.1 state
  have hw := Nat.mul_le_mul_right (sampleBitBudget n request.request.precision+1)
    (Nat.mul_le_mul_left 128 (Nat.add_le_add_right (prepare_width request) 1))
  have ht := wrap_usage 32 2 [(prepare request).1.2,
    (BooleanFreshSeedMeasured.generate next (prepare request).1.1 state).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at ht
  change usage (generate next request state).1.2 ≤ _ at ht
  nlinarith only [hp,hs,hw,ht]

theorem raw_bounds {S : Type*} (next : S → Bool × S) (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) (state : S) :
    (generate next parsed.1.2 state).2 ≤ 2000000*(frame.length+400)^2 ∧
      usage (generate next parsed.1.2 state).1.2 ≤ 2000000*(frame.length+400)^2 := by
  let N := sampleBitBudget parsed.1.1 parsed.1.2.request.precision
  have hOld := (BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead
  have hn := BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed hOld
  change N ≤ BinaryPRGSeedRequestBound.seedCountBound frame.length at hn
  unfold BinaryPRGSeedRequestBound.seedCountBound at hn
  have hw := BinaryPRGSeedOutputLifetimePolynomial.wordWidth_le N
  have hFirst : binaryWordWidth N+1 ≤ 8*(frame.length+400) := by omega
  have hSecond : N+1 ≤ 8*(frame.length+400) := by omega
  have hProduct : (binaryWordWidth N+1)*(N+1) ≤ 64*(frame.length+400)^2 := by
    exact (Nat.mul_le_mul hFirst hSecond).trans_eq (by ring)
  have hOne := Nat.one_le_pow 2 (frame.length+400) (by omega)
  have hp := generate_work next parsed.1.2 state
  have hs := generate_usage next parsed.1.2 state
  change (generate next parsed.1.2 state).2 ≤ 128*(binaryWordWidth N+1)*(N+1)+32 at hp
  change usage (generate next parsed.1.2 state).1.2 ≤ 512*(binaryWordWidth N+1)*(N+1)+128 at hs
  exact ⟨by nlinarith only [hp,hProduct,hOne],by nlinarith only [hs,hProduct,hOne]⟩

theorem physical_bounds {S : Type*} (next : S → Bool × S) (frame : List Bool)
    (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (state : S) :
    (generate next parsed.1.2.logical state).2 ≤ 2000000*(frame.length+400)^2 ∧
      usage (generate next parsed.1.2.logical state).1.2 ≤ 2000000*(frame.length+400)^2 := by
  have hRef := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_refines frame
  rw [hRead,Option.map_some] at hRef
  exact raw_bounds next frame (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hRef.symm state

end Blotto.BinaryPRGRulerSeedMeasured
