import Blotto.BinaryPRGFreshRawLifetime

/-! Two consecutive whole-allocation draws use one fresh primitive state.
The poor player's draw starts at the rich player's returned entropy position.
Both raw executions, including both parses, are charged. No preformed seed
list is borrowed, no inter-field independence is asserted, and every source
version of both outputs is retained through the pair. -/
namespace Blotto.BinaryPRGFreshPairLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
open FreshBitSeedLifetime
set_option maxHeartbeats 3000000

def runWithTrace {S : Type*} (fresh : S → Bool × S) (frame : List Bool) (state : S) :
    ((Option (List Bool) × Option (List Bool)) × S) × Trace :=
  let rich := BinaryPRGFreshRawLifetime.runWithTrace fresh true frame state
  let poor := BinaryPRGFreshRawLifetime.runWithTrace fresh false frame rich.1.2
  (((rich.1.1,poor.1.1),poor.1.2),wrap 64 2 [rich.2,poor.2])

theorem runWithTrace_counted {S : Type*} (fresh : S → Bool × S) (frame : List Bool) (state : S) (calls : ℕ) :
    (runWithTrace (countedFresh fresh) frame (state,calls)).1 =
      ((runWithTrace fresh frame state).1.1,((runWithTrace fresh frame state).1.2,
        calls+2*BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [runWithTrace,BinaryPRGFreshRawLifetime.runWithTrace_counted]
  congr 2
  omega

theorem drawCount_bound (frame : List Bool) :
    2*BinaryPRGFreshRawLifetime.drawCount frame ≤ 16*frame.length+6050 := by
  have h := BinaryPRGFreshRawLifetime.drawCount_bound frame
  unfold BinaryPRGSeedRequestBound.seedCountBound at h
  omega

theorem runWithTrace_tape (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (tape : ℕ → Bool) (position : ℕ) :
    (runWithTrace (tapeFresh tape) frame position).1 =
      ((some (prepared.2.request.output true (fun i => tape (position+i.val))),
        some (prepared.2.request.output false
          (fun i => tape (position+sampleBitBudget prepared.1 prepared.2.request.precision+i.val)))),
        position+sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) := by
  simp only [runWithTrace,BinaryPRGFreshRawLifetime.runWithTrace_tape true frame prepared hRead,
    BinaryPRGFreshRawLifetime.runWithTrace_tape false frame prepared hRead]

theorem runWithTrace_vector (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    (runWithTrace (tapeFresh (vectorTape bits)) frame 0).1 =
      ((some (prepared.2.request.output true (firstBitBlock _ _ bits)),
        some (prepared.2.request.output false (secondBitBlock _ _ bits))),
        sampleBitBudget prepared.1 prepared.2.request.precision+sampleBitBudget prepared.1 prepared.2.request.precision) := by
  rw [runWithTrace_tape frame prepared hRead]
  have hFirst : (fun i : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) => vectorTape bits (0+i.val)) =
      firstBitBlock _ _ bits := by
    funext i
    simp only [Nat.zero_add,vectorTape,firstBitBlock]
    rw [dite_eq_left (by have h := i.isLt; omega)]
    rfl
  have hSecond : (fun i : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) =>
      vectorTape bits (0+sampleBitBudget prepared.1 prepared.2.request.precision+i.val)) = secondBitBlock _ _ bits := by
    funext i
    simp only [Nat.zero_add,vectorTape,secondBitBlock]
    rw [dite_eq_left (by have h := i.isLt; omega)]
    rfl
  rw [hFirst,hSecond,Nat.zero_add]

theorem uniform_usage : ∃ C d : ℕ,∀ {S : Type*} (fresh : S → Bool × S) (frame : List Bool) (state : S),
    usage (runWithTrace fresh frame state).2 ≤ C*(frame.length+1)^d := by
  rcases BinaryPRGFreshRawLifetime.uniform_usage with ⟨C,d,hBound⟩
  refine ⟨2*C+128,d,?_⟩
  intro S fresh frame state
  have hRich := hBound fresh true frame state
  have hPoor := hBound fresh false frame (BinaryPRGFreshRawLifetime.runWithTrace fresh true frame state).1.2
  have hWrap := wrap_usage 64 2 [(BinaryPRGFreshRawLifetime.runWithTrace fresh true frame state).2,
    (BinaryPRGFreshRawLifetime.runWithTrace fresh false frame
      (BinaryPRGFreshRawLifetime.runWithTrace fresh true frame state).1.2).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  have hOne := Nat.one_le_pow d (frame.length+1) (by omega)
  change usage (wrap 64 2 [_,_]) ≤ _
  nlinarith

theorem uniform_all_prefix : ∃ C d : ℕ,∀ {S : Type*} (fresh : S → Bool × S) (frame : List Bool)
    (state : S) (borrowed steps : ℕ),
    retainedHeap (borrowed+frame.length) (runWithTrace fresh frame state).2 steps ≤
      borrowed+frame.length+C*(frame.length+1)^d ∧
    framePeak ((runWithTrace fresh frame state).2.take steps) ≤ C*(frame.length+1)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  exact ⟨C,d,fun fresh frame state borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound fresh frame state) _ steps⟩

end Blotto.BinaryPRGFreshPairLifetime
