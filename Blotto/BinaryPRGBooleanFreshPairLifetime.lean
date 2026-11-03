import Blotto.BinaryTerminalPhysicalFreshRawLifetime
import Blotto.BinaryPRGFreshPairLifetime

/-! Both consecutive players derive/use the actual Boolean seed countdown
after physical raw parsing, retain the returned physical stores through framed
output, and charge both complete parses. The previous bytes and entropy state
are preserved. -/
namespace Blotto.BinaryPRGBooleanFreshPairLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def runWithTrace {S : Type*} (fresh : S → Bool × S) (frame : List Bool) (state : S) :
    ((Option (List Bool) × Option (List Bool)) × S) × Trace :=
  let rich := BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh true frame state
  let poor := BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh false frame rich.1.2
  (((rich.1.1,poor.1.1),poor.1.2),wrap 64 2 [rich.2,poor.2])

theorem runWithTrace_state {S : Type*} (fresh : S → Bool × S) (frame : List Bool) (state : S) :
    (runWithTrace fresh frame state).1 = (BinaryPRGFreshPairLifetime.runWithTrace fresh frame state).1 := by
  simp only [runWithTrace,BinaryPRGFreshPairLifetime.runWithTrace,
    BinaryTerminalPhysicalFreshRawLifetime.runWithTrace_state,
    BinaryPRGBooleanFreshRawLifetime.runWithTrace_state]

theorem runWithTrace_counted {S : Type*} (fresh : S → Bool × S) (frame : List Bool) (state : S) (calls : ℕ) :
    (runWithTrace (FreshBitSeedLifetime.countedFresh fresh) frame (state,calls)).1 =
      ((runWithTrace fresh frame state).1.1,((runWithTrace fresh frame state).1.2,
        calls+2*BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [runWithTrace_state,BinaryPRGFreshPairLifetime.runWithTrace_counted]

theorem accepted_returns {S : Type*} (fresh : S → Bool × S)
    (frame : List Bool)
    (parsed : Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 =
      some (parsed,[])) (state : S) :
    ∃ richBits poorBits : Fin (RationalLottoResourceSystem.sampleBitBudget
        parsed.1 parsed.2.logical.request.precision) → Bool,
      (runWithTrace fresh frame state).1.1 =
        (some (parsed.2.logical.request.output true richBits),
          some (parsed.2.logical.request.output false poorBits)) := by
  let rich := BinaryTerminalPhysicalFreshRawLifetime.runWithTrace
    fresh true frame state
  obtain ⟨richBits,hRich⟩ := BinaryTerminalPhysicalFreshRawLifetime.accepted_returns
    fresh true frame parsed hRead state
  obtain ⟨poorBits,hPoor⟩ := BinaryTerminalPhysicalFreshRawLifetime.accepted_returns
    fresh false frame parsed hRead rich.1.2
  refine ⟨richBits,poorBits,?_⟩
  change (rich.1.1,
    (BinaryTerminalPhysicalFreshRawLifetime.runWithTrace
      fresh false frame rich.1.2).1.1) = _
  exact Prod.ext hRich hPoor

theorem runWithTrace_vector (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 =
      some (prepared,[]))
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget prepared.1
      prepared.2.request.precision+
      RationalLottoResourceSystem.sampleBitBudget prepared.1
        prepared.2.request.precision) → Bool) :
    (runWithTrace (FreshBitSeedLifetime.tapeFresh
      (FreshBitSeedLifetime.vectorTape bits)) frame 0).1 =
      ((some (prepared.2.request.output true
          (firstBitBlock _ _ bits)),
        some (prepared.2.request.output false
          (secondBitBlock _ _ bits))),
        RationalLottoResourceSystem.sampleBitBudget prepared.1
          prepared.2.request.precision+
        RationalLottoResourceSystem.sampleBitBudget prepared.1
          prepared.2.request.precision) := by
  rw [runWithTrace_state]
  exact BinaryPRGFreshPairLifetime.runWithTrace_vector frame prepared hRead bits

theorem uniform_usage : ∃ C d : ℕ,∀ {S : Type*} (fresh : S → Bool × S) (frame : List Bool) (state : S),
    usage (runWithTrace fresh frame state).2 ≤ C*(frame.length+1)^d := by
  rcases BinaryTerminalPhysicalFreshRawLifetime.uniform_usage with ⟨C,d,hBound⟩
  refine ⟨2*C+128,d,?_⟩
  intro S fresh frame state
  have hRich := hBound fresh true frame state
  have hPoor := hBound fresh false frame (BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh true frame state).1.2
  have hWrap := wrap_usage 64 2 [(BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh true frame state).2,
    (BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh false frame
      (BinaryTerminalPhysicalFreshRawLifetime.runWithTrace fresh true frame state).1.2).2]
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

end Blotto.BinaryPRGBooleanFreshPairLifetime
