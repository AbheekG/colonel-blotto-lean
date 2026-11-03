import Blotto.BinaryPRGSeedCountLifetime

/-! Actual raw fresh-bit execution now derives and consumes a Boolean sample
counter. No scheduled natural-count producer or natural countdown is called.
All request gates/output/state semantics remain exactly the previous fresh
runner's. Counter/ruler preparation and old counter versions are retained in
the full raw-length trace. Other native scalar/reference contracts are separate. -/
namespace Blotto.BinaryPRGBooleanFreshRawLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000

def runWithTrace {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (Option (List Bool) × S) × Trace :=
  let decoded := BinaryPRGRawRequestLifetime.readWithTrace frame
  match decoded.1 with
  | none => ((none,state),wrap 24 2 [decoded.2])
  | some parsed =>
      if parsed.2 = [] then
        let seed := BinaryPRGSeedCountLifetime.generateWithTrace fresh parsed.1.2.request state
        let output := BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed.1.1
        ((output.1,seed.1.2),wrap 48 2 [decoded.2,seed.2,output.2])
      else ((none,state),wrap 32 2 [decoded.2])

theorem runWithTrace_state {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (runWithTrace fresh rich frame state).1 = (BinaryPRGFreshRawLifetime.runWithTrace fresh rich frame state).1 := by
  cases hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 with
  | none => simp only [runWithTrace,BinaryPRGFreshRawLifetime.runWithTrace,hRead]
  | some parsed =>
      by_cases hTail : parsed.2 = []
      · simp only [runWithTrace,BinaryPRGFreshRawLifetime.runWithTrace,hRead,ite_eq_left hTail]
        rw [BinaryPRGSeedCountLifetime.generate_state]
      · simp only [runWithTrace,BinaryPRGFreshRawLifetime.runWithTrace,hRead,ite_eq_right hTail]

theorem runWithTrace_counted {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) (calls : ℕ) :
    (runWithTrace (FreshBitSeedLifetime.countedFresh fresh) rich frame (state,calls)).1 =
      ((runWithTrace fresh rich frame state).1.1,((runWithTrace fresh rich frame state).1.2,
        calls+BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [runWithTrace_state,BinaryPRGFreshRawLifetime.runWithTrace_counted]

theorem accepted_returns {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (state : S) :
    ∃ bits : Fin (RationalLottoResourceSystem.sampleBitBudget prepared.1 prepared.2.request.precision) → Bool,
      (runWithTrace fresh rich frame state).1.1 = some (prepared.2.request.output rich bits) := by
  rw [runWithTrace_state]
  exact BinaryPRGFreshRawLifetime.accepted_returns fresh rich frame prepared hRead state

theorem usage_comparison {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ∃ seed : List Bool,usage (runWithTrace fresh rich frame state).2 ≤
      usage (BinaryPRGFullRawLifetime.runWithTrace rich frame seed).2+2000000*(frame.length+400)^2+64 := by
  cases hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 with
  | none =>
      refine ⟨[],?_⟩
      have h := BinaryPRGFreshRawLifetime.reject_usage 16 (BinaryPRGRawRequestLifetime.readWithTrace frame).2
      norm_num only at h
      simp only [runWithTrace,BinaryPRGFullRawLifetime.runWithTrace,hRead]
      omega
  | some parsed =>
      by_cases hTail : parsed.2 = []
      · let seed := BinaryPRGSeedCountLifetime.generateWithTrace fresh parsed.1.2.request state
        refine ⟨seed.1.1,?_⟩
        have hGen := BinaryPRGSeedCountLifetime.raw_usage fresh frame parsed hRead state
        have hInsert := BinaryPRGFreshRawLifetime.insert_usage (BinaryPRGRawRequestLifetime.readWithTrace frame).2 seed.2
          (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed.1.1).2
        change usage seed.2 ≤ _ at hGen
        simp only [runWithTrace,BinaryPRGFullRawLifetime.runWithTrace,hRead,ite_eq_left hTail]
        change usage (wrap 48 2 [(BinaryPRGRawRequestLifetime.readWithTrace frame).2,seed.2,
          (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed.1.1).2]) ≤
          usage (wrap 32 2 [(BinaryPRGRawRequestLifetime.readWithTrace frame).2,
            (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed.1.1).2])+2000000*(frame.length+400)^2+64
        omega
      · refine ⟨[],?_⟩
        have h := BinaryPRGFreshRawLifetime.reject_usage 24 (BinaryPRGRawRequestLifetime.readWithTrace frame).2
        norm_num only at h
        simp only [runWithTrace,BinaryPRGFullRawLifetime.runWithTrace,hRead,ite_eq_right hTail]
        omega

theorem uniform_usage : ∃ C d : ℕ,∀ {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    usage (runWithTrace fresh rich frame state).2 ≤ C*(frame.length+1)^d := by
  rcases BinaryPRGFullRawLifetime.uniform_usage with ⟨C,d,hBound⟩
  let A := 2000000*400^2
  refine ⟨C+A+64,d+2,?_⟩
  intro S fresh rich frame state
  obtain ⟨seed,hCompare⟩ := usage_comparison fresh rich frame state
  have hOld := hBound rich frame seed
  have hX : 0 < frame.length+1 := by omega
  have hUp := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (show d ≤ d+2 by omega))
  have hSquare := Nat.mul_le_mul_left A (Nat.pow_le_pow_right hX (show 2 ≤ d+2 by omega))
  have hOne := Nat.one_le_pow (d+2) (frame.length+1) hX
  have hScale := Nat.mul_le_mul_left 2000000
    (Nat.pow_le_pow_left (show frame.length+400 ≤ 400*(frame.length+1) by omega) 2)
  rw [Nat.mul_pow] at hScale
  dsimp only [A] at *
  nlinarith

theorem uniform_all_prefix : ∃ C d : ℕ,∀ {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool)
    (state : S) (borrowed steps : ℕ),
    retainedHeap (borrowed+frame.length) (runWithTrace fresh rich frame state).2 steps ≤
      borrowed+frame.length+C*(frame.length+1)^d ∧
    framePeak ((runWithTrace fresh rich frame state).2.take steps) ≤ C*(frame.length+1)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  exact ⟨C,d,fun fresh rich frame state borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound fresh rich frame state) _ steps⟩

end Blotto.BinaryPRGBooleanFreshRawLifetime
