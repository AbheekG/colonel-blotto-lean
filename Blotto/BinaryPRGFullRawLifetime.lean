import Blotto.BinaryPRGRawRequestLifetime
import Blotto.BinaryPRGSeedOutputLaw

/-! Complete raw request/seed/output execution. The actually produced typed
request feeds the actual seed validator and physical output path once. Every
parser/promise/accuracy/trailing-input/seed rejection gate is preserved.
Original request length bounds the entire retained trace; an arbitrary seed
contributes its original borrowed storage, not an untrusted workspace bound. -/
namespace Blotto.BinaryPRGFullRawLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option maxHeartbeats 3000000

def runWithTrace (rich : Bool) (frame seed : List Bool) : Option (List Bool) × Trace :=
  let decoded := BinaryPRGRawRequestLifetime.readWithTrace frame
  match decoded.1 with
  | none => (none,wrap 16 2 [decoded.2])
  | some parsed =>
      if parsed.2 = [] then
        let output := BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed
        (output.1,wrap 32 2 [decoded.2,output.2])
      else (none,wrap 24 2 [decoded.2])

theorem runWithTrace_state (rich : Bool) (frame seed : List Bool) :
    (runWithTrace rich frame seed).1 = BinaryPRGRequest.run rich frame seed := by
  have hRead := BinaryPRGAccuracyRulerRequest.read_state frame
  rw [← BinaryPRGRawRequestLifetime.readWithTrace_state] at hRead
  cases hd : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 with
  | none =>
      rw [hd,Option.map_none] at hRead
      simp only [runWithTrace,hd,BinaryPRGRequest.run,← hRead,Option.bind_none]
  | some parsed =>
      rw [hd,Option.map_some] at hRead
      simp only [runWithTrace,hd,BinaryPRGRequest.run,← hRead,Option.bind_some,BinaryPRGAccuracyRulerRequest.forget]
      split
      · exact BinaryPRGHeapSeedOutputLifetime.runWithTrace_request parsed.1.2 rich seed
      · rfl

theorem runWithTrace_returned_budget (rich : Bool) (frame seed bytes : List Bool)
    (h : (runWithTrace rich frame seed).1 = some bytes) :
    ∃ parsed : Σ n,BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords frame =
        some ((⟨parsed.1,parsed.2.source⟩ : Σ n,RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1 (if rich then parsed.2.source.a else parsed.2.source.b) bytes := by
  rw [runWithTrace_state] at h
  exact BinaryPRGRequest.run_returned_budget rich frame seed bytes h

theorem runWithTrace_ofFn (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (rich : Bool)
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    (runWithTrace rich frame (List.ofFn bits)).1 = some (prepared.2.request.output rich bits) := by
  unfold runWithTrace
  dsimp only
  rw [hRead]
  simp only [ite_true,BinaryPRGSeedOutputLaw.runWithTrace_ofFn]

theorem uniform_usage : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    usage (runWithTrace rich frame seed).2 ≤ C*(frame.length+1)^d := by
  rcases BinaryPRGSeedOutputLifetimePolynomial.uniform_usage with ⟨C,d,hSeed⟩
  let A := 500000000000000*8^8
  refine ⟨A+C*13^d+128,d+8,?_⟩
  intro rich frame seed
  let X := frame.length+1
  have hX : 0 < X := by dsimp [X]; omega
  have hOne := Nat.one_le_pow (d+8) X hX
  have hExtra := Nat.zero_le ((C*13^d)*X^(d+8))
  have hInput := (BinaryPRGRawRequestLifetime.readWithTrace_usage frame).trans
    (BinaryPRGRawRequestLifetime.envelope_polynomial frame.length)
  have hScale := Nat.mul_le_mul_left 500000000000000
    (Nat.pow_le_pow_left (show frame.length+8 ≤ 8*X by dsimp [X]; omega) 8)
  rw [Nat.mul_pow,← Nat.mul_assoc] at hScale
  have hInput' : usage (BinaryPRGRawRequestLifetime.readWithTrace frame).2 ≤ A*X^8 := hInput.trans hScale
  have hUp₈ : X^8 ≤ X^(d+8) := Nat.pow_le_pow_right hX (by omega)
  have hRead : usage (BinaryPRGRawRequestLifetime.readWithTrace frame).2 ≤ A*X^(d+8) :=
    hInput'.trans (Nat.mul_le_mul_left A hUp₈)
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryPRGRawRequestLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryPRGRawRequestLifetime.readWithTrace frame).2]) ≤ _
    change _ ≤ (A+C*13^d+128)*X^(d+8)
    nlinarith only [hw,hRead,hOne,hExtra]
  · rename_i parsed hParsed
    split
    · have hOld : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed :=
        (BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hParsed
      have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hOld
      have hs := BinaryPRGFrameCostJoin.read_source_width frame parsed hOld
      have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound frame parsed hOld
      have hSize : parsed.1.1+parsed.1.2.request.source.originalInputWordWidth+parsed.1.2.request.precision+2 ≤ 13*X := by
        dsimp [X]
        omega
      have hOut := (hSeed parsed.1.2 rich seed).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d))
      rw [Nat.mul_pow,← Nat.mul_assoc] at hOut
      have hUp : X^d ≤ X^(d+8) := Nat.pow_le_pow_right hX (by omega)
      have hOutput := hOut.trans (Nat.mul_le_mul_left (C*13^d) hUp)
      have hw := wrap_usage 32 2 [(BinaryPRGRawRequestLifetime.readWithTrace frame).2,
        (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 32 2 [(BinaryPRGRawRequestLifetime.readWithTrace frame).2,
        (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed).2]) ≤ _
      change _ ≤ (A+C*13^d+128)*X^(d+8)
      nlinarith only [hw,hRead,hOutput,hOne]
    · have hw := wrap_usage 24 2 [(BinaryPRGRawRequestLifetime.readWithTrace frame).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [(BinaryPRGRawRequestLifetime.readWithTrace frame).2]) ≤ _
      change _ ≤ (A+C*13^d+128)*X^(d+8)
      nlinarith only [hw,hRead,hOne,hExtra]

theorem uniform_all_prefix : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool) (borrowed steps : ℕ),
    retainedHeap (borrowed+frame.length+seed.length) (runWithTrace rich frame seed).2 steps ≤
      borrowed+frame.length+seed.length+C*(frame.length+1)^d ∧
    framePeak ((runWithTrace rich frame seed).2.take steps) ≤ C*(frame.length+1)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  exact ⟨C,d,fun rich frame seed borrowed steps => BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound rich frame seed) _ steps⟩

end Blotto.BinaryPRGFullRawLifetime
