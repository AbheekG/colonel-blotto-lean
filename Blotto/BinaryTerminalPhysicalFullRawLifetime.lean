import Blotto.BinaryTerminalPhysicalSeedOutputLifetime
import Blotto.BinaryTerminalPhysicalRawPolynomial
import Blotto.BinaryPRGFullRawLifetime

/-! A full raw request/seed/output execution retains accepted physical
numerical stores through the terminal route and final framed bytes. -/
namespace Blotto.BinaryTerminalPhysicalFullRawLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option maxHeartbeats 3000000

def runWithTrace (rich : Bool) (frame seed : List Bool) :
    Option (List Bool) × Trace :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none => (none,wrap 16 2 [decoded.2])
  | some parsed =>
      if parsed.2 = [] then
        let output := BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
          frame parsed hParsed rich seed
        (output.1,wrap 32 2 [decoded.2,output.2])
      else (none,wrap 24 2 [decoded.2])

theorem runWithTrace_state (rich : Bool) (frame seed : List Bool) :
    (runWithTrace rich frame seed).1 =
      (BinaryPRGFullRawLifetime.runWithTrace rich frame seed).1 := by
  have hRef := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_refines frame
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    rw [hNone,Option.map_none] at hRef
    simp only [BinaryPRGFullRawLifetime.runWithTrace,← hRef]
  · rename_i parsed hSome
    rw [hSome,Option.map_some] at hRef
    split
    · rename_i hTail
      simp only [BinaryPRGFullRawLifetime.runWithTrace,← hRef,
        BinaryPRGPhysicalRawRequestLifetime.forgetParsed,ite_eq_left hTail]
      exact BinaryTerminalPhysicalSeedOutputLifetime.accepted_state
        frame parsed hSome rich seed
    · rename_i hTail
      simp only [BinaryPRGFullRawLifetime.runWithTrace,← hRef,
        BinaryPRGPhysicalRawRequestLifetime.forgetParsed,ite_eq_right hTail]

theorem runWithTrace_request (rich : Bool) (frame seed : List Bool) :
    (runWithTrace rich frame seed).1 = BinaryPRGRequest.run rich frame seed := by
  rw [runWithTrace_state]
  exact BinaryPRGFullRawLifetime.runWithTrace_state rich frame seed

theorem returned_budget (rich : Bool) (frame seed bytes : List Bool)
    (h : (runWithTrace rich frame seed).1 = some bytes) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords frame =
        some ((⟨parsed.1,parsed.2.source⟩ :
          Σ n,RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1
        (if rich then parsed.2.source.a else parsed.2.source.b) bytes := by
  rw [runWithTrace_state] at h
  exact BinaryPRGFullRawLifetime.runWithTrace_returned_budget rich frame seed bytes h

theorem runWithTrace_ofFn (frame : List Bool)
    (parsed : Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 =
      some (parsed,[])) (rich : Bool)
    (bits : Fin (sampleBitBudget parsed.1
      parsed.2.logical.request.precision) → Bool) :
    (runWithTrace rich frame (List.ofFn bits)).1 =
      some (parsed.2.logical.request.output rich bits) := by
  rw [runWithTrace_state]
  have hRef := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_refines frame
  rw [hRead,Option.map_some] at hRef
  have hOld : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 =
      some ((⟨parsed.1,parsed.2.logical⟩ :
        Σ n,BinaryPRGAccuracyRulerRequest.Request n),[]) := by
    simpa only [BinaryPRGPhysicalRawRequestLifetime.forgetParsed] using hRef.symm
  exact BinaryPRGFullRawLifetime.runWithTrace_ofFn frame
    ⟨parsed.1,parsed.2.logical⟩ hOld rich bits

noncomputable def envelope (frame seed : List Bool) : ℕ :=
  BinaryPRGPhysicalRawRequestLifetime.envelope frame.length+
    ((BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1.map
      (fun parsed => if parsed.2 = [] then
        BinaryTerminalPhysicalSeedOutputLifetime.envelope frame parsed.1 seed
        else 0)).getD 0+128

theorem runWithTrace_usage (rich : Bool) (frame seed : List Bool) :
    usage (runWithTrace rich frame seed).2 ≤ envelope frame seed := by
  have hRead := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_usage frame
  unfold runWithTrace
  dsimp only
  split
  · rename_i hNone
    have hw := wrap_usage 16 2
      [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2
      [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
    unfold envelope
    rw [hNone]
    simp only [Option.map_none,Option.getD_none]
    omega
  · rename_i parsed hSome
    split
    · rename_i hTail
      have hOut := BinaryTerminalPhysicalSeedOutputLifetime.accepted_usage
        frame parsed hSome rich seed
      have hw := wrap_usage 32 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
          (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
            frame parsed hSome rich seed).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 32 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
          (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
            frame parsed hSome rich seed).2]) ≤ _
      unfold envelope
      rw [hSome]
      simp only [Option.map_some,Option.getD_some,ite_eq_left hTail]
      omega
    · rename_i hTail
      have hw := wrap_usage 24 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
      unfold envelope
      rw [hSome]
      simp only [Option.map_some,Option.getD_some,ite_eq_right hTail]
      omega

theorem uniform_after_parser : ∃ C d : ℕ, ∀ (rich : Bool)
    (frame seed : List Bool),
    usage (runWithTrace rich frame seed).2 ≤
      BinaryPRGPhysicalRawRequestLifetime.envelope frame.length+
        C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ :=
    BinaryTerminalPhysicalSeedOutputLifetime.accepted_uniform_polynomial
  refine ⟨C+128,d,?_⟩
  intro rich frame seed
  let X := frame.length+1
  have hOne : 1 ≤ X^d := Nat.one_le_pow d X (by dsimp only [X]; omega)
  have hRead := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_usage frame
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2
      [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2
      [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
    change _ ≤ BinaryPRGPhysicalRawRequestLifetime.envelope frame.length+
      (C+128)*X^d
    nlinarith only [hw,hRead,hOne]
  · rename_i parsed hParsed
    split
    · have hOut := hSeed frame parsed hParsed rich seed
      change usage (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
        frame parsed hParsed rich seed).2 ≤ C*X^d at hOut
      have hw := wrap_usage 32 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
          (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
            frame parsed hParsed rich seed).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 32 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
          (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
            frame parsed hParsed rich seed).2]) ≤ _
      change _ ≤ BinaryPRGPhysicalRawRequestLifetime.envelope frame.length+
        (C+128)*X^d
      nlinarith only [hw,hRead,hOut,hOne]
    · have hw := wrap_usage 24 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
      change _ ≤ BinaryPRGPhysicalRawRequestLifetime.envelope frame.length+
        (C+128)*X^d
      nlinarith only [hw,hRead,hOne]

theorem uniform_after_parser_all_prefix : ∃ C d : ℕ,
    ∀ (rich : Bool) (frame seed : List Bool) (borrowed steps : ℕ),
    retainedHeap (borrowed+frame.length+seed.length)
        (runWithTrace rich frame seed).2 steps ≤
        borrowed+frame.length+seed.length+
          BinaryPRGPhysicalRawRequestLifetime.envelope frame.length+
          C*(frame.length+1)^d ∧
      framePeak ((runWithTrace rich frame seed).2.take steps) ≤
        BinaryPRGPhysicalRawRequestLifetime.envelope frame.length+
          C*(frame.length+1)^d := by
  obtain ⟨C,d,hUsage⟩ := uniform_after_parser
  exact ⟨C,d,fun rich frame seed borrowed steps =>
    by simpa only [Nat.add_assoc] using
      BinaryPRGHeapTraceUsage.all_prefix _ _
        (hUsage rich frame seed) (borrowed+frame.length+seed.length) steps⟩

theorem uniform_usage : ∃ C d : ℕ, ∀ (rich : Bool)
    (frame seed : List Bool),
    usage (runWithTrace rich frame seed).2 ≤
      C*(frame.length+1)^d := by
  obtain ⟨C₁,d₁,hAfter⟩ := uniform_after_parser
  obtain ⟨C₂,d₂,hParser⟩ :=
    BinaryTerminalPhysicalRawPolynomial.uniform_envelope
  refine ⟨C₁+C₂,max d₁ d₂,?_⟩
  intro rich frame seed
  let X := frame.length+1
  have hX : 0 < X := by dsimp only [X]; omega
  have h := hAfter rich frame seed
  have hp := hParser frame.length
  have h1 : X^d₁ ≤ X^(max d₁ d₂) :=
    Nat.pow_le_pow_right hX (Nat.le_max_left _ _)
  have h2 : X^d₂ ≤ X^(max d₁ d₂) :=
    Nat.pow_le_pow_right hX (Nat.le_max_right _ _)
  have h1' := Nat.mul_le_mul_left C₁ h1
  have h2' := Nat.mul_le_mul_left C₂ h2
  change usage (runWithTrace rich frame seed).2 ≤
    BinaryPRGPhysicalRawRequestLifetime.envelope frame.length+C₁*X^d₁ at h
  change BinaryPRGPhysicalRawRequestLifetime.envelope frame.length ≤
    C₂*X^d₂ at hp
  change _ ≤ (C₁+C₂)*X^(max d₁ d₂)
  nlinarith only [h,hp,h1',h2']

theorem uniform_usage_all_prefix : ∃ C d : ℕ,
    ∀ (rich : Bool) (frame seed : List Bool) (borrowed steps : ℕ),
    retainedHeap (borrowed+frame.length+seed.length)
        (runWithTrace rich frame seed).2 steps ≤
        borrowed+frame.length+seed.length+C*(frame.length+1)^d ∧
      framePeak ((runWithTrace rich frame seed).2.take steps) ≤
        C*(frame.length+1)^d := by
  obtain ⟨C,d,hUsage⟩ := uniform_usage
  exact ⟨C,d,fun rich frame seed borrowed steps =>
    by simpa only [Nat.add_assoc] using
      BinaryPRGHeapTraceUsage.all_prefix _ _
        (hUsage rich frame seed) (borrowed+frame.length+seed.length) steps⟩

theorem all_prefix (rich : Bool) (frame seed : List Bool)
    (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length+seed.length)
        (runWithTrace rich frame seed).2 steps ≤
        borrowed+frame.length+seed.length+envelope frame seed ∧
      framePeak ((runWithTrace rich frame seed).2.take steps) ≤
        envelope frame seed :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (runWithTrace_usage rich frame seed) _ steps

end Blotto.BinaryTerminalPhysicalFullRawLifetime
