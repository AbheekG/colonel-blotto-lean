import Blotto.BinaryTerminalPhysicalEmissionSeed
import Blotto.BinaryTerminalPhysicalOutputRaw
import Blotto.BinaryTerminalPhysicalPreparedRaw

/-! Complete raw frames consume measured validation, cache prefix, terminal
emission/fallback and physical output. Original bytes and Boolean allowances
are preserved, including all rejection paths. Group factory/draw, row projection,
complete parser and native observer/reference/allocator prices remain separate. -/

namespace Blotto.BinaryTerminalPhysicalEmissionRaw
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (rich : Bool) (frame seed : List Bool) : ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none => (((none,[]),wrap 16 2 [decoded.2]),0)
  | some parsed =>
      if parsed.2 = [] then
        let output := BinaryTerminalPhysicalEmissionSeed.run frame parsed hParsed rich seed
        ((output.1.1,wrap 32 2 [decoded.2,output.1.2]),output.2)
      else (((none,[]),wrap 24 2 [decoded.2]),0)

theorem run_data (rich : Bool) (frame seed : List Bool) :
    (run rich frame seed).1.1 = (BinaryTerminalPhysicalOutputRaw.run rich frame seed).1.1 := by
  unfold run BinaryTerminalPhysicalOutputRaw.run
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i parsed hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,BinaryTerminalPhysicalEmissionSeed.run_data]
      · simp only [ite_eq_right hTail]

theorem accepted_charge (rich : Bool) (frame seed : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    (run rich frame seed).2+BinaryBigEndian.littleValue (run rich frame seed).1.1.2 =
      (BinaryTerminalPhysicalEmissionSeed.run frame parsed hRead rich seed).2+
        BinaryBigEndian.littleValue (BinaryTerminalPhysicalEmissionSeed.run frame parsed hRead rich seed).1.1.2 := by
  unfold run
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_left hTail]

theorem uniform_work : ∃ C d : ℕ, ∀ (rich : Bool) (frame seed : List Bool),
    (run rich frame seed).2+BinaryBigEndian.littleValue (run rich frame seed).1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalEmissionSeed.accepted_uniform_work
  refine ⟨C,d,?_⟩
  intro rich frame seed
  unfold run
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hParsed
    split
    · exact hBound frame parsed hParsed rich seed
    · exact Nat.zero_le _

theorem uniform_usage : ∃ C d : ℕ, ∀ (rich : Bool) (frame seed : List Bool),
    usage (run rich frame seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C₁,d₁,hOutput⟩ := BinaryTerminalPhysicalEmissionSeed.accepted_uniform_usage
  obtain ⟨C₂,d₂,hParser⟩ := BinaryTerminalPhysicalRawPolynomial.uniform_envelope
  let D := max d₁ d₂
  refine ⟨C₁+C₂+64,D,?_⟩
  intro rich frame seed
  have hX : 0 < frame.length+1 := by omega
  have hRead := (BinaryPRGPhysicalRawRequestLifetime.readWithTrace_usage frame).trans (hParser frame.length)
  have h₁ := Nat.mul_le_mul_left C₁ (Nat.pow_le_pow_right hX (Nat.le_max_left d₁ d₂))
  have h₂ := Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_right hX (Nat.le_max_right d₁ d₂))
  have hOne := Nat.one_le_pow D (frame.length+1) (by omega)
  unfold run
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
    dsimp only [D] at *
    nlinarith only [hw,hRead,h₂,hOne]
  · rename_i parsed hParsed
    split
    · let output := BinaryTerminalPhysicalEmissionSeed.run frame parsed hParsed rich seed
      have ho := hOutput frame parsed hParsed rich seed
      have hw := wrap_usage 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,output.1.2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage output.1.2 ≤ _ at ho
      change usage (wrap 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,output.1.2]) ≤ _
      dsimp only [D] at *
      nlinarith only [hw,hRead,ho,h₁,h₂,hOne]
    · have hw := wrap_usage 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
      dsimp only [D] at *
      nlinarith only [hw,hRead,h₂,hOne]

theorem all_prefixes : ∃ C d : ℕ, ∀ (rich : Bool) (frame seed : List Bool) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length+seed.length) (run rich frame seed).1.2 steps ≤
        borrowed+frame.length+seed.length+B ∧ framePeak ((run rich frame seed).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := uniform_usage
  exact ⟨C,d,fun rich frame seed borrowed steps =>
    all_prefix _ _ (hBound rich frame seed) (borrowed+frame.length+seed.length) steps⟩

end Blotto.BinaryTerminalPhysicalEmissionRaw
