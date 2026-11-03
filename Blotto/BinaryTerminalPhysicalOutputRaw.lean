import Blotto.BinaryTerminalPhysicalOutputSeed
import Blotto.BinaryTerminalPhysicalPreparedRaw

/-! Complete raw frames consume measured preparation/output once, with exact
preceding bytes, Boolean allowances and traces. The natural charge now covers
validation, physical choice store, cache prefix and physical output. Remaining
terminal/fallback, row projection, parser and native prices are separate. -/

namespace Blotto.BinaryTerminalPhysicalOutputRaw
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
        let output := BinaryTerminalPhysicalOutputSeed.run frame parsed hParsed rich seed
        ((output.1.1,wrap 32 2 [decoded.2,output.1.2]),output.2)
      else (((none,[]),wrap 24 2 [decoded.2]),0)

theorem run_erases (rich : Bool) (frame seed : List Bool) :
    (run rich frame seed).1 = (BinaryTerminalPhysicalPreparedRaw.raw rich frame seed).1 := by
  unfold run BinaryTerminalPhysicalPreparedRaw.raw
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
      · simp only [ite_eq_left hTail,BinaryTerminalPhysicalOutputSeed.run_erases]
      · simp only [ite_eq_right hTail]

theorem accepted_charge (rich : Bool) (frame seed : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    (run rich frame seed).2+BinaryBigEndian.littleValue (run rich frame seed).1.1.2 =
      (BinaryTerminalPhysicalPreparationWork.run frame parsed hRead rich seed).2+
        BinaryBigEndian.littleValue (BinaryTerminalPhysicalPreparationWork.run frame parsed hRead rich seed).1.1.2+
          BinaryTerminalPhysicalOutputSeed.outputCharge frame parsed hRead rich seed := by
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
    exact BinaryTerminalPhysicalOutputSeed.run_total_work frame parsed hRead rich seed

theorem uniform_work : ∃ C d : ℕ, ∀ (rich : Bool) (frame seed : List Bool),
    (run rich frame seed).2+BinaryBigEndian.littleValue (run rich frame seed).1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalOutputSeed.accepted_uniform_work
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
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalPreparedRaw.raw_uniform_usage
  refine ⟨C,d,?_⟩
  intro rich frame seed
  rw [run_erases]
  exact hBound rich frame seed

theorem all_prefixes : ∃ C d : ℕ, ∀ (rich : Bool) (frame seed : List Bool) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length+seed.length) (run rich frame seed).1.2 steps ≤
        borrowed+frame.length+seed.length+B ∧ framePeak ((run rich frame seed).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := uniform_usage
  exact ⟨C,d,fun rich frame seed borrowed steps =>
    all_prefix _ _ (hBound rich frame seed) (borrowed+frame.length+seed.length) steps⟩

end Blotto.BinaryTerminalPhysicalOutputRaw
