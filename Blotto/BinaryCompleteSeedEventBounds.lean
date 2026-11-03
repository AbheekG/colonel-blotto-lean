import Blotto.BinaryCompleteSeedCharges

/-! Actual seed-wrapper event counts have a frame-only envelope, including
validation rejection and overlong seed inputs. -/
namespace Blotto.BinaryCompleteSeedEventBounds
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryTerminalPhysicalCompleteSeedMeasured
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem accepted_trace : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (seed : List Bool),
    (run frame parsed hParsed rich seed).1.2.length ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hFramed⟩ := BinaryCompleteSeedCharges.framed_joint
  let D := max d 1
  refine ⟨C+2000000,D,?_⟩
  intro frame parsed hParsed rich seed
  let prepared := BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed
  let X := frame.length+1
  have hX : 0 < X := by dsimp only [X]; omega
  have hPW := BinaryTerminalPhysicalPreparationWork.preparation_frame_bound frame parsed hParsed seed
  have hPT := BinarySeedValidationTraceBounds.preparation_length parsed.1.2.logical seed
  change prepared.2 ≤ 128000*X at hPW
  change prepared.1.2.length ≤ prepared.2+5 at hPT
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d 1))
  have hLinear : X ≤ X^D := by simpa only [pow_one] using Nat.pow_le_pow_right hX (Nat.le_max_right d 1)
  have hOne : 1 ≤ X^D := Nat.one_le_pow _ _ (by omega)
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · simp only [wrap,combine,List.length_append,under_length,List.length_cons,List.length_nil]
    dsimp only [prepared,X,D] at *
    nlinarith only [hPW,hPT,hLinear,hOne]
  · rename_i held hPrepared
    obtain ⟨blocks,hHeld⟩ := prepared_some parsed.1.2.logical seed held hPrepared
    subst held
    have hf := hFramed frame parsed hParsed rich blocks
    have hs := BinarySeedValidationTraceBounds.store_length frame parsed hParsed blocks
    simp only [wrap,combine,List.length_append,under_length,List.length_cons,List.length_nil]
    rw [BinaryTerminalPhysicalCompleteFramedMeasured.run]
    dsimp only [prepared,X,D] at *
    nlinarith only [hf,hs,hPW,hPT,hd,hLinear,hOne]

end Blotto.BinaryCompleteSeedEventBounds
