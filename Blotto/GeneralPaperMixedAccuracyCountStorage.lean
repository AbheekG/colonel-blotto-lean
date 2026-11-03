import Blotto.GeneralPaperMeasuredUnequalDispatchHeadlines

/-! Store the actual counter run priced at A using physical reference S.
The input is owned once and all recursive frames remain counted. -/
namespace Blotto.GeneralPaperMixedAccuracyCountStorage
open GeneralPaperEncodedScalarStorage GeneralPaperBinaryAccuracy
open GeneralPaperAccuracyCountConstructionStorage (controls cap price width frameProfile profile)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def frame (S A : ℕ) (bits : List Bool) : ℕ :=
  fields S (controls A bits) + 128 * S + 1 + match bits with
  | [] => 0
  | _ :: rest => GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a + b) (count (fun w => w) A rest).1 1

def frames (S A : ℕ) : List Bool → ℕ
  | [] => frame S A []
  | b :: rest => frame S A (b :: rest) + frames S A rest

def window (S A : ℕ) (bits : List Bool) : ℕ :=
  listFootprint S (fun _ : Bool => 1) bits + frames S A bits

theorem work_cap (S A E : ℕ) (h : A ≤ S) (bits : List Bool) (hc : bits.length ≤ E) :
    (count (fun w => w) A bits).2 ≤ price S E :=
  (GeneralPaperMeasuredInitializerMonotonicity.count A S h bits).trans
    (GeneralPaperAccuracyCountConstructionStorage.work_cap S E bits hc)

theorem controls_cap (S A E : ℕ) (h : A ≤ S) (bits : List Bool) (hc : bits.length ≤ E) :
    ∀ z ∈ controls A bits, z ≤ cap S E := by
  have hw := work_cap S A E h bits hc
  have hn : (count (fun w => w) A bits).1 ≤ E := by rw [count_data]; exact hc
  intro z hz
  cases bits with
  | nil =>
    simp only [controls, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    unfold cap
    rcases hz with (rfl | rfl) | rfl <;> omega
  | cons b rest =>
    have hr : rest.length ≤ E := by simp only [List.length_cons] at hc; omega
    have ho := work_cap S A E h rest hr
    have hOld : (count (fun w => w) A rest).1 ≤ E := by rw [count_data]; exact hr
    have ha := GeneralPaperAccuracyCountConstructionStorage.addition A E rest hr
    simp only [controls, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    unfold cap
    rcases hz with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem control_count (A : ℕ) (bits : List Bool) : (controls A bits).length ≤ 8 := by
  cases bits <;> simp [controls]

theorem frame_bound (S A E : ℕ) (h : A ≤ S) (bits : List Bool) (hc : bits.length ≤ E) :
    frame S A bits ≤ frameProfile S E := by
  have hf := GeneralPaperExpressionArrayReturns.fields_mono_cap S (cap S E) (controls A bits)
    (controls_cap S A E h bits hc)
  have hF := hf.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right (natBits (cap S E) + S) (control_count A bits)) (32 * S))
  cases bits with
  | nil =>
    dsimp only [frame]
    unfold frameProfile
    omega
  | cons b rest =>
    have hr : rest.length ≤ E := by simp only [List.length_cons] at hc; omega
    have ha := GeneralPaperAccuracyCountConstructionStorage.addition A E rest hr
    dsimp only [frame]
    unfold frameProfile
    omega

theorem frames_bound (S A E : ℕ) (h : A ≤ S) (bits : List Bool) (hc : bits.length ≤ E) :
    frames S A bits ≤ (bits.length + 1) * frameProfile S E := by
  induction bits with
  | nil => simpa only [frames, List.length_nil, Nat.zero_add, Nat.one_mul] using frame_bound S A E h [] hc
  | cons b rest ih =>
    have hf := frame_bound S A E h (b :: rest) hc
    have hi := ih (by simp only [List.length_cons] at hc; omega)
    rw [frames]
    exact (Nat.add_le_add hf hi).trans_eq (by simp only [List.length_cons]; ring)

theorem bounded (S A E : ℕ) (h : A ≤ S) (bits : List Bool) (hc : bits.length ≤ E) :
    window S A bits ≤ profile S E := by
  have hf := frames_bound S A E h bits hc
  have hF := hf.trans (Nat.mul_le_mul_right (frameProfile S E) (Nat.add_le_add_right hc 1))
  have hi := list_bound S 1 (fun _ : Bool => 1) bits (fun _ _ => le_rfl)
  have hI := hi.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (1 + 2 * S) hc) _)
  exact Nat.add_le_add hI hF

theorem frame_diagonal (S : ℕ) (bits : List Bool) : frame S S bits = GeneralPaperAccuracyCountConstructionStorage.frame S bits := rfl

theorem frames_diagonal (S : ℕ) (bits : List Bool) : frames S S bits = GeneralPaperAccuracyCountConstructionStorage.frames S bits := by
  induction bits with
  | nil => rfl
  | cons b rest ih => simp only [frames, GeneralPaperAccuracyCountConstructionStorage.frames, frame_diagonal, ih]

theorem window_diagonal (S : ℕ) (bits : List Bool) : window S S bits = GeneralPaperAccuracyCountConstructionStorage.window S bits := by
  rw [window, frames_diagonal]
  rfl

end Blotto.GeneralPaperMixedAccuracyCountStorage
