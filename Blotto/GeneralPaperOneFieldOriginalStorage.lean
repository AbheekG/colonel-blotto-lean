import Blotto.GeneralPaperOneFieldOriginalResources
import Blotto.GeneralPaperIndexedArrayLifetime
import Blotto.GeneralPaperNaturalScalarLifetime

/-! Encoded lifetimes of the actual one-field constructor in the paper array
model. There are two sequential singleton fills. The second retains the
first returned row. Each cursor counts both prefix buffers, its activation
frames, the copied rational and the enclosing dispatch fields. Returned
rows use the same array contents as the executed constructor. -/
namespace Blotto.GeneralPaperOneFieldOriginalStorage
open GeneralPaperOriginalGameInput GeneralPaperOriginalHeadlineParameters
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile)
open GeneralPaperEncodedScalarStorage (fields fields_bound natBits)
open GeneralPaperIndexedArrayLifetime
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def callback (b : ℚ) (j : Fin 1) : ℚ × ℕ := (if j = 0 then b else 0, 8)

def row (b : ℚ) : FixedArrayTable 1 ℚ :=
  (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (callback b)).1

theorem row_actual (b : ℚ) : (row b).data =
    (GeneralPaperEqualRealBoundaryScan.vertex b (0 : Fin 1)).1.data := rfl

theorem row_read (b : ℚ) (j : Fin 1) : (row b).read j = b := by
  unfold row
  rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
  simp [callback, Fin.eq_zero j]

theorem row_foot (b : ℚ) : arrayFootprint 1 rationalWordWidth (row b) = 65 + rationalWordWidth b := by
  simp only [arrayFootprint, row_read, Fin.sum_univ_one]
  omega

theorem source_work (b : ℚ) :
    (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (callback b)).2 = 68 := by
  rw [PaperIndexedArrayConstruction.run_work]
  norm_num [callback, PaperIndexedArrayConstruction.overhead,
    PaperIndexedArrayConstruction.initialWork, PaperIndexedArrayConstruction.stepWork]

theorem vertex_work (b : ℚ) :
    (GeneralPaperEqualRealBoundaryScan.vertex b (0 : Fin 1)).2 = 100 := by
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (callback b)).2 + 32 = 100
  rw [source_work]

theorem pair_work (b : ℚ) : (GeneralPaperOneFieldRealPreparation.run 1 b).2 = 232 := by
  change (GeneralPaperEqualRealBoundaryScan.vertex 1 (0 : Fin 1)).2 +
    (GeneralPaperEqualRealBoundaryScan.vertex b (0 : Fin 1)).2 + 32 = 232
  rw [vertex_work, vertex_work]

def description (p : Input) : ℕ :=
  arrayFootprint 1 rationalWordWidth (row 1) + arrayFootprint 1 rationalWordWidth (row p.budget) +
    fields 1 [(GeneralPaperOneFieldRealPreparation.run 1 p.budget).2] + 128

theorem description_bound (p : Input) : description p ≤ 1024 * inputSize p := by
  have hi := input_positive p
  have hb : rationalWordWidth p.budget + 1 ≤ inputSize p := by unfold inputSize; omega
  have hOne : rationalWordWidth (1 : ℚ) = 3 := by decide
  have h232 : binaryWordWidth 232 = 8 := by decide
  norm_num [description, row_foot, pair_work, fields, natBits, hOne, h232]
  omega

def controls (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) : ℕ :=
  fields 1 [p.n, (GeneralPaperEqualRealBoundaryScan.vertex 1 (0 : Fin 1)).2,
    (GeneralPaperEqualRealBoundaryScan.vertex p.budget (0 : Fin 1)).2,
    (GeneralPaperOneFieldRealPreparation.run 1 p.budget).2,
    (GeneralPaperAllBranchBitDispatch.one p hN).2,
    (GeneralPaperMeasuredBitDispatch.run model K p).2] + 128

inductive Phase
  | constructing (poor : Bool) (cursor : ℕ) (valid : cursor ≤ 1)
  | returned

def window (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) : Phase → ℕ
  | .constructing poor k hk =>
    let b := if poor then p.budget else 1
    2 * inputSize p + controls model K p hN +
      (if poor then arrayFootprint 1 rationalWordWidth (row 1) else 0) +
      2 * arrayFootprint 1 rationalWordWidth (prefixTable (fun _ => 1) 1 (callback b) k hk) +
      activationFoot (fun _ => 1) 1 (callback b) k hk + rationalWordWidth b + 64
  | .returned => 2 * inputSize p + description p

theorem controls_bound (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) :
    controls model K p hN ≤ 16384 * inputSize p := by
  have hi := input_positive p
  have hw := GeneralPaperOneFieldOriginalResources.work model K p hN
  have ho : (GeneralPaperAllBranchBitDispatch.one p hN).2 ≤
      (GeneralPaperMeasuredBitDispatch.run model K p).2 := by
    rw [GeneralPaperMeasuredBitDispatch.on_one model K p hN]
    omega
  have hf := fields_bound 1 (2048 * inputSize p + 2)
    [p.n, (GeneralPaperEqualRealBoundaryScan.vertex 1 (0 : Fin 1)).2,
      (GeneralPaperEqualRealBoundaryScan.vertex p.budget (0 : Fin 1)).2,
      (GeneralPaperOneFieldRealPreparation.run 1 p.budget).2,
      (GeneralPaperAllBranchBitDispatch.one p hN).2,
      (GeneralPaperMeasuredBitDispatch.run model K p).2] (by
        intro x hx
        have h := GeneralPaperNaturalScalarLifetime.counter_word x
        simp only [List.mem_cons, List.not_mem_nil, or_false, vertex_work, pair_work, hN] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields 1 _ ≤ 6 * (2048 * inputSize p + 2 + 1) + 32 at hf
  unfold controls
  omega

theorem cursor_bound (b : ℚ) (k : ℕ) (hk : k ≤ 1) :
    2 * arrayFootprint 1 rationalWordWidth (prefixTable (fun _ => 1) 1 (callback b) k hk) +
      activationFoot (fun _ => 1) 1 (callback b) k hk ≤ 2 * rationalWordWidth b + 512 := by
  have hp := prefix_payload (fun _ => 1) 1 (callback b) rationalWordWidth
    (rationalWordWidth b) (by intro j; simp [callback, Fin.eq_zero j]) k hk
  have ha := activation_bound (fun _ => 1) 1 (callback b) k hk
  rw [source_work] at ha
  have hf : frame 1 1 68 = 91 := by decide
  rw [hf] at ha
  unfold arrayProfile at hp
  omega

theorem all_phases (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1)
    (phase : Phase) : window model K p hN phase ≤ 32768 * inputSize p := by
  have hi := input_positive p
  have hb : rationalWordWidth p.budget + 1 ≤ inputSize p := by unfold inputSize; omega
  have hc := controls_bound model K p hN
  have hOne : rationalWordWidth (1 : ℚ) = 3 := by decide
  cases phase with
  | constructing poor k hk =>
    have h := cursor_bound (if poor then p.budget else 1) k hk
    cases poor <;> simp only [window, Bool.false_eq_true, ↓reduceIte, row_foot, hOne] at h ⊢ <;> omega
  | returned =>
    have h := description_bound p
    change 2 * inputSize p + description p ≤ _
    omega

theorem description_headline (p : Input) : (description p : ℚ) ≤
    1024 * descriptionScale p * (logarithm p : ℚ) ^ 0 := by
  have h : (description p : ℚ) ≤ 1024 * (inputSize p : ℚ) := by exact_mod_cast description_bound p
  have hm := mul_le_mul_of_nonneg_left (description_ge_input p) (by norm_num : (0 : ℚ) ≤ 1024)
  simpa only [pow_zero, mul_one] using h.trans hm

theorem space_headline (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1)
    (phase : Phase) : (window model K p hN phase : ℚ) ≤
      32768 * spaceScale p * (logarithm p : ℚ) ^ 0 := by
  have h : (window model K p hN phase : ℚ) ≤ 32768 * (inputSize p : ℚ) := by
    exact_mod_cast all_phases model K p hN phase
  have hm := mul_le_mul_of_nonneg_left (space_ge_input p) (by norm_num : (0 : ℚ) ≤ 32768)
  simpa only [pow_zero, mul_one] using h.trans hm

end Blotto.GeneralPaperOneFieldOriginalStorage
