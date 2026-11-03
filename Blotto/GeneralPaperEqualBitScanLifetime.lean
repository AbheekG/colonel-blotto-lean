import Blotto.GeneralPaperEqualBitVertexLifetime
import Blotto.GeneralPaperPackingAllocationLifetime

/-! The measured heavy scan owns one materialized length array and one
shared index list. Its literal reached recursion retains scalar comparison
scratch, encoded work/control fields and references, never copies of tails.
Index construction is reserved alongside the complete reached scan. -/
namespace Blotto.GeneralPaperEqualBitScanLifetime
open GeneralPaperEncodedScalarStorage
open GeneralPaperEqualBitBoundaryScan (scan stepBound)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def optionCode {n : ℕ} : Option (Fin n) → ℕ
  | none => 0
  | some j => j.val + 1

theorem option_bound {n : ℕ} (x : Option (Fin n)) : optionCode x ≤ n := by
  cases x <;> dsimp only [optionCode] <;> omega

def workCap (W n S : ℕ) : ℕ := n * S + 32 * W + 32
def metadataCap (W n S : ℕ) : ℕ := n + 1 + workCap W n S + S + 64 * W + 64
def frameProfile (W n P S : ℕ) : ℕ :=
  8 * (natBits (metadataCap W n S) + W) + 224 * W + 32 * S + P + 3

def frame {n : ℕ} (model : RationalCostModel) (W : ℕ) (lengths : FixedArrayTable n ℚ) : List (Fin n) → ℕ
  | [] => fields W [n,0,0,32 * W + 32,(scan model W lengths []).2] + 128 * W
  | j :: rest =>
    let tested := GeneralPaperExpressionBitExecution.compare model W 1 (lengths.read j)
    let header := 64 * (W + binaryWordWidth (j.val + 1) + 1)
    let result := scan model W lengths (j :: rest)
    fields W [n,(j :: rest).length,j.val,optionCode result.1,tested.2,header,result.2,tested.2 + header] +
      192 * W + GeneralPaperExpressionStorageBudget.compareFrame model W 1 (lengths.read j) +
      rationalWordWidth (lengths.read j) + 3

theorem frame_bound {n : ℕ} (model : RationalCostModel) (W P : ℕ)
    (lengths : FixedArrayTable n ℚ) (hP : 3 ≤ P)
    (hp : ∀ j, rationalWordWidth (lengths.read j) ≤ P)
    (items : List (Fin n)) (hlen : items.length ≤ n) :
    frame model W lengths items ≤ frameProfile W n P (stepBound model W n P) := by
  let S := stepBound model W n P
  have hSource := GeneralPaperEqualBitBoundaryScan.scan_work model W P lengths hP hp items
  change (scan model W lengths items).2 ≤ items.length * S + 32 * W + 32 at hSource
  have hWork : (scan model W lengths items).2 ≤ workCap W n S := by
    have hm := Nat.mul_le_mul_right S hlen
    dsimp only [workCap]
    omega
  cases items with
  | nil =>
    have hf := fields_bound W (natBits (metadataCap W n S)) [n,0,0,32 * W + 32,(scan model W lengths []).2] (by
      intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals dsimp only [metadataCap, workCap, scan]; omega)
    change fields W _ ≤ 5 * (natBits (metadataCap W n S) + W) + 32 * W at hf
    change frame model W lengths [] ≤ frameProfile W n P S
    dsimp only [frame, frameProfile]
    omega
  | cons j rest =>
    let tested := GeneralPaperExpressionBitExecution.compare model W 1 (lengths.read j)
    let header := 64 * (W + binaryWordWidth (j.val + 1) + 1)
    let result := scan model W lengths (j :: rest)
    have hStep : tested.2 + header ≤ S := GeneralPaperEqualBitBoundaryScan.compare_work model W P lengths hP hp j
    have hResult : result.2 ≤ workCap W n S := hWork
    have hOption := option_bound result.1
    have hScratch := GeneralPaperExpressionStorageBudget.compare_frame_bound model W 1 (lengths.read j)
    change GeneralPaperExpressionStorageBudget.compareFrame model W 1 (lengths.read j) ≤ 32 * tested.2 at hScratch
    have hValue := hp j
    have hf := fields_bound W (natBits (metadataCap W n S))
      [n,(j :: rest).length,j.val,optionCode result.1,tested.2,header,result.2,tested.2 + header] (by
        intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals unfold metadataCap; omega)
    change fields W _ ≤ 8 * (natBits (metadataCap W n S) + W) + 32 * W at hf
    change frame model W lengths (j :: rest) ≤ frameProfile W n P S
    dsimp only [frame, frameProfile]
    change fields W [n,(j :: rest).length,j.val,optionCode result.1,tested.2,header,result.2,tested.2 + header] +
      192 * W + GeneralPaperExpressionStorageBudget.compareFrame model W 1 (lengths.read j) +
      rationalWordWidth (lengths.read j) + 3 ≤ _
    omega

def frames {n : ℕ} (model : RationalCostModel) (W : ℕ) (lengths : FixedArrayTable n ℚ) : List (Fin n) → ℕ
  | [] => frame model W lengths []
  | j :: rest => frame model W lengths (j :: rest) +
    if (GeneralPaperExpressionBitExecution.compare model W 1 (lengths.read j)).1 then 0
    else frames model W lengths rest

theorem frames_bound {n : ℕ} (model : RationalCostModel) (W P : ℕ)
    (lengths : FixedArrayTable n ℚ) (hP : 3 ≤ P)
    (hp : ∀ j, rationalWordWidth (lengths.read j) ≤ P)
    (items : List (Fin n)) (hlen : items.length ≤ n) :
    frames model W lengths items ≤ (items.length + 1) * frameProfile W n P (stepBound model W n P) := by
  induction items with
  | nil => simpa only [frames, List.length_nil, Nat.zero_add, Nat.one_mul] using frame_bound model W P lengths hP hp [] hlen
  | cons j rest ih =>
    have hf := frame_bound model W P lengths hP hp (j :: rest) hlen
    have hi := ih (by simp only [List.length_cons] at hlen; omega)
    rw [frames]
    split_ifs <;> simp only [List.length_cons] <;> nlinarith only [hf, hi, Nat.zero_le (rest.length * frameProfile W n P (stepBound model W n P))]

def window {n : ℕ} (model : RationalCostModel) (W : ℕ) (lengths : FixedArrayTable n ℚ) (cursor : ℕ) : ℕ :=
  let ids := GeneralPaperEqualRouteConstruction.indices lengths.data.size lengths.size
  GeneralPaperEncodedBasisStorage.arrayFootprint W rationalWordWidth lengths +
    listFootprint W (fun i => natBits i.val) ids +
    GeneralPaperPackingAllocationLifetime.indicesLive W n cursor + frames model W lengths ids +
    fields W [n,cursor,optionCode (GeneralPaperEqualBitBoundaryScan.run model W lengths).1,
      (GeneralPaperEqualBitBoundaryScan.run model W lengths).2] + 128 * W

def totalWork (model : RationalCostModel) (W n P : ℕ) : ℕ :=
  n * stepBound model W n P + GeneralPaperEqualRouteConstruction.indicesWork W n + 96 * W + 96
def parentCap (model : RationalCostModel) (W n P : ℕ) : ℕ := n + 1 + totalWork model W n P
def profile (model : RationalCostModel) (W n P : ℕ) : ℕ :=
  GeneralPaperEncodedBasisStorage.arrayProfile W n P +
    GeneralPaperPositiveScanLifetime.labelProfile W n n +
    GeneralPaperPackingAllocationLifetime.indicesProfile W n +
    (n + 1) * frameProfile W n P (stepBound model W n P) +
    4 * (natBits (parentCap model W n P) + W) + 160 * W

theorem all_cursors {n : ℕ} (model : RationalCostModel) (W P : ℕ)
    (lengths : FixedArrayTable n ℚ) (hP : 3 ≤ P)
    (hp : ∀ j, rationalWordWidth (lengths.read j) ≤ P)
    (cursor : ℕ) (hcursor : cursor ≤ n) :
    window model W lengths cursor ≤ profile model W n P := by
  have hArray := GeneralPaperEncodedBasisStorage.array_bound W P rationalWordWidth lengths hp
  have hList := GeneralPaperPositiveScanLifetime.labels_bound W (List.finRange n) n (by rw [List.length_finRange])
  have hIndices := GeneralPaperPackingAllocationLifetime.indices_bound W n cursor hcursor
  have hFrames := frames_bound model W P lengths hP hp (List.finRange n) (by rw [List.length_finRange])
  rw [List.length_finRange] at hFrames
  have hWork := GeneralPaperEqualBitBoundaryScan.run_work model W P lengths hP hp
  change (GeneralPaperEqualBitBoundaryScan.run model W lengths).2 ≤ totalWork model W n P at hWork
  have hOption := option_bound (GeneralPaperEqualBitBoundaryScan.run model W lengths).1
  have hf := fields_bound W (natBits (parentCap model W n P))
    [n,cursor,optionCode (GeneralPaperEqualBitBoundaryScan.run model W lengths).1,
      (GeneralPaperEqualBitBoundaryScan.run model W lengths).2] (by
      intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals unfold parentCap; omega)
  change fields W _ ≤ 4 * (natBits (parentCap model W n P) + W) + 32 * W at hf
  dsimp only [window, profile]
  rw [GeneralPaperEqualRouteConstruction.indices_eq]
  omega

end Blotto.GeneralPaperEqualBitScanLifetime
