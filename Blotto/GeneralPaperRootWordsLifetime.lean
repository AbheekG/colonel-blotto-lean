import Blotto.GeneralPaperDirectoryCopyLifetimeRates

/-! Complete actual root-word construction. Full pending root records,
word-copy scratch, saved partial/control prices and one returned word list
coexist with the root source. No root suffix is counted per ancestor. -/
namespace Blotto.GeneralPaperRootWordsLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperNestedArrayFieldCursor (rootWords)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def frames (S A : ℕ) : List (Region A) → ℕ
  | [] => fields S [S,A,(rootWords S A []).2] + 64 * S
  | root :: roots => GeneralPaperMeasuredLayoutStorage.regionFoot S root + A +
    fields S [S,A,(rootWords S A roots).2,(rootWords S A roots).2 + A,(rootWords S A (root :: roots)).2] +
    128 * S + frames S A roots

theorem frames_bound (model : RationalCostModel) (S A Q : ℕ) (roots : List (Region A)) (hA : 0 < A)
    (hCap : ∀ root ∈ roots,root.stop < 2 ^ A) (hWork : (rootWords S A roots).2 ≤ Q) :
    frames S A roots ≤ (roots.length + 1) * unit model S A Q := by
  induction roots with
  | nil =>
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(rootWords S A []).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    simp only [frames,List.length_nil,Nat.zero_add,Nat.one_mul]
    omega
  | cons root roots ih =>
    have hWhole := hWork
    change (rootWords S A roots).2 + A + 64 * (S + A + 1) ≤ Q at hWork
    have hRegion := GeneralPaperMeasuredLayoutStorage.region_bound S A root hA (hCap root (List.mem_cons_self ..))
    have ht := ih (fun r hr => hCap r (List.mem_cons_of_mem _ hr)) (by omega)
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(rootWords S A roots).2,
      (rootWords S A roots).2 + A,(rootWords S A (root :: roots)).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 5 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    have hLocal : GeneralPaperMeasuredLayoutStorage.regionFoot S root + A + fields S [S,A,(rootWords S A roots).2,
        (rootWords S A roots).2 + A,(rootWords S A (root :: roots)).2] + 128 * S ≤ unit model S A Q := by
      unfold GeneralPaperMeasuredLayoutStorage.regionBound at hRegion
      omega
    simp only [frames,List.length_cons]
    nlinarith only [ht,hLocal]

def window (S A : ℕ) (roots : List (Region A)) : ℕ :=
  GeneralPaperMeasuredLayoutStorage.regionsFoot S roots + frames S A roots +
    listFootprint S (fun _ : FixedBinaryWord A => A) (rootWords S A roots).1 +
    fields S [S,A,(rootWords S A roots).2] + 64 * S

theorem window_bound (model : RationalCostModel) (S A Q : ℕ) (roots : List (Region A)) (hA : 0 < A)
    (hCap : ∀ root ∈ roots,root.stop < 2 ^ A) (hWork : (rootWords S A roots).2 ≤ Q) :
    window S A roots ≤ (roots.length + 1) * 4 * unit model S A Q := by
  have hFrames := frames_bound model S A Q roots hA hCap hWork
  have hRoots := list_bound S (GeneralPaperMeasuredLayoutStorage.regionBound S A)
    (GeneralPaperMeasuredLayoutStorage.regionFoot S) roots (fun root hr => GeneralPaperMeasuredLayoutStorage.region_bound S A root hA (hCap root hr))
  have hWords := list_bound S A (fun _ : FixedBinaryWord A => A) (rootWords S A roots).1 (fun _ _ => le_rfl)
  rw [GeneralPaperNestedArrayFieldCursor.root_words_data,List.length_map] at hWords
  have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(rootWords S A roots).2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hStep := Nat.mul_le_mul_left roots.length
    (show GeneralPaperMeasuredLayoutStorage.regionBound S A + A + 4 * S ≤ unit model S A Q by
      unfold GeneralPaperMeasuredLayoutStorage.regionBound
      omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ roots.length + 1 by omega)
  unfold window GeneralPaperMeasuredLayoutStorage.regionsFoot
  rw [GeneralPaperNestedArrayFieldCursor.root_words_data]
  nlinarith only [hFrames,hRoots,hWords,hFields,hStep,hBase,hUnit]

end Blotto.GeneralPaperRootWordsLifetime
