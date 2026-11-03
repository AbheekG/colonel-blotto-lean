import Blotto.GeneralPaperHeaderCountExpansionLifetime

/-! Complete count-directory recursion and parent scratch. Local expansion
mass sums to the expanded header-slot count; safe measured owners bound
that total once. Original/expanded directories, all expansion activations,
pending header frames, root scratch and parent prices can coexist. -/
namespace Blotto.GeneralPaperHeaderCountDirectoryLifetime
open GeneralPaperEncodedScalarStorage
open GeneralPaperReferenceRegionSlots
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperFieldDirectorySafety (Safe)
open GeneralPaperMeasuredBlockPlan (Plan)
open GeneralPaperHeaderTargetCopyLifetime (cap)
open GeneralPaperHeaderCountDirectory (headers prepare)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem mass_sum {A : ℕ} (values : List (Header A)) :
    GeneralPaperReferenceHeaderSlotArea.slots (values.map GeneralPaperHeaderCountExpansion.expanded) =
      (values.map (fun header => header.fixed + header.targets.length)).sum := by
  simp only [GeneralPaperReferenceHeaderSlotArea.slots,List.map_map,Function.comp_def,
    GeneralPaperStoredHeaderPreparationWork.expanded_length]

def controls (model : RationalCostModel) (S A : ℕ) (header : Header A) (rest : List (Header A)) : List ℕ :=
  let actual := GeneralPaperHeaderCountExpansion.run model S A header
  let later := headers model S A rest
  [S,A,actual.2,later.2,actual.2 + later.2,(headers model S A (header :: rest)).2]

def frameUnit (S A B Q : ℕ) : ℕ := 6 * (natBits (cap S A B Q) + S) + 160 * S + 64

def frames (model : RationalCostModel) (S A : ℕ) : List (Header A) → ℕ
  | [] => fields S [S,A,(headers model S A []).2] + 64 * S
  | header :: rest => GeneralPaperHeaderCountExpansionLifetime.window model S A header +
      fields S (controls model S A header rest) + 128 * S + frames model S A rest

theorem frames_bound (model : RationalCostModel) (S A B Q : ℕ) (values : List (Header A))
    (hA : 0 < A) (hValid : ∀ header ∈ values,Valid header)
    (hCap : ∀ header ∈ values,header.region.stop < 2 ^ A)
    (hMass : ∀ header ∈ values,header.fixed + header.targets.length ≤ B)
    (hWork : (headers model S A values).2 ≤ Q) :
    frames model S A values ≤
      ((values.map (fun header => header.fixed + header.targets.length)).sum + values.length) *
        GeneralPaperHeaderCountExpansionLifetime.unit model S A B Q + (values.length + 1) * frameUnit S A B Q := by
  induction values with
  | nil =>
    have hFields := fields_bound S (natBits (cap S A B Q)) [S,A,(headers model S A []).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (cap S A B Q) + S) + 32 * S at hFields
    simp only [frames,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.zero_mul,Nat.one_mul]
    unfold frameUnit
    omega
  | cons header rest ih =>
    have hWhole := hWork
    change (GeneralPaperHeaderCountExpansion.run model S A header).2 + (headers model S A rest).2 +
      64 * (S + A + 1) ≤ Q at hWork
    have hh : header ∈ header :: rest := List.mem_cons_self ..
    have hLocal := GeneralPaperHeaderCountExpansionLifetime.window_bound model S A B Q header hA
      (hValid header hh) (hCap header hh) (hMass header hh) (by omega)
    have hTail := ih (fun h hm => hValid h (List.mem_cons_of_mem _ hm))
      (fun h hm => hCap h (List.mem_cons_of_mem _ hm)) (fun h hm => hMass h (List.mem_cons_of_mem _ hm)) (by omega)
    have hFields := fields_bound S (natBits (cap S A B Q)) (controls model S A header rest) (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 6 * (natBits (cap S A B Q) + S) + 32 * S at hFields
    simp only [frames,List.map_cons,List.sum_cons,List.length_cons]
    unfold frameUnit at hTail ⊢
    nlinarith only [hLocal,hTail,hFields]

theorem reached_frames (model : RationalCostModel) (S A : ℕ) (values : List (Header A)) (depth : ℕ) :
    frames model S A (values.drop depth) ≤ frames model S A values := by
  induction values generalizing depth with
  | nil => simp only [List.drop_nil,le_refl]
  | cons header rest ih =>
    cases depth with
    | zero => simp only [List.drop_zero,le_refl]
    | succ depth =>
      have h := ih depth
      simp only [List.drop_succ_cons]
      have hStep : frames model S A rest ≤ frames model S A (header :: rest) := by
        change _ ≤ GeneralPaperHeaderCountExpansionLifetime.window model S A header +
          fields S (controls model S A header rest) + 128 * S + frames model S A rest
        omega
      exact h.trans hStep

theorem returned_shared_suffix (model : RationalCostModel) (S A : ℕ) (values : List (Header A)) (depth : ℕ) :
    (headers model S A (values.drop depth)).1 = (headers model S A values).1.drop depth := by
  induction values generalizing depth with
  | nil => simp only [GeneralPaperHeaderCountDirectory.headers_data,List.drop_nil,List.map_nil]
  | cons header rest ih =>
    cases depth with
    | zero => simp only [List.drop_zero]
    | succ depth =>
      simpa only [GeneralPaperHeaderCountDirectory.headers_data,List.map_cons,List.drop_succ_cons] using ih depth

def parentControls (model : RationalCostModel) (S A : ℕ) (directory : Directory A) : List ℕ :=
  [S,A,(headers model S A directory.headers).2,GeneralPaperLastRegionSelection.price S A directory.root,
    (prepare model S A directory).2]

def window (model : RationalCostModel) (S A : ℕ) (directory : Directory A) : ℕ :=
  GeneralPaperFieldDirectoryStorage.countWindow model S A directory + frames model S A directory.headers +
    GeneralPaperMeasuredLayoutStorage.regionFoot S directory.root + fields S (parentControls model S A directory) + 128 * S

def profile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  let Q := GeneralPaperStoredDirectoryPreparationWork.countBound model S A B
  GeneralPaperFieldDirectoryStorage.countBound model S A B +
    (2 * B) * GeneralPaperHeaderCountExpansionLifetime.unit model S A B Q + (B + 1) * frameUnit S A B Q +
    GeneralPaperMeasuredLayoutStorage.regionBound S A + 5 * (natBits (cap S A B Q) + S) + 160 * S

theorem window_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    window model S A directory ≤ profile model S A plan.sizes.sum := by
  let Q := GeneralPaperStoredDirectoryPreparationWork.countBound model S A plan.sizes.sum
  have hWork : (prepare model S A directory).2 ≤ Q :=
    GeneralPaperStoredDirectoryPreparationWork.count_work model S A start plan directory hSafe hPos hA hCap
  have hHeadersWork : (headers model S A directory.headers).2 ≤ Q := by
    have h := hWork
    change (headers model S A directory.headers).2 + GeneralPaperLastRegionSelection.price S A directory.root +
      64 * (S + A + 1) ≤ Q at h
    omega
  have hExpandedSafe := GeneralPaperHeaderCountDirectory.safe _ directory hSafe
  have hMassTotal := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start plan
    (GeneralPaperHeaderCountDirectory.expanded directory).headers hExpandedSafe.2.1 hA hExpandedSafe.2.2.2.1
  change GeneralPaperReferenceHeaderSlotArea.slots (directory.headers.map GeneralPaperHeaderCountExpansion.expanded) ≤ plan.sizes.sum at hMassTotal
  rw [mass_sum] at hMassTotal
  have hMass : ∀ header ∈ directory.headers,header.fixed + header.targets.length ≤ plan.sizes.sum := by
    intro header hh
    exact (List.single_le_sum (fun n _ => Nat.zero_le n) _ (List.mem_map.mpr ⟨header,hh,rfl⟩)).trans hMassTotal
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hSafe.2.1 hCap
  have hFrames := frames_bound model S A plan.sizes.sum Q directory.headers hA hSafe.2.2.2.1 hCaps hMass hHeadersWork
  have hCounts := GeneralPaperStoredDirectoryPreparationWork.directory_counts model S A start plan directory hSafe hPos
  have hExpandFactor := Nat.mul_le_mul_right (GeneralPaperHeaderCountExpansionLifetime.unit model S A plan.sizes.sum Q)
    (show (directory.headers.map (fun h => h.fixed + h.targets.length)).sum + directory.headers.length ≤ 2 * plan.sizes.sum by omega)
  have hFrameFactor := Nat.mul_le_mul_right (frameUnit S A plan.sizes.sum Q) (Nat.add_le_add_right hCounts.1 1)
  have hOwners := GeneralPaperFieldDirectoryStorage.count_window_bound model S A start plan directory hSafe hPos hA hCap
  have hRootRange := GeneralPaperMeasuredBlockLayout.range model S A start plan directory.root hSafe.1
  have hRoot := GeneralPaperMeasuredLayoutStorage.region_bound S A directory.root hA (hRootRange.2.trans_lt hCap)
  have hFields := fields_bound S (natBits (cap S A plan.sizes.sum Q)) (parentControls model S A directory) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [parentControls,List.mem_cons,List.not_mem_nil,or_false] at hx
    have h := hWork
    change (headers model S A directory.headers).2 + GeneralPaperLastRegionSelection.price S A directory.root +
      64 * (S + A + 1) ≤ Q at h
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 5 * (natBits (cap S A plan.sizes.sum Q) + S) + 32 * S at hFields
  dsimp only [window,profile,Q] at *
  omega

end Blotto.GeneralPaperHeaderCountDirectoryLifetime
