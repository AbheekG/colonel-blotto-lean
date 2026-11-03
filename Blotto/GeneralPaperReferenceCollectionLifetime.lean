import Blotto.GeneralPaperReferenceBatchLifetime

/-! Complete actual reference-entry collection and caller data. Every
entry owner includes its natural position. Batch outputs and left-only
append activations are charged by local target count; one final collected
list and the original header list coexist. Shared right/output suffixes
are not charged once per ancestor. -/
namespace Blotto.GeneralPaperReferenceCollectionLifetime
open GeneralPaperEncodedScalarStorage
open GeneralPaperReferenceSlotConstruction (Entry)
open GeneralPaperReferenceRegionSlots
open GeneralPaperReferenceRegionProgram (collect append)
open GeneralPaperReferenceBatchLifetime (wordLimit)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def appendFrames (S A : ℕ) (first rest : List (Entry A)) : ℕ :=
  GeneralPaperUnifiedInstallationLifetime.liftFrames S A (GeneralPaperReferenceSlotLifetime.entryFoot S)
    (fun xs => (append S A xs rest).2) first

def appendUnit (S A Q : ℕ) : ℕ :=
  3 * A + 64 * S + 1 + GeneralPaperUnifiedInstallationLifetime.liftFrameBound S A Q

theorem append_frames_bound (model : RationalCostModel) (S A Q : ℕ) (header : Header A) (rest : List (Entry A))
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A)
    (hWork : (append S A (batch model S A header).entries rest).2 ≤ Q) :
    appendFrames S A (batch model S A header).entries rest ≤ (header.targets.length + 1) * appendUnit S A Q := by
  have h := GeneralPaperUnifiedInstallationLifetime.lift_frames_bound S A Q (GeneralPaperReferenceSlotLifetime.entryFoot S)
    (fun xs => (append S A xs rest).2) (batch model S A header).entries
    (fun entry entries => by dsimp only [append]; omega) hWork
  have hSum := sum_bound (GeneralPaperReferenceSlotLifetime.entryFoot S) (3 * A + 64 * S + 1)
    (batch model S A header).entries (GeneralPaperReferenceSlotLifetime.header_entry_bound model S A header hA hValid hCap)
  have hCount : (batch model S A header).entries.length = header.targets.length :=
    GeneralPaperReferenceSlotBatch.count model S A header.region.start header.fixed 1 0 0 header.targets
  rw [hCount] at h hSum
  unfold appendFrames appendUnit
  nlinarith only [h,hSum,Nat.zero_le (3 * A + 64 * S + 1)]

theorem append_shared_suffix (S A : ℕ) (first rest : List (Entry A)) :
    (append S A first rest).1.drop first.length = rest := by
  rw [GeneralPaperReferenceRegionProgram.append_data]
  exact List.drop_left

def controls (model : RationalCostModel) (S A : ℕ) (header : Header A) (rest : List (Header A)) : List ℕ :=
  let actual := batch model S A header
  let later := collect model S A rest
  let joined := append S A actual.entries later.entries
  [S,A,actual.work,later.work,joined.2,actual.work + later.work,actual.work + later.work + joined.2,
    (collect model S A (header :: rest)).work]

def frameUnit (S A Q : ℕ) : ℕ := 8 * (wordLimit S A Q + S) + 160 * S + 64

def frames (model : RationalCostModel) (S A : ℕ) : List (Header A) → ℕ
  | [] => fields S [S,A,(collect model S A []).work] + 64 * S
  | header :: rest =>
    GeneralPaperReferenceBatchLifetime.window model S A header +
      appendFrames S A (batch model S A header).entries (collect model S A rest).entries +
      fields S (controls model S A header rest) + 128 * S + frames model S A rest

theorem frames_bound (model : RationalCostModel) (S A Q : ℕ) (values : List (Header A))
    (hA : 0 < A) (hValid : ∀ header ∈ values,Valid header)
    (hCap : ∀ header ∈ values,header.region.stop < 2 ^ A)
    (hWork : (collect model S A values).work ≤ Q) :
    frames model S A values ≤
      (GeneralPaperReferenceHeaderSlotArea.slots values + values.length) *
        (GeneralPaperReferenceBatchLifetime.unit model S A Q + appendUnit S A Q) +
      (values.length + 1) * frameUnit S A Q := by
  induction values with
  | nil =>
    have hAWord := GeneralPaperNaturalScalarLifetime.counter_word A
    have hFields := fields_bound S (wordLimit S A Q) [S,A,(collect model S A []).work] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      have hPrice := Nat.add_le_add_left (binaryWordWidth_mono hWork) 1
      change natBits (collect model S A []).work ≤ natBits Q at hPrice
      unfold wordLimit natBits at *
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (wordLimit S A Q + S) + 32 * S at hFields
    simp only [frames,GeneralPaperReferenceHeaderSlotArea.slots,List.map_nil,List.sum_nil,List.length_nil,
      Nat.zero_add,Nat.zero_mul,Nat.one_mul]
    unfold frameUnit
    omega
  | cons header rest ih =>
    have hWhole := hWork
    change (batch model S A header).work + (collect model S A rest).work +
      (append S A (batch model S A header).entries (collect model S A rest).entries).2 + 64 * (S + A + 1) ≤ Q at hWork
    have hh : header ∈ header :: rest := List.mem_cons_self ..
    have hBatch := GeneralPaperReferenceBatchLifetime.window_bound model S A Q header hA (hValid header hh) (hCap header hh) (by omega)
    have hAppend := append_frames_bound model S A Q header (collect model S A rest).entries hA
      (hValid header hh) (hCap header hh) (by omega)
    have hTail := ih (fun h hm => hValid h (List.mem_cons_of_mem _ hm)) (fun h hm => hCap h (List.mem_cons_of_mem _ hm)) (by omega)
    have hAWord := GeneralPaperNaturalScalarLifetime.counter_word A
    have hFields := fields_bound S (wordLimit S A Q) (controls model S A header rest) (by
      intro x hx
      simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|hx
      · unfold wordLimit; omega
      · unfold wordLimit; omega
      · have hp : x ≤ Q := by
          rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
        have hb := Nat.add_le_add_left (binaryWordWidth_mono hp) 1
        change natBits x ≤ natBits Q at hb
        unfold wordLimit
        omega)
    change fields S _ ≤ 8 * (wordLimit S A Q + S) + 32 * S at hFields
    simp only [frames,GeneralPaperReferenceHeaderSlotArea.slots,List.map_cons,List.sum_cons,List.length_cons] at hTail ⊢
    unfold frameUnit at hTail ⊢
    nlinarith only [hBatch,hAppend,hTail,hFields]

theorem reached_frames (model : RationalCostModel) (S A : ℕ) (values : List (Header A)) (depth : ℕ) :
    frames model S A (values.drop depth) ≤ frames model S A values := by
  induction values generalizing depth with
  | nil => simp only [List.drop_nil,le_refl]
  | cons header rest ih =>
    cases depth with
    | zero => simp only [List.drop_zero,le_refl]
    | succ depth =>
      have h := ih depth
      have hStep : frames model S A rest ≤ frames model S A (header :: rest) := by
        change _ ≤ GeneralPaperReferenceBatchLifetime.window model S A header +
          appendFrames S A (batch model S A header).entries (collect model S A rest).entries +
          fields S (controls model S A header rest) + 128 * S + frames model S A rest
        omega
      simpa only [List.drop_succ_cons] using h.trans hStep

theorem collected_entry_bound (model : RationalCostModel) (S A : ℕ) (values : List (Header A))
    (hA : 0 < A) (hValid : ∀ header ∈ values,Valid header)
    (hCap : ∀ header ∈ values,header.region.stop < 2 ^ A) :
    ∀ entry ∈ (collect model S A values).entries,GeneralPaperReferenceSlotLifetime.entryFoot S entry ≤ 3 * A + 64 * S + 1 := by
  intro entry he
  obtain ⟨header,hh,hEntry⟩ := (GeneralPaperReferenceRegionProgram.member model S A values entry).mp he
  exact GeneralPaperReferenceSlotLifetime.header_entry_bound model S A header hA (hValid header hh) (hCap header hh) entry hEntry

def window (model : RationalCostModel) (S A : ℕ) (values : List (Header A)) : ℕ :=
  listFootprint S (GeneralPaperFieldDirectoryStorage.headerFoot S) values +
    listFootprint S (GeneralPaperReferenceSlotLifetime.entryFoot S) (collect model S A values).entries +
    frames model S A values + fields S [S,A,(collect model S A values).work] + 64 * S

def unit (model : RationalCostModel) (S A Q : ℕ) : ℕ :=
  GeneralPaperReferenceBatchLifetime.unit model S A Q + appendUnit S A Q + frameUnit S A Q +
    (384 * (S + A + 1) + 34 * S) + (3 * A + 1 + 98 * S) + 3 * (wordLimit S A Q + S) + 96 * S

theorem window_bound (model : RationalCostModel) (S A Q : ℕ) (values : List (Header A))
    (hA : 0 < A) (hValid : ∀ header ∈ values,Valid header)
    (hCap : ∀ header ∈ values,header.region.stop < 2 ^ A)
    (hWork : (collect model S A values).work ≤ Q) :
    window model S A values ≤ (GeneralPaperReferenceHeaderSlotArea.slots values + values.length + 1) * unit model S A Q := by
  have hFrames := frames_bound model S A Q values hA hValid hCap hWork
  have hFramesFactor := Nat.mul_le_mul_right (GeneralPaperReferenceBatchLifetime.unit model S A Q + appendUnit S A Q)
    (show GeneralPaperReferenceHeaderSlotArea.slots values + values.length ≤ GeneralPaperReferenceHeaderSlotArea.slots values + values.length + 1 by omega)
  have hParentFactor := Nat.mul_le_mul_right (frameUnit S A Q)
    (show values.length + 1 ≤ GeneralPaperReferenceHeaderSlotArea.slots values + values.length + 1 by omega)
  have hHeader := GeneralPaperFieldDirectoryStorage.headers_bound S A values hA hValid hCap
  have hHeaderLinks := Nat.mul_le_mul_right (2 * S)
    (show values.length ≤ GeneralPaperReferenceHeaderSlotArea.slots values + values.length + 1 by omega)
  have hHeaderDescriptor := GeneralPaperHeaderCountExpansionLifetime.reserve (32 * S)
    (GeneralPaperReferenceHeaderSlotArea.slots values + values.length)
  have hEntries := list_bound S (3 * A + 64 * S + 1) (GeneralPaperReferenceSlotLifetime.entryFoot S) (collect model S A values).entries
    (collected_entry_bound model S A values hA hValid hCap)
  rw [GeneralPaperReferenceRegionProgram.count] at hEntries
  change listFootprint S _ _ ≤ GeneralPaperReferenceHeaderSlotArea.slots values * (3 * A + 64 * S + 1 + 2 * S) + 32 * S at hEntries
  have hEntryFactor := Nat.mul_le_mul_right (3 * A + 64 * S + 1 + 2 * S)
    (show GeneralPaperReferenceHeaderSlotArea.slots values ≤ GeneralPaperReferenceHeaderSlotArea.slots values + values.length + 1 by omega)
  have hAWord := GeneralPaperNaturalScalarLifetime.counter_word A
  have hFields := fields_bound S (wordLimit S A Q) [S,A,(collect model S A values).work] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    have hPrice := Nat.add_le_add_left (binaryWordWidth_mono hWork) 1
    change natBits (collect model S A values).work ≤ natBits Q at hPrice
    unfold wordLimit natBits at *
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (wordLimit S A Q + S) + 32 * S at hFields
  have hResultFactor := GeneralPaperHeaderCountExpansionLifetime.reserve (3 * (wordLimit S A Q + S) + 96 * S)
    (GeneralPaperReferenceHeaderSlotArea.slots values + values.length)
  have hHeaderFactor := Nat.mul_le_mul_right (384 * (S + A + 1))
    (show GeneralPaperReferenceHeaderSlotArea.slots values + values.length ≤ GeneralPaperReferenceHeaderSlotArea.slots values + values.length + 1 by omega)
  have hHeaderFull : listFootprint S (GeneralPaperFieldDirectoryStorage.headerFoot S) values ≤
      (GeneralPaperReferenceHeaderSlotArea.slots values + values.length + 1) * (384 * (S + A + 1) + 34 * S) := by
    unfold listFootprint
    nlinarith only [hHeader,hHeaderLinks,hHeaderDescriptor,hHeaderFactor]
  have hEntryFull : listFootprint S (GeneralPaperReferenceSlotLifetime.entryFoot S) (collect model S A values).entries ≤
      (GeneralPaperReferenceHeaderSlotArea.slots values + values.length + 1) * (3 * A + 1 + 98 * S) := by
    nlinarith only [hEntries,hEntryFactor,hHeaderDescriptor]
  unfold window unit
  nlinarith only [hFrames,hFramesFactor,hParentFactor,hHeaderFull,hEntryFull,hFields,hResultFactor]

end Blotto.GeneralPaperReferenceCollectionLifetime
