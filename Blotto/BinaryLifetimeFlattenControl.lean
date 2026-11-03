import Blotto.NativeArrayConversionControl

/-! Source control for the former `List.flattenTR` entry-array trace path.
The array observer traverses each child trace with `Array.appendList`, then
converts the accumulated array to a list. The selected `fromEntries` path
now uses `BinaryLifetimeFlattenList.flattenDirect`; its exact result agrees
with this retained reference, but its actual allocation uses lists. -/
namespace Blotto.BinaryLifetimeFlattenControl
open BinarySeedPreparationSpace NativeArrayConversionCore

def payloadCount {α : Type*} (lists : List (List α)) : ℕ :=
  (lists.map List.length).sum

def appendWithCount {α : Type*} : List α → Array α → Array α × ℕ
  | [], acc => (acc,0)
  | item :: rest, acc =>
      let later := appendWithCount rest (acc.push item)
      (later.1,later.2+1)

theorem appendWithCount_state {α : Type*} (items : List α) (acc : Array α) :
    (appendWithCount items acc).1 = acc.appendList items := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih =>
      simpa only [appendWithCount,Array.appendList,List.foldl_cons] using ih (acc.push item)

theorem appendWithCount_count {α : Type*} (items : List α) (acc : Array α) :
    (appendWithCount items acc).2 = items.length := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => simp only [appendWithCount,List.length_cons,ih]

def flattenWithCount {α : Type*} : List (List α) → Array α → Array α × ℕ
  | [], acc => (acc,0)
  | child :: rest, acc =>
      let appended := appendWithCount child acc
      let later := flattenWithCount rest appended.1
      (later.1,appended.2+later.2)

theorem flattenWithCount_result {α : Type*} (lists : List (List α)) (acc : Array α) :
    (flattenWithCount lists acc).1.toList = acc.toList ++ lists.flatten := by
  induction lists generalizing acc with
  | nil => simp [flattenWithCount]
  | cons child rest ih =>
      simp only [flattenWithCount,List.flatten_cons,ih,appendWithCount_state]
      change (acc ++ child).toList ++ rest.flatten = acc.toList ++ (child ++ rest.flatten)
      rw [Array.toList_appendList]
      simp only [List.append_assoc]

theorem flattenWithCount_count {α : Type*} (lists : List (List α)) (acc : Array α) :
    (flattenWithCount lists acc).2 = payloadCount lists := by
  induction lists generalizing acc with
  | nil => rfl
  | cons child rest ih =>
      simp only [flattenWithCount,appendWithCount_count,ih,payloadCount,List.map_cons,List.sum_cons]

theorem selected_flatten_count {α : Type*} (lists : List (List α)) :
    (flattenWithCount lists #[]).1.toList = List.flattenTR lists ∧
    (flattenWithCount lists #[]).2 = (List.flattenTR lists).length := by
  have hResult := flattenWithCount_result lists (#[] : Array α)
  have hCount := flattenWithCount_count lists (#[] : Array α)
  constructor
  · simpa only [Array.toList_empty,List.nil_append,← List.flatten_eq_flattenTR] using hResult
  · simpa only [payloadCount,← List.flatten_eq_flattenTR,List.length_flatten] using hCount

theorem selected_flatten_read_count {α : Type*} (lists : List (List α)) :
    ((read (flattenWithCount lists #[]).1).2.filterMap ReadSnapshot.readIndex).length =
      (flattenWithCount lists #[]).2 := by
  have h := selected_flatten_count lists
  have hSize : (flattenWithCount lists #[]).1.size = (List.flattenTR lists).length := by
    rw [← Array.length_toList,h.1]
  rw [NativeArrayConversionControl.read_count,hSize,h.2]

theorem selected_flatten_push_data {α : Type*} (lists : List (List α)) :
    (flattenWithCount lists #[]).1 = (pushLoop lists.flatten #[]).1 := by
  apply Array.toList_inj.mp
  rw [flattenWithCount_result,pushLoop_state]
  simp [Array.toArrayAux_eq]

theorem selected_flatten_push_control {α : Type*} (lists : List (List α)) :
    let T := payloadCount lists
    (pushLoop lists.flatten #[]).2.filterMap NativeArrayConversionControl.PushSnapshot.pushIndex =
      List.range T ∧
    NativeArrayConversionControl.prefixSlots (pushLoop lists.flatten #[]).2 ≤ (T+1)^2 := by
  dsimp only
  have hLength : lists.flatten.length = payloadCount lists := by
    simp [payloadCount]
  constructor
  · simp only [NativeArrayConversionControl.pushLoop_indices,hLength,
      show (#[] : Array α).size = 0 from rfl,List.range_eq_range']
  · have hValid := pushLoop_valid lists.flatten (#[] : Array α) (payloadCount lists)
      (by simp [hLength])
    have h := NativeArrayConversionControl.prefixSlots_bound (payloadCount lists)
      (pushLoop lists.flatten (#[] : Array α)).2 hValid
    rw [pushLoop_length] at h
    rw [hLength] at h
    nlinarith

theorem selected_flatten_scalar_width {α : Type*} (lists : List (List α)) :
    let T := payloadCount lists
    (∀ s ∈ (pushLoop lists.flatten #[]).2,
      ∀ value ∈ s.operands T,binaryWordWidth value ≤ binaryWordWidth (T+1)) ∧
    (∀ s ∈ (read (flattenWithCount lists #[]).1).2,
      ∀ value ∈ s.operands (flattenWithCount lists #[]).1.size,
        binaryWordWidth value ≤ binaryWordWidth (T+1)) := by
  dsimp only
  have hLength : lists.flatten.length = payloadCount lists := by simp [payloadCount]
  have hValid := pushLoop_valid lists.flatten (#[] : Array α) (payloadCount lists)
    (by simp [hLength])
  have hSize : (flattenWithCount lists #[]).1.size = payloadCount lists := by
    rw [← Array.length_toList,(selected_flatten_count lists).1]
    simp [payloadCount,← List.flatten_eq_flattenTR]
  constructor
  · intro s hs value hv
    exact binaryWordWidth_mono ((PushSnapshot.operand_bound (hValid s hs)) value hv)
  · intro s hs value hv
    have h := NativeArrayConversionControl.read_scalar_width
      (flattenWithCount lists #[]).1 s hs value hv
    rw [hSize] at h
    exact h

theorem selected_flatten_visits {α : Type*} (lists : List (List α)) :
    (flattenWithCount lists #[]).2 +
      ((read (flattenWithCount lists #[]).1).2.filterMap ReadSnapshot.readIndex).length +
      lists.length = 2*payloadCount lists+lists.length := by
  rw [selected_flatten_read_count,flattenWithCount_count]
  omega

theorem fromEntries_flatten_count {α : Type*} (n : ℕ)
    (entries : List (α × Trace)) (hEntries : entries.length = n) :
    (BinaryLifetimeArray.fromEntries n entries hEntries).2 =
      [.frames (n+4),.arrayAllocation (2*(n+1)^2+8)] ++
        under 2 (flattenWithCount (BinaryLifetimeArray.mapDirect Prod.snd entries) #[]).1.toList ∧
    (flattenWithCount (BinaryLifetimeArray.mapDirect Prod.snd entries) #[]).2 =
      (List.flattenTR (BinaryLifetimeArray.mapDirect Prod.snd entries)).length := by
  have h := selected_flatten_count (BinaryLifetimeArray.mapDirect Prod.snd entries)
  exact ⟨by simp only [BinaryLifetimeArray.fromEntries,
    BinaryLifetimeFlattenList.flattenDirect_eq_flattenTR,h.1],h.2⟩

theorem fromEntries_direct_cons_count {α : Type*} (n : ℕ)
    (entries : List (α × Trace)) (hEntries : entries.length = n) :
    let lists := BinaryLifetimeArray.mapDirect Prod.snd entries
    (BinaryLifetimeArray.fromEntries n entries hEntries).2 =
      [.frames (n+4),.arrayAllocation (2*(n+1)^2+8)] ++
        under 2 (BinaryLifetimeFlattenList.gatherWithCount lists []).1 ∧
    (BinaryLifetimeFlattenList.gatherWithCount lists []).2 =
      2*payloadCount lists := by
  dsimp only
  have h := BinaryLifetimeFlattenList.flattenDirect_cons_count
    (BinaryLifetimeArray.mapDirect Prod.snd entries)
  constructor
  · simp only [BinaryLifetimeArray.fromEntries,h.1]
  · simpa only [payloadCount,BinaryLifetimeFlattenList.payloadCount] using h.2

theorem fromEntries_flatten_visits {α : Type*} (n : ℕ)
    (entries : List (α × Trace)) (hEntries : entries.length = n) :
    let lists := BinaryLifetimeArray.mapDirect Prod.snd entries
    (flattenWithCount lists #[]).2 +
      ((read (flattenWithCount lists #[]).1).2.filterMap ReadSnapshot.readIndex).length + n =
      2*payloadCount lists+n := by
  dsimp only
  have h := selected_flatten_visits (BinaryLifetimeArray.mapDirect Prod.snd entries)
  rw [BinaryLifetimeArray.mapDirect_length,hEntries] at h
  exact h

end Blotto.BinaryLifetimeFlattenControl
