import Blotto.GeneralPaperReferenceRegionSlots

/-! Install every header into one raw reference memory. Entry batches and
list appends execute once and carry explicit prices. Disjoint actual owner
regions imply global key uniqueness, so each installed field can be read
through its actual root and local index after all other headers are written. -/
namespace Blotto.GeneralPaperReferenceRegionProgram
open GeneralPaperReferenceRegionSlots GeneralPaperReferenceSlotConstruction GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def append (S A : ℕ) : List (Entry A) → List (Entry A) → List (Entry A) × ℕ
  | [],ys => (ys,64 * (S + A + 1))
  | entry :: entries,ys =>
    let later := append S A entries ys
    (entry :: later.1,later.2 + GeneralPaperEncodedScalarStorage.natBits entry.position + 2 * A + 64 * (S + A + 1))

theorem append_data (S A : ℕ) (xs ys : List (Entry A)) : (append S A xs ys).1 = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [append,ih,List.cons_append]

theorem append_work (S A : ℕ) (xs ys : List (Entry A)) :
    (append S A xs ys).2 = (xs.map (fun e => GeneralPaperEncodedScalarStorage.natBits e.position)).sum +
      xs.length * (2 * A + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction xs with
  | nil => simp only [append,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons x xs ih => simp only [append,ih,List.map_cons,List.sum_cons,List.length_cons]; ring

structure Collected (A : ℕ) where
  entries : List (Entry A)
  work : ℕ

def collect (model : RationalCostModel) (S A : ℕ) : List (Header A) → Collected A
  | [] => ⟨[],64 * (S + A + 1)⟩
  | header :: headers =>
    let actual := batch model S A header
    let later := collect model S A headers
    let combined := append S A actual.entries later.entries
    ⟨combined.1,actual.work + later.work + combined.2 + 64 * (S + A + 1)⟩

theorem collect_cons (model : RationalCostModel) (S A : ℕ) (header : Header A) (headers : List (Header A)) :
    (collect model S A (header :: headers)).entries = (batch model S A header).entries ++ (collect model S A headers).entries := by
  simp only [collect,append_data]

theorem collect_data (model : RationalCostModel) (S A : ℕ) (headers : List (Header A)) :
    (collect model S A headers).entries = (headers.map (fun header => (batch model S A header).entries)).flatten := by
  induction headers with
  | nil => rfl
  | cons header headers ih => simp only [collect_cons,ih,List.map_cons,List.flatten_cons]

theorem member (model : RationalCostModel) (S A : ℕ) (headers : List (Header A)) (entry : Entry A) :
    entry ∈ (collect model S A headers).entries ↔ ∃ header ∈ headers,entry ∈ (batch model S A header).entries := by
  rw [collect_data]
  constructor
  · intro h
    obtain ⟨xs,hxs,he⟩ := List.mem_flatten.mp h
    obtain ⟨header,hh,rfl⟩ := List.mem_map.mp hxs
    exact ⟨header,hh,he⟩
  · rintro ⟨header,hh,he⟩
    exact List.mem_flatten.mpr ⟨_,List.mem_map.mpr ⟨header,hh,rfl⟩,he⟩

theorem count (model : RationalCostModel) (S A : ℕ) (headers : List (Header A)) :
    (collect model S A headers).entries.length = (headers.map (fun header => header.targets.length)).sum := by
  induction headers with
  | nil => rfl
  | cons header headers ih =>
    rw [collect_cons,List.length_append,ih]
    change (GeneralPaperReferenceSlotBatch.run model S A header.region.start header.fixed 1 0 0 header.targets).entries.length + _ = _
    rw [GeneralPaperReferenceSlotBatch.count]
    rfl

def DisjointOwners {A : ℕ} (headers : List (Header A)) : Prop :=
  headers.Pairwise (fun first second =>
    Disjoint (Set.Ico first.region.start first.region.stop) (Set.Ico second.region.start second.region.stop))

theorem keys_nodup (model : RationalCostModel) (S A : ℕ) (headers : List (Header A)) (hA : 0 < A)
    (hValid : ∀ header ∈ headers,Valid header) (hCap : ∀ header ∈ headers,header.region.stop < 2 ^ A)
    (hOwners : DisjointOwners headers) :
    ((collect model S A headers).entries.map (fun entry => entry.location.value)).Nodup := by
  induction headers with
  | nil => exact List.nodup_nil
  | cons first headers ih =>
    have hHead : first ∈ first :: headers := List.mem_cons_self ..
    have hTailValid := fun header hh => hValid header (List.mem_cons_of_mem first hh)
    have hTailCap := fun header hh => hCap header (List.mem_cons_of_mem first hh)
    have hPair := List.pairwise_cons.mp hOwners
    rw [collect_cons,List.map_append,List.nodup_append]
    refine ⟨GeneralPaperReferenceRegionSlots.keys_nodup model S A first hA (hValid first hHead) (hCap first hHead),
      ih hTailValid hTailCap hPair.2,?_⟩
    intro x hx y hy hEq
    obtain ⟨entry,he,hKey⟩ := List.mem_map.mp hy
    obtain ⟨header,hh,hEntry⟩ := (member model S A headers entry).mp he
    have hDis := GeneralPaperReferenceRegionSlots.disjoint_keys model S A first header hA
      (hValid first hHead) (hTailValid header hh) (hCap first hHead) (hTailCap header hh) (hPair.1 header hh)
    apply List.disjoint_left.mp hDis hx
    rw [hEq]
    exact List.mem_map.mpr ⟨entry,hEntry,hKey⟩

structure Prepared (A : ℕ) where
  memory : GeneralPaperRawReferenceMemory.Memory A
  work : ℕ

def prepare (model : RationalCostModel) (S A : ℕ) (headers : List (Header A))
    (memory : GeneralPaperRawReferenceMemory.Memory A) : Prepared A :=
  let actual := collect model S A headers
  let installed := GeneralPaperRawReferenceMemory.install A memory actual.entries
  ⟨installed.1,actual.work + installed.2 + 64 * (S + A + 1)⟩

def read (model : RationalCostModel) (A : ℕ) (memory : GeneralPaperRawReferenceMemory.Memory A)
    (root : FixedBinaryWord A) (fixed index : ℕ) : Option (FixedBinaryWord A) × ℕ :=
  GeneralPaperReferenceHeaderProgram.read model A memory root.value fixed 1 index 0

theorem prepare_work (model : RationalCostModel) (S A : ℕ) (headers : List (Header A))
    (memory : GeneralPaperRawReferenceMemory.Memory A) :
    (prepare model S A headers memory).work = (collect model S A headers).work +
      (headers.map (fun header => header.targets.length)).sum * (128 * A + 128) + 64 * A + 64 + 64 * (S + A + 1) := by
  dsimp only [prepare]
  rw [GeneralPaperRawReferenceMemory.install_work,count]
  ring

theorem read_prepared (model : RationalCostModel) (S A : ℕ) (headers : List (Header A))
    (memory : GeneralPaperRawReferenceMemory.Memory A) (hA : 0 < A)
    (hValid : ∀ header ∈ headers,Valid header) (hCap : ∀ header ∈ headers,header.region.stop < 2 ^ A)
    (hRoots : ∀ header ∈ headers,header.region.reference.value = header.region.start)
    (hOwners : DisjointOwners headers) (header : Header A) (hHeader : header ∈ headers) (j : Fin header.targets.length) :
    (read model A (prepare model S A headers memory).memory header.region.reference header.fixed j.val).1 =
      some header.targets[j.val] := by
  let entries := (batch model S A header).entries
  have hIndex : j.val < entries.length := by
    dsimp only [entries,batch]
    rw [GeneralPaperReferenceSlotBatch.count]
    exact j.isLt
  let entry := entries[j.val]
  have hSome : entries[j.val]? = some entry := List.getElem?_eq_getElem hIndex
  have hMem : entry ∈ entries := List.getElem_mem hIndex
  have hLocation := GeneralPaperReferenceSlotBatch.lookup_location model S A header.region.start header.fixed 1 0 0
    header.targets j.val j.isLt
  change (entries[j.val]?).map Entry.location = _ at hLocation
  rw [hSome] at hLocation
  simp only [Option.map_some,Option.some.injEq,Nat.zero_add] at hLocation
  have hTarget := GeneralPaperReferenceSlotBatch.lookup_target model S A header.region.start header.fixed 1 0 0 header.targets j.val
  change (entries[j.val]?).map Entry.target = header.targets[j.val]? at hTarget
  rw [hSome,List.getElem?_eq_getElem j.isLt] at hTarget
  simp only [Option.map_some,Option.some.injEq] at hTarget
  have hInstalled := GeneralPaperRawReferenceMemory.installed A memory (collect model S A headers).entries
    (keys_nodup model S A headers hA hValid hCap hOwners) entry
    ((member model S A headers entry).mpr ⟨header,hHeader,hMem⟩)
  unfold read
  rw [GeneralPaperReferenceHeaderProgram.read_data,hRoots header hHeader,← hLocation]
  exact hInstalled.trans (congrArg some hTarget)

end Blotto.GeneralPaperReferenceRegionProgram
