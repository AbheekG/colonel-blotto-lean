import Blotto.GeneralPaperMixedReferenceMemory

/-! Computed local-width field reads into the common mixed-width RAM.
Header batches are generated once and installed together. The reader accepts
only memory, the raw root and an index; correctness follows from actual
installation, rather than a decoded reference passed into the reader. -/
namespace Blotto.GeneralPaperMixedReferenceRegionProgram
open GeneralPaperReferenceRegionSlots GeneralPaperReferenceRegionProgram GeneralPaperReferenceSlotConstruction
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Prepared where
  memory : GeneralPaperPayloadMemory.Memory Word
  work : ℕ

def prepare (model : RationalCostModel) (S A B : ℕ) (inside : List (Header A)) (outside : List (Header B))
    (memory : GeneralPaperPayloadMemory.Memory Word) : Prepared :=
  let first := collect model S A inside
  let second := collect model S B outside
  let actual := GeneralPaperMixedReferenceMemory.prepare S A B first.entries second.entries memory
  ⟨actual.memory,first.work + second.work + actual.work + 64 * (S + A + B + 1)⟩

def read (model : RationalCostModel) (A : ℕ) (memory : GeneralPaperPayloadMemory.Memory Word)
    (root : FixedBinaryWord A) (fixed index : ℕ) : Option Word × ℕ :=
  let zero := GeneralPaperStoredWordEncoding.word model A A 0
  let location := GeneralPaperReferenceSlotConstruction.run model A A root.value fixed 1 index 0 zero.1
  let actual := GeneralPaperPayloadMemory.read A GeneralPaperMixedReferenceMemory.encode memory location.1.location
  (actual.1,zero.2 + location.2 + actual.2 + 64 * A + 64)

theorem read_data (model : RationalCostModel) (A : ℕ) (memory : GeneralPaperPayloadMemory.Memory Word)
    (root : FixedBinaryWord A) (fixed index : ℕ) :
    (read model A memory root fixed index).1 =
      memory (FixedBinaryWord.ofNat A (root.value + A * (fixed + 1 * index + 0))).value := by
  simp only [read,GeneralPaperReferenceSlotConstruction.location,GeneralPaperPayloadMemory.read]

theorem read_header (model : RationalCostModel) (S A : ℕ) (memory : GeneralPaperPayloadMemory.Memory Word)
    (header : Header A) (hRoot : header.region.reference.value = header.region.start)
    (hInstalled : ∀ entry ∈ (batch model S A header).entries,
      memory entry.location.value = some (⟨A,entry.target⟩ : Word)) (j : Fin header.targets.length) :
    (read model A memory header.region.reference header.fixed j.val).1 = some (⟨A,header.targets[j.val]⟩ : Word) := by
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
  rw [read_data,hRoot,← hLocation,hInstalled entry hMem,hTarget]

theorem read_work_of_some (model : RationalCostModel) (A : ℕ) (memory : GeneralPaperPayloadMemory.Memory Word)
    (root : FixedBinaryWord A) (fixed index : ℕ) (target : FixedBinaryWord A)
    (hRead : (read model A memory root fixed index).1 = some (⟨A,target⟩ : Word)) :
    (read model A memory root fixed index).2 =
      (GeneralPaperStoredWordEncoding.word model A A 0).2 +
      (GeneralPaperReferenceSlotConstruction.run model A A root.value fixed 1 index 0
        (GeneralPaperStoredWordEncoding.word model A A 0).1).2 + 129 * A + 128 := by
  have hMemory := hRead
  rw [read_data] at hMemory
  dsimp only [read,GeneralPaperPayloadMemory.read]
  rw [GeneralPaperReferenceSlotConstruction.location,hMemory]
  simp only [Option.elim_some,GeneralPaperMixedReferenceMemory.encode]
  ring

theorem inside_read (model : RationalCostModel) (S A B : ℕ) (inside : List (Header A)) (outside : List (Header B))
    (memory : GeneralPaperPayloadMemory.Memory Word) (hA : 0 < A)
    (hValid : ∀ header ∈ inside,Valid header) (hCap : ∀ header ∈ inside,header.region.stop < 2 ^ A)
    (hRoots : ∀ header ∈ inside,header.region.reference.value = header.region.start)
    (hOwners : DisjointOwners inside)
    (hDisjoint : List.Disjoint ((collect model S A inside).entries.map (fun entry => entry.location.value))
      ((collect model S B outside).entries.map (fun entry => entry.location.value)))
    (header : Header A) (hHeader : header ∈ inside) (j : Fin header.targets.length) :
    (read model A (prepare model S A B inside outside memory).memory header.region.reference header.fixed j.val).1 =
      some (⟨A,header.targets[j.val]⟩ : Word) := by
  apply read_header model S A _ header (hRoots header hHeader) _ j
  intro entry hEntry
  exact GeneralPaperMixedReferenceMemory.inside_read S A B (collect model S A inside).entries (collect model S B outside).entries
    memory (keys_nodup model S A inside hA hValid hCap hOwners) hDisjoint entry
    ((member model S A inside entry).mpr ⟨header,hHeader,hEntry⟩)

theorem outside_read (model : RationalCostModel) (S A B : ℕ) (inside : List (Header A)) (outside : List (Header B))
    (memory : GeneralPaperPayloadMemory.Memory Word) (hB : 0 < B)
    (hValid : ∀ header ∈ outside,Valid header) (hCap : ∀ header ∈ outside,header.region.stop < 2 ^ B)
    (hRoots : ∀ header ∈ outside,header.region.reference.value = header.region.start)
    (hOwners : DisjointOwners outside)
    (header : Header B) (hHeader : header ∈ outside) (j : Fin header.targets.length) :
    (read model B (prepare model S A B inside outside memory).memory header.region.reference header.fixed j.val).1 =
      some (⟨B,header.targets[j.val]⟩ : Word) := by
  apply read_header model S B _ header (hRoots header hHeader) _ j
  intro entry hEntry
  exact GeneralPaperMixedReferenceMemory.outside_read S A B (collect model S A inside).entries (collect model S B outside).entries
    memory (keys_nodup model S B outside hB hValid hCap hOwners) entry
    ((member model S B outside entry).mpr ⟨header,hHeader,hEntry⟩)

theorem prepare_work (model : RationalCostModel) (S A B : ℕ) (inside : List (Header A)) (outside : List (Header B))
    (memory : GeneralPaperPayloadMemory.Memory Word) :
    (prepare model S A B inside outside memory).work =
      (collect model S A inside).work + (collect model S B outside).work +
      (inside.map (fun header => header.targets.length)).sum * (67 * A + 64 + 128 * (S + A + 1)) +
      (outside.map (fun header => header.targets.length)).sum * (67 * B + 64 + 128 * (S + B + 1)) +
      128 * (S + A + 1) + 128 * (S + B + 1) + 128 * (S + A + B + 1) := by
  dsimp only [prepare]
  rw [GeneralPaperMixedReferenceMemory.prepare_work,count,count]
  ring

end Blotto.GeneralPaperMixedReferenceRegionProgram
