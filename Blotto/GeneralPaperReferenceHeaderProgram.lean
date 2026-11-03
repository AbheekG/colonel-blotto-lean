import Blotto.GeneralPaperReferenceSlotBatch

/-! Executed header construction/install and a reader that computes its
location from the index. Reads use the local stored width, not the original
preparation word. The source target is recovered from raw memory, not passed
to the reader as a decoded-value or address oracle. -/
namespace Blotto.GeneralPaperReferenceHeaderProgram
open GeneralPaperReferenceSlotConstruction (Entry)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Prepared (A : ℕ) where
  memory : GeneralPaperRawReferenceMemory.Memory A
  entries : List (Entry A)
  work : ℕ

def prepare (model : RationalCostModel) (S A base fixed stride cell : ℕ) (values : List (FixedBinaryWord A))
    (memory : GeneralPaperRawReferenceMemory.Memory A) : Prepared A :=
  let program := GeneralPaperReferenceSlotBatch.run model S A base fixed stride cell 0 values
  let installed := GeneralPaperRawReferenceMemory.install A memory program.entries
  ⟨installed.1,program.entries,program.work + installed.2 + 64 * (S + A + 1)⟩

def read (model : RationalCostModel) (A : ℕ) (memory : GeneralPaperRawReferenceMemory.Memory A)
    (base fixed stride index cell : ℕ) : Option (FixedBinaryWord A) × ℕ :=
  let zero := GeneralPaperStoredWordEncoding.word model A A 0
  let location := GeneralPaperReferenceSlotConstruction.run model A A base fixed stride index cell zero.1
  let loaded := GeneralPaperRawReferenceMemory.read A memory location.1.location
  (loaded.1,zero.2 + location.2 + loaded.2 + 64 * A + 64)

theorem read_data (model : RationalCostModel) (A : ℕ) (memory : GeneralPaperRawReferenceMemory.Memory A)
    (base fixed stride index cell : ℕ) :
    (read model A memory base fixed stride index cell).1 =
      memory (FixedBinaryWord.ofNat A (base + A * (fixed + stride * index + cell))).value := by
  simp only [read,GeneralPaperReferenceSlotConstruction.location,GeneralPaperRawReferenceMemory.read]

theorem prepare_work (model : RationalCostModel) (S A base fixed stride cell : ℕ) (values : List (FixedBinaryWord A))
    (memory : GeneralPaperRawReferenceMemory.Memory A) :
    (prepare model S A base fixed stride cell values memory).work =
      (GeneralPaperReferenceSlotBatch.run model S A base fixed stride cell 0 values).work +
      values.length * (128 * A + 128) + 64 * A + 64 + 64 * (S + A + 1) := by
  dsimp only [prepare]
  rw [GeneralPaperRawReferenceMemory.install_work,GeneralPaperReferenceSlotBatch.count]
  ring

theorem read_prepared (model : RationalCostModel) (S A base fixed stride cell : ℕ) (values : List (FixedBinaryWord A))
    (memory : GeneralPaperRawReferenceMemory.Memory A) (hA : 0 < A) (hCell : cell < stride)
    (hCap : base + A * (fixed + stride * values.length) < 2 ^ A) (j : Fin values.length) :
    (read model A (prepare model S A base fixed stride cell values memory).memory base fixed stride j.val cell).1 =
      some values[j.val] := by
  let entries := (GeneralPaperReferenceSlotBatch.run model S A base fixed stride cell 0 values).entries
  have hIndex : j.val < entries.length := by
    dsimp only [entries]
    rw [GeneralPaperReferenceSlotBatch.count]
    exact j.isLt
  let entry := entries[j.val]
  have hSome : entries[j.val]? = some entry := List.getElem?_eq_getElem hIndex
  have hMem : entry ∈ entries := List.getElem_mem hIndex
  have hLocation := GeneralPaperReferenceSlotBatch.lookup_location model S A base fixed stride cell 0 values j.val j.isLt
  change (entries[j.val]?).map Entry.location = _ at hLocation
  rw [hSome] at hLocation
  simp only [Option.map_some,Option.some.injEq,Nat.zero_add] at hLocation
  have hTarget := GeneralPaperReferenceSlotBatch.lookup_target model S A base fixed stride cell 0 values j.val
  change (entries[j.val]?).map Entry.target = values[j.val]? at hTarget
  rw [hSome,List.getElem?_eq_getElem j.isLt] at hTarget
  simp only [Option.map_some,Option.some.injEq] at hTarget
  have hInstalled := GeneralPaperReferenceSlotBatch.installed model S A base fixed stride cell 0 values.length values memory
    hA (by omega) hCell hCap entry hMem
  rw [read_data,← hLocation]
  exact hInstalled.trans (congrArg some hTarget)

end Blotto.GeneralPaperReferenceHeaderProgram
