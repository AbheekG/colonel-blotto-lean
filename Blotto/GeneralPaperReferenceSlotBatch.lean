import Blotto.GeneralPaperRawReferenceMemory

/-! Sequential construction and installation of a header's raw-reference
entries. The index is advanced once per target with priced arithmetic;
there is no repeated indexed lookup through a linked list. -/
namespace Blotto.GeneralPaperReferenceSlotBatch
open GeneralPaperReferenceSlotConstruction (Entry)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Result (A : ℕ) where
  entries : List (Entry A)
  next : ℕ
  work : ℕ

def run (model : RationalCostModel) (S A base fixed stride cell : ℕ) : ℕ → List (FixedBinaryWord A) → Result A
  | start,[] => ⟨[],start,64 * (S + A + 1)⟩
  | start,target :: targets =>
    let entry := GeneralPaperReferenceSlotConstruction.run model S A base fixed stride start cell target
    let next := GeneralPaperNaturalScalarStep.run model S .add start 1
    let later := run model S A base fixed stride cell next.1 targets
    ⟨entry.1 :: later.entries,later.next,entry.2 + next.2 + later.work + 128 * (S + A + 1)⟩

theorem next (model : RationalCostModel) (S A base fixed stride cell start : ℕ) (targets : List (FixedBinaryWord A)) :
    (run model S A base fixed stride cell start targets).next = start + targets.length := by
  induction targets generalizing start with
  | nil => simp only [run,List.length_nil,Nat.add_zero]
  | cons target targets ih =>
    simp only [run,GeneralPaperNaturalScalarStep.run,GeneralPaperNaturalScalarStep.Op.apply,ih,List.length_cons]
    omega

theorem targets (model : RationalCostModel) (S A base fixed stride cell start : ℕ) (values : List (FixedBinaryWord A)) :
    (run model S A base fixed stride cell start values).entries.map Entry.target = values := by
  induction values generalizing start with
  | nil => rfl
  | cons value values ih => simp only [run,List.map_cons,GeneralPaperReferenceSlotConstruction.target,ih]

theorem count (model : RationalCostModel) (S A base fixed stride cell start : ℕ) (values : List (FixedBinaryWord A)) :
    (run model S A base fixed stride cell start values).entries.length = values.length := by
  have h := congrArg List.length (targets model S A base fixed stride cell start values)
  simpa only [List.length_map] using h

theorem member_index (model : RationalCostModel) (S A base fixed stride cell start : ℕ)
    (values : List (FixedBinaryWord A)) :
    ∀ e ∈ (run model S A base fixed stride cell start values).entries,
      ∃ i value,start ≤ i ∧ i < start + values.length ∧
        e = (GeneralPaperReferenceSlotConstruction.run model S A base fixed stride i cell value).1 := by
  induction values generalizing start with
  | nil => intro e he; cases he
  | cons value values ih =>
    intro e he
    change e ∈ (GeneralPaperReferenceSlotConstruction.run model S A base fixed stride start cell value).1 ::
      (run model S A base fixed stride cell (start + 1) values).entries at he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · refine ⟨start,value,le_rfl,?_,rfl⟩
      simp only [List.length_cons]
      omega
    · obtain ⟨i,target,hl,hu,hEq⟩ := ih (start + 1) e he
      refine ⟨i,target,by omega,?_,hEq⟩
      simp only [List.length_cons]
      omega

theorem positions_nodup (model : RationalCostModel) (S A base fixed stride cell start : ℕ)
    (values : List (FixedBinaryWord A)) (hA : 0 < A) (hStride : 0 < stride) :
    ((run model S A base fixed stride cell start values).entries.map Entry.position).Nodup := by
  induction values generalizing start with
  | nil => exact List.nodup_nil
  | cons value values ih =>
    change ((GeneralPaperReferenceSlotConstruction.run model S A base fixed stride start cell value).1.position ::
      (run model S A base fixed stride cell (start + 1) values).entries.map Entry.position).Nodup
    rw [List.nodup_cons]
    refine ⟨?_,ih (start + 1)⟩
    intro hMem
    obtain ⟨e,he,hEq⟩ := List.mem_map.mp hMem
    obtain ⟨i,target,hl,hu,rfl⟩ := member_index model S A base fixed stride cell (start + 1) values e he
    rw [GeneralPaperReferenceSlotConstruction.position,GeneralPaperReferenceSlotConstruction.position] at hEq
    have hi := Nat.mul_le_mul_left stride hl
    have hOrder : stride * start + cell < stride * i + cell := by nlinarith only [hi,hStride]
    have h := Nat.mul_lt_mul_of_pos_left hOrder hA
    nlinarith only [h,hEq]

theorem location_values (model : RationalCostModel) (S A base fixed stride cell start count : ℕ)
    (values : List (FixedBinaryWord A)) (hCount : start + values.length ≤ count) (hCell : cell < stride)
    (hCap : base + A * (fixed + stride * count) < 2 ^ A) :
    ∀ e ∈ (run model S A base fixed stride cell start values).entries,e.location.value = e.position := by
  intro e he
  obtain ⟨i,value,hl,hu,rfl⟩ := member_index model S A base fixed stride cell start values e he
  exact GeneralPaperReferenceSlotConstruction.location_value model S A base fixed stride count i cell value (by omega) hCell hCap

theorem keys_nodup (model : RationalCostModel) (S A base fixed stride cell start count : ℕ)
    (values : List (FixedBinaryWord A)) (hA : 0 < A) (hCount : start + values.length ≤ count) (hCell : cell < stride)
    (hCap : base + A * (fixed + stride * count) < 2 ^ A) :
    ((run model S A base fixed stride cell start values).entries.map (fun e => e.location.value)).Nodup := by
  have hEq := List.map_congr_left (location_values model S A base fixed stride cell start count values hCount hCell hCap)
  rw [hEq]
  exact positions_nodup model S A base fixed stride cell start values hA (by omega)

theorem installed (model : RationalCostModel) (S A base fixed stride cell start count : ℕ)
    (values : List (FixedBinaryWord A)) (memory : GeneralPaperRawReferenceMemory.Memory A)
    (hA : 0 < A) (hCount : start + values.length ≤ count) (hCell : cell < stride)
    (hCap : base + A * (fixed + stride * count) < 2 ^ A) :
    ∀ e ∈ (run model S A base fixed stride cell start values).entries,
      (GeneralPaperRawReferenceMemory.read A
        (GeneralPaperRawReferenceMemory.install A memory (run model S A base fixed stride cell start values).entries).1
        e.location).1 = some e.target :=
  GeneralPaperRawReferenceMemory.installed A memory _ (keys_nodup model S A base fixed stride cell start count
    values hA hCount hCell hCap)

theorem lookup_target (model : RationalCostModel) (S A base fixed stride cell start : ℕ)
    (values : List (FixedBinaryWord A)) (index : ℕ) :
    (((run model S A base fixed stride cell start values).entries)[index]?).map Entry.target = values[index]? := by
  have h := congrArg (fun xs : List (FixedBinaryWord A) => xs[index]?) (targets model S A base fixed stride cell start values)
  simpa only [List.getElem?_map] using h

theorem lookup_location (model : RationalCostModel) (S A base fixed stride cell start : ℕ)
    (values : List (FixedBinaryWord A)) (index : ℕ) (hIndex : index < values.length) :
    (((run model S A base fixed stride cell start values).entries)[index]?).map Entry.location =
      some (FixedBinaryWord.ofNat A (base + A * (fixed + stride * (start + index) + cell))) := by
  induction values generalizing start index with
  | nil => simp only [List.length_nil] at hIndex; omega
  | cons value values ih =>
    cases index with
    | zero =>
      simp only [run,List.getElem?_cons_zero,Option.map_some,GeneralPaperReferenceSlotConstruction.location,Nat.add_zero]
    | succ index =>
      have hLength : index + 1 < values.length + 1 := hIndex
      have hTail : index < values.length := by omega
      have h := ih (start + 1) index hTail
      simpa only [run,GeneralPaperNaturalScalarStep.run,GeneralPaperNaturalScalarStep.Op.apply,
        List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end Blotto.GeneralPaperReferenceSlotBatch
