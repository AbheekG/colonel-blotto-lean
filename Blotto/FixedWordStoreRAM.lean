import Blotto.FixedWordRegion

/-! One fixed-width word store expands into exactly W existing-bit stores.
Every bit of the selected slot is written and other slots/frame are preserved.
Address primitive prices are supplied explicitly; payload codecs are separate. -/

namespace Blotto.FixedWordStoreRAM

def assignments {n W : ℕ} (j : Fin n) (word : Fin W → Bool) : List (Fin (n * W) × Bool) :=
  List.ofFn (fun offset => (FixedWordRegion.localAddress j offset, word offset))

theorem assignments_length {n W : ℕ} (j : Fin n) (word : Fin W → Bool) : (assignments j word).length = W :=
  List.length_ofFn

theorem assignments_keys_iff {n W : ℕ} (j : Fin n) (word : Fin W → Bool) (k : Fin n) (offset : Fin W) :
    FixedWordRegion.localAddress k offset ∈ (assignments j word).map Prod.fst ↔ k = j := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨e, he, hEq⟩
    rcases List.mem_ofFn.mp he with ⟨b, rfl⟩
    have hp : (j, b) = (k, offset) := finProdFinEquiv.injective
      (show finProdFinEquiv (j, b) = finProdFinEquiv (k, offset) from hEq)
    exact (congrArg Prod.fst hp).symm
  · intro h
    subst k
    exact List.mem_map.mpr ⟨(FixedWordRegion.localAddress j offset, word offset), List.mem_ofFn.mpr ⟨offset, rfl⟩, rfl⟩

def store {n W : ℕ} {β : Type*} (j : Fin n) (word : Fin W → Bool)
    (memory : Fin (n * W) → Bool) (frame : β) : TableStoreState (n * W) Bool β :=
  TableStoreRAM.run (assignments j word) ⟨memory, frame⟩

theorem store_read {n W : ℕ} {β : Type*} (j : Fin n) (word : Fin W → Bool)
    (memory : Fin (n * W) → Bool) (frame : β) (k : Fin n) (offset : Fin W) :
    (store j word memory frame).cells (FixedWordRegion.localAddress k offset) =
      if k = j then word offset else memory (FixedWordRegion.localAddress k offset) := by
  let a := FixedArrayTable.ofFn memory
  let final := fun address : Fin (n * W) =>
    let p := finProdFinEquiv.symm address
    if p.1 = j then word p.2 else memory address
  have ha : a.read = memory := by funext address; exact FixedArrayTable.read_ofFn memory address
  have hAssigned : ∀ e ∈ assignments j word, e.2 = final e.1 := by
    intro e he
    rcases List.mem_ofFn.mp he with ⟨b, rfl⟩
    change word b = if (finProdFinEquiv.symm (finProdFinEquiv (j, b))).1 = j then
      word (finProdFinEquiv.symm (finProdFinEquiv (j, b))).2 else memory (finProdFinEquiv (j, b))
    rw [Equiv.symm_apply_apply]
    simp only [ite_true]
  have hRun := congrArg (fun state : TableStoreState (n * W) Bool β => state.cells)
    (TableStoreRAM.run_refines_patch (assignments j word) a frame)
  rw [ha] at hRun
  change (TableStoreRAM.run (assignments j word) ⟨memory, frame⟩).cells (FixedWordRegion.localAddress k offset) = _
  rw [hRun]
  change (a.patch (assignments j word)).read (FixedWordRegion.localAddress k offset) = _
  rw [FixedArrayTable.read_patch a (assignments j word) final hAssigned]
  have hFinal : final (FixedWordRegion.localAddress k offset) =
      if k = j then word offset else memory (FixedWordRegion.localAddress k offset) := by
    change (if (finProdFinEquiv.symm (finProdFinEquiv (k, offset))).1 = j then
      word (finProdFinEquiv.symm (finProdFinEquiv (k, offset))).2 else memory (finProdFinEquiv (k, offset))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [hFinal, ha]
  by_cases h : k = j
  · have hMem := (assignments_keys_iff j word k offset).mpr h
    simp only [ite_eq_left hMem, ite_eq_left h]
  · have hMem : FixedWordRegion.localAddress k offset ∉ (assignments j word).map Prod.fst :=
      fun hMem => h ((assignments_keys_iff j word k offset).mp hMem)
    simp only [ite_eq_right hMem, ite_eq_right h]

theorem store_frame {n W : ℕ} {β : Type*} (j : Fin n) (word : Fin W → Bool)
    (memory : Fin (n * W) → Bool) (frame : β) : (store j word memory frame).frame = frame :=
  TableStoreRAM.run_frame _ _

theorem store_count {n W : ℕ} (j : Fin n) (word : Fin W → Bool) : TableStoreRAM.writeCount (assignments j word) = W := by
  rw [TableStoreRAM.writeCount_eq, assignments_length]

theorem storeWordWork_bound {n W : ℕ} (j : Fin n) (word : Fin W → Bool) (addressPrice : Fin (n * W) → ℕ)
    (A : ℕ) (hAddress : ∀ address, addressPrice address ≤ A) :
    TableStoreRAM.writeWordWork (fun _ : Bool => 1) addressPrice (assignments j word) ≤ W * (2 + A) := by
  have hp := TableStoreRAM.writeWordWork_bound (fun _ : Bool => 1) addressPrice (assignments j word) 1 A
    (fun _ _ => le_rfl) hAddress
  simpa only [assignments_length, Nat.mul_one] using hp

end Blotto.FixedWordStoreRAM
