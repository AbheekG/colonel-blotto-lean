import Blotto.GeneralPaperCellCatalogue

/-! Pad optional per-cell entries to a common native slot count. Slot zero
is the actually decoded zero option. Missing cells and unused slots store
only duplicates of zero, so padding adds no new action. Each nonempty cell
retains its original typed entry at index cell+1.
-/
namespace Blotto.GeneralPaperCatalogueSlots
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCodeMinimumScan
set_option autoImplicit false
set_option maxHeartbeats 3500000

def zero (a : Alphabet) : Entry := ⟨0,⟨grid a 0,false⟩⟩

def value {n cap : ℕ} (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) (i : Fin (cap+1)) : Entry :=
  if i.val=0 then zero a
  else if h : i.val-1<n then (raw.read ⟨i.val-1,h⟩).getD (zero a) else zero a

def build {n cap : ℕ} (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) : FixedArrayTable (cap+1) Entry × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i => (value a raw i,20))

theorem read_build {n cap : ℕ} (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) (i : Fin (cap+1)) :
    (build a raw).1.read i=value a raw i := by
  rw [build,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem read_zero {n cap : ℕ} (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) :
    (build (cap:=cap) a raw).1.read 0=zero a := by
  rw [read_build]
  simp only [value,Fin.val_zero,ite_true]

theorem read_cell {n cap : ℕ} (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) (hCount : n≤cap)
    (r : Fin n) (entry : Entry) (hSome : raw.read r=some entry) :
    (build (cap:=cap) a raw).1.read ⟨r.val+1,by have := r.isLt; omega⟩=entry := by
  rw [read_build]
  simp only [value,show ¬r.val+1=0 by omega,ite_false,Nat.add_sub_cancel,r.isLt,dif_pos,hSome,Option.getD_some]

theorem entry_cases {n cap : ℕ} (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) (i : Fin (cap+1)) :
    (build a raw).1.read i=zero a ∨ ∃ r, raw.read r=some ((build a raw).1.read i) := by
  rw [read_build]
  dsimp only [value]
  split
  · exact Or.inl rfl
  · split
    · rename_i h
      cases hr : raw.read ⟨i.val-1,h⟩ with
      | none => exact Or.inl rfl
      | some entry => exact Or.inr ⟨⟨i.val-1,h⟩,hr⟩
    · exact Or.inl rfl

theorem decoded {n cap : ℕ} (a : Alphabet) (response : Bool) (raw : FixedArrayTable n (Option Entry))
    (hRaw : ∀ r entry, raw.read r=some entry → (decode a response entry.cost).choice=some entry.predecessor)
    (i : Fin (cap+1)) :
    (decode a response ((build a raw).1.read i).cost).choice=some ((build a raw).1.read i).predecessor := by
  rcases entry_cases a raw i with hz|⟨r,hr⟩
  · rw [hz]
    exact GeneralPaperCodeDecodeSound.decode_zero a response
  · exact hRaw r _ hr

theorem zero_tag (a : Alphabet) : (zero a).predecessor.tag=0 := GeneralPaperCodeDecodeSound.zero_tag a

theorem build_work {n cap : ℕ} (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) :
    (build (cap:=cap) a raw).2=62*(cap+1)+18 := by
  rw [build,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

end Blotto.GeneralPaperCatalogueSlots
