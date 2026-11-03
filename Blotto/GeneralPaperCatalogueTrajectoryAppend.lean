import Blotto.GeneralPaperCatalogueForestUpdate

/-! Append only the newly returned epoch rows by array pushes. The loop
reads each new row once; it does not traverse the previously recorded rows.
These are reference-array semantics, without a native allocator claim.
-/
namespace Blotto.GeneralPaperCatalogueTrajectoryAppend
set_option autoImplicit false

def pushPrefix {α : Type*} (chunk first : Array α) : (count : ℕ) → count≤chunk.size → Array α
  | 0,_ => first
  | count+1,h => (pushPrefix chunk first count (by omega)).push (chunk[count]'(by omega))

theorem pushPrefix_size {α : Type*} (chunk first : Array α) (count : ℕ) (h : count≤chunk.size) :
    (pushPrefix chunk first count h).size=first.size+count := by
  induction count with
  | zero => simp only [pushPrefix,Nat.add_zero]
  | succ count ih => simp only [pushPrefix,Array.size_push,ih,Nat.add_assoc]

theorem pushPrefix_old {α : Type*} (chunk first : Array α) (count : ℕ) (h : count≤chunk.size)
    (i : ℕ) (hi : i<first.size) :
    (pushPrefix chunk first count h)[i]'(by rw [pushPrefix_size]; omega)=first[i] := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [pushPrefix,Array.getElem_push,pushPrefix_size]
    rw [dif_pos (by omega)]
    exact ih (by omega)

theorem pushPrefix_new {α : Type*} (chunk first : Array α) (count : ℕ) (h : count≤chunk.size)
    (time : ℕ) (ht : time<count) :
    (pushPrefix chunk first count h)[first.size+time]'(by rw [pushPrefix_size]; omega)=chunk[time]'(by omega) := by
  induction count with
  | zero => omega
  | succ count ih =>
    simp only [pushPrefix,Array.getElem_push,pushPrefix_size]
    by_cases hc : time<count
    · rw [dif_pos (by omega)]
      exact ih (by omega) hc
    · rw [dif_neg (by omega)]
      have he : time=count := by omega
      subst time
      rfl

def append {α : Type*} (first chunk : Array α) : Array α := pushPrefix chunk first chunk.size le_rfl

theorem size {α : Type*} (first chunk : Array α) : (append first chunk).size=first.size+chunk.size :=
  pushPrefix_size chunk first chunk.size le_rfl

theorem old {α : Type*} (first chunk : Array α) (i : ℕ) (hi : i<first.size) :
    (append first chunk)[i]'(by rw [size]; omega)=first[i] := pushPrefix_old chunk first chunk.size le_rfl i hi

theorem new {α : Type*} (first chunk : Array α) (time : ℕ) (ht : time<chunk.size) :
    (append first chunk)[first.size+time]'(by rw [size]; omega)=chunk[time] :=
  pushPrefix_new chunk first chunk.size le_rfl time ht

end Blotto.GeneralPaperCatalogueTrajectoryAppend
