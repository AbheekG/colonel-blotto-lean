import Blotto.GeneralPaperInitialForestConstructionStorage

/-! Native reference-push append storage includes both input owners,
reserved old/new prefix buffers, the complete returned trajectory, recursive
control frames and one guarded row/read/push scratch window. Payload caps
are derived from the caller's actual rows, without traversing old rows. -/
namespace Blotto.GeneralPaperTrajectoryAppendStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperRetainedTrajectoryBits (rowBits)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def RowsBound {m : ℕ} (L : ℕ) (rows : Array (FixedArrayTable m ℕ)) : Prop :=
  ∀ i : Fin rows.size,rowBits rows[i.val]≤m*L

def rowsProfile (W m capacity L : ℕ) : ℕ := capacity*(m*L+m*W+65*W)+64*W

theorem rows_bounded {m : ℕ} (W capacity L : ℕ) (rows : Array (FixedArrayTable m ℕ))
    (hc : rows.size≤capacity) (hr : RowsBound L rows) :
    GeneralPaperEncodedTrajectoryStorage.footprint W capacity rows≤rowsProfile W m capacity L := by
  have hb := GeneralPaperRetainedTrajectoryBits.trajectory_bound rows L hr
  have hp := Nat.mul_le_mul_right (m*L) hc
  have hs := Nat.mul_le_mul_right (m*W+64*W) hc
  unfold GeneralPaperEncodedTrajectoryStorage.footprint rowsProfile
  nlinarith only [hb,hp,hs]

theorem prefix_rows {m : ℕ} (W capacity L : ℕ) (first chunk : Array (FixedArrayTable m ℕ))
    (hf : RowsBound L first) (hc : RowsBound L chunk) (count : ℕ) (hn : count≤chunk.size) :
    RowsBound L (GeneralPaperTrajectoryAppendExecution.pushPrefix true (fun w => w) W capacity chunk first count hn).1 := by
  rw [GeneralPaperTrajectoryAppendExecution.prefix_data]
  intro i
  by_cases hi : i.val<first.size
  · rw [GeneralPaperCatalogueTrajectoryAppend.pushPrefix_old chunk first count hn i.val hi]
    exact hf ⟨i.val,hi⟩
  · have htotal : i.val<first.size+count := i.isLt.trans_eq (GeneralPaperCatalogueTrajectoryAppend.pushPrefix_size chunk first count hn)
    have hj : i.val-first.size<count := by omega
    have he : first.size+(i.val-first.size)=i.val := by omega
    have hread := GeneralPaperCatalogueTrajectoryAppend.pushPrefix_new chunk first count hn (i.val-first.size) hj
    simp only [he] at hread
    rw [hread]
    exact hc ⟨i.val-first.size,by omega⟩

def frames (W capacity n : ℕ) : ℕ := (n+1)*(8*natBits (capacity+2)+256*W)

def active {m : ℕ} (W capacity : ℕ) (first chunk : Array (FixedArrayTable m ℕ)) (count : ℕ) : ℕ :=
  if h : count<chunk.size then
    let A := GeneralPaperSummaryArrayExecution.arrayWord W (capacity+2)
    GeneralPaperEncodedTrajectoryStorage.rowFootprint W chunk[count]+
      (64*A+PaperIndexedArrayConstruction.stepWork (fun w => w) A (first.size+count)+GeneralPaperLocalEpochExecution.control (fun w => w) A (count+1))
  else 0

def window {m : ℕ} (W capacity : ℕ) (first chunk : Array (FixedArrayTable m ℕ)) (count : ℕ) (hn : count≤chunk.size) : ℕ :=
  let current := (GeneralPaperTrajectoryAppendExecution.pushPrefix true (fun w => w) W capacity chunk first count hn).1
  GeneralPaperEncodedTrajectoryStorage.footprint W capacity first+GeneralPaperEncodedTrajectoryStorage.footprint W capacity chunk+
    2*GeneralPaperEncodedTrajectoryStorage.footprint W capacity current+
    GeneralPaperEncodedTrajectoryStorage.footprint W capacity (GeneralPaperTrajectoryAppendExecution.run true (fun w => w) W capacity first chunk).1+
    frames W capacity chunk.size+active W capacity first chunk count+
    fields W [capacity,capacity+2,first.size,chunk.size,count,count+1,first.size+count,first.size+count+1]+256*W

def profile (W m capacity chunkSize L : ℕ) : ℕ :=
  5*rowsProfile W m capacity L+frames W capacity chunkSize+
    (m*L+m*W+64*W)+256*GeneralPaperSummaryArrayExecution.arrayWord W (capacity+2)+
    (8*(natBits (capacity+2)+W)+32*W)+256*W

theorem bounded {m : ℕ} (W capacity L : ℕ) (first chunk : Array (FixedArrayTable m ℕ)) (count : ℕ) (hn : count≤chunk.size)
    (ht : first.size+chunk.size≤capacity) (hf : RowsBound L first) (hc : RowsBound L chunk) :
    window W capacity first chunk count hn≤profile W m capacity chunk.size L := by
  have hfirst := rows_bounded W capacity L first (by omega) hf
  have hchunk := rows_bounded W capacity L chunk (by omega) hc
  have hp := rows_bounded W capacity L
    (GeneralPaperTrajectoryAppendExecution.pushPrefix true (fun w => w) W capacity chunk first count hn).1
    (GeneralPaperTrajectoryAppendExecution.prefix_capacity true (fun w => w) W capacity chunk first count hn ht)
    (prefix_rows W capacity L first chunk hf hc count hn)
  have hr := rows_bounded W capacity L (GeneralPaperTrajectoryAppendExecution.run true (fun w => w) W capacity first chunk).1
    (GeneralPaperTrajectoryAppendExecution.prefix_capacity true (fun w => w) W capacity chunk first chunk.size (Nat.le_refl _) ht)
    (prefix_rows W capacity L first chunk hf hc chunk.size (Nat.le_refl _))
  have ha : active W capacity first chunk count≤(m*L+m*W+64*W)+256*GeneralPaperSummaryArrayExecution.arrayWord W (capacity+2) := by
    unfold active
    split
    · rename_i h
      have hrow := hc ⟨count,h⟩
      change rowBits chunk[count]≤m*L at hrow
      have hrow' : GeneralPaperEncodedTrajectoryStorage.rowFootprint W chunk[count]≤m*L+m*W+64*W := by
        unfold GeneralPaperEncodedTrajectoryStorage.rowFootprint GeneralPaperEncodedNatArray.footprint GeneralPaperEncodedNatArray.payload
        unfold rowBits at hrow
        omega
      have hstep := GeneralPaperTrajectoryAppendPrice.step (fun w => w) (fun _ _ h => h)
        (GeneralPaperSummaryArrayExecution.arrayWord W (capacity+2)) capacity (first.size+count) count
        (GeneralPaperSummaryArrayControls.array_word_positive W (capacity+2)) (by omega) (by omega)
        (GeneralPaperLocalEpochPrice.capacity_word W capacity)
      exact Nat.add_le_add hrow' hstep
    · exact Nat.zero_le _
  have hi := fields_bound W (natBits (capacity+2)) [capacity,capacity+2,first.size,chunk.size,count,count+1,first.size+count,first.size+count+1] (by
    intro x hx; apply GeneralPaperRankStorageMonotonicity.nat_word
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals omega)
  simp only [List.length_cons,List.length_nil] at hi
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperTrajectoryAppendStorage
