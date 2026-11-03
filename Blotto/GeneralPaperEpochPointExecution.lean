import Blotto.GeneralPaperPricedListAppend

/-! One conversion of each retained input array, one successor map and
two left-list appends. Position/successor order and every extra are retained.
No alphabet is enumerated and no second length traversal is introduced.
-/
namespace Blotto.GeneralPaperEpochPointExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def successor (price : ℕ → ℕ) (W x : ℕ) : ℕ × ℕ :=
  (x+1,GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) x 1+32*W)

def run {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) : List ℕ × ℕ :=
  let p := StoredArrayReferenceList.list positions.data
  let e := StoredArrayReferenceList.list extras.data
  let successors := GeneralPaperPricedListMap.run W (successor price W) p
  let joined := GeneralPaperPricedListAppend.run W p successors.1
  let all := GeneralPaperPricedListAppend.run W joined.1 e
  (all.1,StoredArrayReferenceList.work index (if bits then arrayWord W (n+2) else W) positions.data.size+
    StoredArrayReferenceList.work index (if bits then arrayWord W (m+2) else W) extras.data.size+
    successors.2+joined.2+all.2+64*W)

theorem data {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    (run bits index price W positions extras).1=GeneralPaperEpochPartition.points positions extras := by
  simp only [run,GeneralPaperPricedListAppend.data,GeneralPaperPricedListMap.data,
    StoredArrayReferenceList.list_data,successor,GeneralPaperEpochPartition.points]

theorem length {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    (run bits index price W positions extras).1.length=2*n+m := by
  rw [data]
  exact GeneralPaperEpochPartition.points_length positions extras

theorem member_bound {n : ℕ} (U : ℕ) (values : FixedArrayTable n ℕ) (hBounds : ∀ r,values.read r≤U)
    (x : ℕ) (hx : x∈values.data.toList) : x≤U := by
  obtain ⟨i,hi,hx⟩ := List.getElem_of_mem hx
  have hiN : i<n := by simpa only [Array.length_toList,values.size] using hi
  have he : values.read ⟨i,hiN⟩=x := by simpa only [FixedArrayTable.read,Array.getElem_toList] using hx
  rw [←he]
  exact hBounds ⟨i,hiN⟩

theorem points_bound {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (hPositions : ∀ r,positions.read r<U) (hExtras : ∀ r,extras.read r≤U)
    (x : ℕ) (hx : x∈(run bits index price W positions extras).1) : x≤U := by
  rw [data,GeneralPaperEpochPartition.points] at hx
  rcases List.mem_append.mp hx with hx|hx
  · rcases List.mem_append.mp hx with hx|hx
    · exact member_bound U positions (fun r => (hPositions r).le) x hx
    · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      have hyU := member_bound (U-1) positions (fun r => by have h := hPositions r; omega) y hy
      have hPos : 0<U := by
        obtain ⟨i,hi,he⟩ := List.getElem_of_mem hy
        have hiN : i<n := by simpa only [Array.length_toList,positions.size] using hi
        have h := hPositions ⟨i,hiN⟩
        omega
      omega
  · exact member_bound U extras hExtras x hx

end Blotto.GeneralPaperEpochPointExecution
