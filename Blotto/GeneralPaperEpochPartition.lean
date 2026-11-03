import Blotto.GeneralPaperPreparedPartition

/-! Build the source partition from native threshold and extra-code arrays.
Both each position and its successor are inserted. Extra codes include cached
candidate/response codes and a signed block's sign boundary.
-/
namespace Blotto.GeneralPaperEpochPartition
open GeneralPaperEpochCellInstructions
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem read_mem {n : ℕ} (values : FixedArrayTable n ℕ) (r : Fin n) : values.read r∈values.data.toList := by
  have hi : r.val<values.data.toList.length := by rw [Array.length_toList,values.size]; exact r.isLt
  have he := List.getElem_mem hi
  simpa only [Array.getElem_toList,FixedArrayTable.read] using he

def points {n m : ℕ} (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) : List ℕ :=
  let p := positions.data.toList
  p++p.map (fun x => x+1)++extras.data.toList

def prepare {n m : ℕ} (U : ℕ) (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) : GeneralPaperPreparedPartition.Prepared :=
  GeneralPaperPreparedPartition.build U (points positions extras)

theorem points_length {n m : ℕ} (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    (points positions extras).length=2*n+m := by
  simp only [points,List.length_append,List.length_map,Array.length_toList,positions.size,extras.size]
  omega

theorem position_mem {n m : ℕ} (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) (r : Fin n) :
    positions.read r∈points positions extras := by
  simp only [points,List.mem_append]
  exact Or.inl (Or.inl (read_mem positions r))

theorem successor_mem {n m : ℕ} (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) (r : Fin n) :
    positions.read r+1∈points positions extras := by
  simp only [points,List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.mpr ⟨positions.read r,read_mem positions r,rfl⟩))

theorem extra_mem {n m : ℕ} (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) (r : Fin m) :
    extras.read r∈points positions extras := by
  simp only [points,List.mem_append]
  exact Or.inr (read_mem extras r)

theorem count_bound {n m : ℕ} (U : ℕ) (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    (prepare U positions extras).count≤2*n+m+1 := by
  have he := GeneralPaperPreparedPartition.count_bound U (points positions extras)
  simpa only [prepare,points_length] using he

theorem covers {n m : ℕ} (U : ℕ) (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    Covers U (prepare U positions extras).intervals := GeneralPaperPreparedPartition.partition_covers _ _

theorem disjoint {n m : ℕ} (U : ℕ) (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    GeneralPaperEpochCellInstructions.Disjoint (prepare U positions extras).intervals :=
  GeneralPaperPreparedPartition.partition_disjoint _ _

theorem strict_test_constant {n m : ℕ} (U : ℕ) (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (a : Fin n) (hA : positions.read a<U) (r : Fin (prepare U positions extras).count) (i j : ℕ)
    (hI : Contains (prepare U positions extras).intervals r i) (hJ : Contains (prepare U positions extras).intervals r j) :
    positions.read a< i ↔ positions.read a<j := by
  have he := GeneralPaperPreparedPartition.threshold_constant U (points positions extras) (positions.read a+1)
    (successor_mem positions extras a) (by omega) r i j hI hJ
  omega

theorem weak_test_constant {n m : ℕ} (U : ℕ) (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (a : Fin n) (hA : positions.read a<U) (r : Fin (prepare U positions extras).count) (i j : ℕ)
    (hI : Contains (prepare U positions extras).intervals r i) (hJ : Contains (prepare U positions extras).intervals r j) :
    positions.read a≤ i ↔ positions.read a≤j :=
  GeneralPaperPreparedPartition.threshold_constant U (points positions extras) (positions.read a)
    (position_mem positions extras a) hA.le r i j hI hJ

theorem extra_test_constant {n m : ℕ} (U : ℕ) (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (a : Fin m) (hA : extras.read a≤U) (r : Fin (prepare U positions extras).count) (i j : ℕ)
    (hI : Contains (prepare U positions extras).intervals r i) (hJ : Contains (prepare U positions extras).intervals r j) :
    extras.read a≤ i ↔ extras.read a≤j :=
  GeneralPaperPreparedPartition.threshold_constant U (points positions extras) (extras.read a)
    (extra_mem positions extras a) hA r i j hI hJ

end Blotto.GeneralPaperEpochPartition
