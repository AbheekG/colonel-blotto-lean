import Blotto.GeneralPaperQuantizedColumn

/-! Actual full-row quantization. Each original row retains its identity
through every field's inverse permutation. Prepared columns store labels and
anchors once; the dictionary uses only these retained array readers.
-/
namespace Blotto.GeneralPaperRowQuantizer
open GeneralPaperDictionary
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators Classical

def columnInput {T m : ℕ} (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (j : Fin m) : FixedArrayTable T ℚ :=
  FixedArrayTable.ofFn (fun i => (rows.read i).read j)

def prepare {K B m : ℕ} (hK : 0<K) (hB : 0<B) (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) :
    FixedArrayTable m (GeneralPaperQuantizedColumn.Column (K*B) K) :=
  FixedArrayTable.ofFn (fun j => GeneralPaperQuantizedColumn.build hK hB (columnInput rows j))

def dictionary {T m K : ℕ} (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) : Dictionary T m K :=
  ⟨fun i j => (columns.read j).labels.read i,fun j l => (columns.read j).anchors.read l⟩

def build {K B m : ℕ} (hK : 0<K) (hB : 0<B) (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) : Dictionary (K*B) m K :=
  let columns := prepare hK hB rows
  dictionary columns

def original {T m : ℕ} (rows : FixedArrayTable T (FixedArrayTable m ℚ)) : Dictionary T m T :=
  ⟨fun i _ => i,fun j i => (rows.read i).read j⟩

theorem balanced {K B m : ℕ} (hK : 0<K) (hB : 0<B) (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) :
    Balanced (build hK hB rows) := by
  apply balanced_of_counts _ (Nat.mul_pos hK hB) hK
  intro j l
  have h := GeneralPaperQuantizedColumn.label_count hK hB (columnInput rows j) l
  have hc : (Finset.univ.filter (fun i => (build hK hB rows).label i j=l)).card=B := by
    simpa only [build,dictionary,prepare,FixedArrayTable.read_ofFn] using h
  rw [hc]
  exact Nat.mul_comm B K

theorem anchor_zero {K B m : ℕ} (hK : 0<K) (hB : 0<B) (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (j : Fin m) :
    (build hK hB rows).anchor j ⟨0,hK⟩=0 := by
  simpa only [build,dictionary,prepare,FixedArrayTable.read_ofFn] using
    GeneralPaperQuantizedColumn.zero_anchor hK hB (columnInput rows j)

theorem anchors_nonnegative {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hRows : ∀ i j,0≤(rows.read i).read j) (j : Fin m) (l : Fin K) :
    0≤(build hK hB rows).anchor j l := by
  have hColumn (i : Fin (K*B)) : 0≤(columnInput rows j).read i := by
    simpa only [columnInput,FixedArrayTable.read_ofFn] using hRows i j
  simpa only [build,dictionary,prepare,FixedArrayTable.read_ofFn] using
    GeneralPaperQuantizedColumn.anchors_nonnegative hK hB (columnInput rows j) hColumn l

theorem anchors_ordered {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hRows : ∀ i j,0≤(rows.read i).read j) (j : Fin m) :
    Monotone ((build hK hB rows).anchor j) := by
  have hColumn (i : Fin (K*B)) : 0≤(columnInput rows j).read i := by
    simpa only [columnInput,FixedArrayTable.read_ofFn] using hRows i j
  simpa only [build,dictionary,prepare,FixedArrayTable.read_ofFn] using
    GeneralPaperQuantizedColumn.anchors_ordered hK hB (columnInput rows j) hColumn

theorem row_coordinate_le {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hRows : ∀ i j,0≤(rows.read i).read j)
    (i : Fin (K*B)) (j : Fin m) :
    (build hK hB rows).anchor j ((build hK hB rows).label i j) ≤ (rows.read i).read j := by
  have hColumn (i : Fin (K*B)) : 0≤(columnInput rows j).read i := by
    simpa only [columnInput,FixedArrayTable.read_ofFn] using hRows i j
  simpa only [build,dictionary,prepare,FixedArrayTable.read_ofFn,columnInput,GeneralPaperQuantizedColumn.bid] using
    GeneralPaperQuantizedColumn.bid_le_original hK hB (columnInput rows j) hColumn i

theorem every_row_feasible {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (budget : ℝ)
    (hRows : ∀ i,Feasible budget (fun j => ((rows.read i).read j:ℝ))) (i : Fin (K*B)) :
    Feasible budget ((law (build hK hB rows) (Nat.mul_pos hK hB)).realRow i) := by
  have hNonnegative (i : Fin (K*B)) (j : Fin m) : 0≤(rows.read i).read j := by
    have h := (hRows i).1 j
    change (0:ℝ) ≤ ((rows.read i).read j:ℝ) at h
    exact_mod_cast h
  refine ⟨?_,?_⟩
  · intro j
    change (0:ℝ) ≤ (build hK hB rows).anchor j ((build hK hB rows).label i j)
    exact_mod_cast anchors_nonnegative hK hB rows hNonnegative j ((build hK hB rows).label i j)
  · apply le_trans (b := ∑ j,((rows.read i).read j:ℝ))
    · apply Finset.sum_le_sum
      intro j _
      change ((build hK hB rows).anchor j ((build hK hB rows).label i j):ℝ) ≤ ((rows.read i).read j:ℝ)
      exact_mod_cast row_coordinate_le hK hB rows hNonnegative i j
    · exact (hRows i).2

theorem law_supported {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (budget : ℝ)
    (hRows : ∀ i,Feasible budget (fun j => ((rows.read i).read j:ℝ))) :
    Supported budget (law (build hK hB rows) (Nat.mul_pos hK hB)).law :=
  RationalWholeRowLaw.law_supported _ budget (every_row_feasible hK hB rows budget hRows)

end Blotto.GeneralPaperRowQuantizer
