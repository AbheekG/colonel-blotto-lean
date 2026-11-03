import Blotto.GeneralPaperSourceScoreStorage

/-! Encoded residency of the actual full score/resource matrix. Entries
include their integer score, rational anchor and pair metadata; both array
levels include slots and descriptors. The DP input list borrows the same
field arrays, so its list nodes are counted without copying the matrix. -/
namespace Blotto.GeneralPaperEncodedScoreMatrixStorage
open GeneralPaperExactScoreDP GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def entryFootprint (W : ℕ) (a : ℕ×ℚ) : ℕ := natBits a.1+rationalWordWidth a.2+34*W
def entryProfile (W S A : ℕ) : ℕ := natBits S+(1+2*A)+34*W

theorem entry_bound (W S A : ℕ) (a : ℕ×ℚ) (hs : a.1≤S) (ha : RationalHeight a.2 A) :
    entryFootprint W a≤entryProfile W S A := by
  have hS := binaryWordWidth_mono hs
  have hA := rationalWordWidth_of_height ha
  unfold entryFootprint entryProfile natBits
  omega

def fieldFootprint {K : ℕ} (W : ℕ) (a : Field K) : ℕ := footprint W (entryFootprint W) a.data
def fieldProfile (W K S A : ℕ) : ℕ := K*(entryProfile W S A+W)+64*W

theorem field_bound {K : ℕ} (W S A : ℕ) (a : Field K) (hs : ∀ l,(a.read l).1≤S)
    (ha : ∀ l,RationalHeight (a.read l).2 A) : fieldFootprint W a≤fieldProfile W K S A := by
  have hb := bounded W (entryProfile W S A) (entryFootprint W) a.data (by
    intro i
    let l : Fin K := ⟨i.val,i.isLt.trans_eq a.size⟩
    exact entry_bound W S A (a.read l) (hs l) (ha l))
  simpa only [fieldFootprint,fieldProfile,a.size] using hb

def matrixFootprint {m K : ℕ} (W : ℕ) (a : FixedArrayTable m (Field K)) : ℕ :=
  footprint W (fieldFootprint W) a.data
def matrixProfile (W m K S A : ℕ) : ℕ := m*(fieldProfile W K S A+W)+64*W

theorem matrix_bound {m K : ℕ} (W S A : ℕ) (a : FixedArrayTable m (Field K))
    (hs : ∀ j l,((a.read j).read l).1≤S) (ha : ∀ j l,RationalHeight ((a.read j).read l).2 A) :
    matrixFootprint W a≤matrixProfile W m K S A := by
  have hb := bounded W (fieldProfile W K S A) (fieldFootprint W) a.data (by
    intro i
    let j : Fin m := ⟨i.val,i.isLt.trans_eq a.size⟩
    exact field_bound W S A (a.read j) (hs j) (ha j))
  simpa only [matrixFootprint,matrixProfile,a.size] using hb

theorem score_bound {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (j : Fin m) (l : Fin K) :
    GeneralPaperStrictScore.score v S j l≤S := by
  have h := Finset.single_le_sum (f:=fun t : Fin m => GeneralPaperStrictScore.score v S t l)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact h.trans (GeneralPaperComputedThreshold.totalScore_le v S hK (fun _ => l))

theorem native_field {T m K : ℕ} (model : RationalCostModel) (W depth S A : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (hK : 0<K)
    (hCap : S<2^depth) (j : Fin m) (ha : ∀ l,RationalHeight (dict.anchor j l) A) :
    fieldFootprint W (GeneralPaperScoreMatrixBits.fieldRun model W depth dict v S j).1≤fieldProfile W K S A := by
  rw [GeneralPaperScoreMatrixBits.field_data model W depth dict v S hK hCap j]
  apply field_bound
  · intro l
    simpa only [FixedArrayTable.read_ofFn] using score_bound v S hK j l
  · intro l
    simpa only [FixedArrayTable.read_ofFn] using ha l

theorem native_matrix {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W depth S A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (v : RationalFieldSelector m)
    (hK : 0<K) (hCap : S<2^depth) (ha : ∀ j l,RationalHeight ((columns.read j).anchors.read l) A) :
    matrixFootprint W (GeneralPaperPhysicalScoreMatrix.run bits model W depth columns v S).1≤matrixProfile W m K S A := by
  rw [GeneralPaperPhysicalScoreMatrix.data bits model W depth columns v S hK hCap]
  apply matrix_bound
  · intro j l
    simpa only [FixedArrayTable.read_ofFn] using score_bound v S hK j l
  · intro j l
    simpa only [FixedArrayTable.read_ofFn] using ha j l

theorem borrowed_fields {m K : ℕ} (W : ℕ) (a : FixedArrayTable m (Field K)) :
    listFootprint W (fun _ : Field K => 0) a.data.toList=m*(2*W)+32*W := by
  simp [listFootprint,a.size]

@[fun_prop]
theorem matrix_profile_scale (m K S A : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => matrixProfile W m K S A) := by
  unfold matrixProfile fieldProfile entryProfile
  fun_prop

end Blotto.GeneralPaperEncodedScoreMatrixStorage
