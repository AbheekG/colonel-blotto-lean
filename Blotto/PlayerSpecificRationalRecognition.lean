import Blotto.PlayerSpecificRecognition
import Blotto.PlayerSpecificRatioSort

/-! Original positive normalized rational data enter the actual ratio sort,
one coefficient initialization, suffix pass, interval sweep, and complete
candidate search. Only degree-at-most-three real roots use the augmented
real-RAM primitive; all remaining runtime tests are scalar comparisons. -/
namespace Blotto
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure RationalPlayerSpecificInput (n : ℕ) where
  valuesA : RationalFieldSelector n
  valuesB : RationalFieldSelector n
  budget : ℚ
  budget_pos : 0<budget
  budget_le : budget≤1

namespace PlayerSpecificRationalRecognition
open PlayerSpecificCubic PlayerSpecificSweep PlayerSpecificSweepBounds
open PlayerSpecificCells PlayerSpecificCellCandidates PlayerSpecificRecognition

def arrayA {n : ℕ} (i : RationalPlayerSpecificInput n) : FixedArrayTable n ℚ := FixedArrayTable.ofFn i.valuesA.weight
def arrayB {n : ℕ} (i : RationalPlayerSpecificInput n) : FixedArrayTable n ℚ := FixedArrayTable.ofFn i.valuesB.weight

def ids {n : ℕ} (i : RationalPlayerSpecificInput n) : List (Fin n) :=
  (PlayerSpecificRatioSort.run (arrayA i) (arrayB i)).1.data.toList

theorem ids_sorted {n : ℕ} (i : RationalPlayerSpecificInput n) :
    ids i=GeneralPaperRowSort.sorted (PlayerSpecificRatioSort.prepare (arrayA i) (arrayB i)).1 := by
  unfold ids
  rw [PlayerSpecificRatioSort.data]
  simp only [GeneralPaperRowSort.order,List.toList_toArray]

theorem ids_perm {n : ℕ} (i : RationalPlayerSpecificInput n) : (ids i).Perm (List.finRange n) := by
  rw [ids_sorted]
  exact GeneralPaperRowSort.sorted_perm _

theorem ids_length {n : ℕ} (i : RationalPlayerSpecificInput n) : (ids i).length=n := by
  simpa only [List.length_finRange] using (ids_perm i).length_eq

theorem ids_order {n : ℕ} (i : RationalPlayerSpecificInput n) :
    (ids i).Pairwise (fun j k => i.valuesA.values.weight j/i.valuesB.values.weight j ≤
      i.valuesA.values.weight k/i.valuesB.values.weight k) := by
  rw [ids_sorted]
  apply (GeneralPaperRowSort.sorted_order (PlayerSpecificRatioSort.prepare (arrayA i) (arrayB i)).1).imp
  intro j k hjk
  have hq : i.valuesA.weight j/i.valuesB.weight j ≤ i.valuesA.weight k/i.valuesB.weight k := by
    have hle := hjk.elim le_of_lt (fun h => h.1.le)
    simpa only [PlayerSpecificRatioSort.ratio_read,arrayA,arrayB,FixedArrayTable.read_ofFn] using hle
  change (i.valuesA.weight j : ℝ)/(i.valuesB.weight j : ℝ)≤
    (i.valuesA.weight k : ℝ)/(i.valuesB.weight k : ℝ)
  exact_mod_cast hq

/-- Literal constant-work accumulation of the two initially nonzero sums.
The other coefficients and the empty prefix maximum start at zero. -/
noncomputable def initialSums : List (ℝ×ℝ) → State ℝ×ℕ
  | [] => (⟨⟨0,0,0,0⟩,0⟩,8)
  | x::xs =>
    let tail := initialSums xs
    (⟨⟨x.2+tail.1.coefficients.A1,0,x.2^2/x.1+tail.1.coefficients.B1,0⟩,0⟩,tail.2+32)

theorem initialSums_data (fields : List (ℝ×ℝ)) : (initialSums fields).1=initial fields := by
  induction fields with
  | nil => rfl
  | cons x xs ih => simp only [initialSums,ih,initial,List.map_cons,List.sum_cons]

theorem initialSums_work (fields : List (ℝ×ℝ)) : (initialSums fields).2=32*fields.length+8 := by
  induction fields with
  | nil => rfl
  | cons x xs ih => simp only [initialSums,List.length_cons,ih]; omega

noncomputable def run {n : ℕ} (i : RationalPlayerSpecificInput n) : Option (Cell×ℝ)×ℕ :=
  let sorted := PlayerSpecificRatioSort.run (arrayA i) (arrayB i)
  let fields := sorted.1.data.toList.map (fun j => ((i.valuesA.weight j : ℝ),(i.valuesB.weight j : ℝ)))
  let sums := initialSums fields
  let suffix := suffixes fields
  let cells := build sums.1 0 suffix.2.1
  let found := PlayerSpecificRootSearch.run (i.budget : ℝ) cells.1
  (found.1,sorted.2+(64*n+32)+sums.2+suffix.2.2+cells.2+found.2+16)

theorem data {n : ℕ} (i : RationalPlayerSpecificInput n) :
    (run i).1=(PlayerSpecificRootSearch.run (i.budget : ℝ)
      (intervals i.valuesA.values i.valuesB.values (ids i))).1 := by
  simp only [run,intervals,initialSums_data,ids,RationalFieldSelector.values]

theorem work {n : ℕ} (i : RationalPlayerSpecificInput n) :
    (run i).2≤4096*(n+1)*(binaryWordWidth (n+1)+2) := by
  let fields := (ids i).map (fun j => ((i.valuesA.weight j : ℝ),(i.valuesB.weight j : ℝ)))
  have hf : fields.length=n := by simp only [fields,List.length_map,ids_length]
  have hSuffix : (suffixes fields).2.1.length=n := by
    have h := congrArg List.length (suffixes_fields fields)
    simpa only [List.length_map,hf] using h
  have hs := PlayerSpecificRatioSort.work (arrayA i) (arrayB i)
  have hi := initialSums_work fields
  have hm := suffixes_work fields
  have hc := PlayerSpecificCells.work (initialSums fields).1 0 (suffixes fields).2.1
  have hcount := PlayerSpecificCells.count (initialSums fields).1 0 (suffixes fields).2.1
  have hr := PlayerSpecificRootSearch.work (i.budget : ℝ)
    (build (initialSums fields).1 0 (suffixes fields).2.1).1
  rw [hf] at hi hm
  rw [hSuffix] at hc hcount
  rw [hcount] at hr
  have hL : 2≤binaryWordWidth (n+1)+2 := by omega
  have hLarge := Nat.mul_le_mul_left (n+1) hL
  change (PlayerSpecificRatioSort.run (arrayA i) (arrayB i)).2+(64*n+32)+
    (initialSums fields).2+(suffixes fields).2.2+(build (initialSums fields).1 0 (suffixes fields).2.1).2+
    (PlayerSpecificRootSearch.run (i.budget : ℝ) (build (initialSums fields).1 0 (suffixes fields).2.1).1).2+16≤_
  nlinarith only [hs,hi,hm,hc,hr,hLarge]

theorem sound {n : ℕ} (i : RationalPlayerSpecificInput n) (c : Cell) (gamma : ℝ)
    (h : (run i).1=some (c,gamma)) :
    ValidParameters i.valuesA.values i.valuesB.values (i.budget : ℝ) gamma
      (candidateScale c.state.coefficients (i.budget : ℝ) gamma) := by
  rw [data] at h
  exact PlayerSpecificRecognition.sound i.valuesA.values i.valuesB.values (ids i) (ids_perm i) (ids_order i)
    _ gamma (by exact_mod_cast i.budget_pos) c h

theorem complete {n : ℕ} (i : RationalPlayerSpecificInput n) (gamma scale : ℝ)
    (h : ValidParameters i.valuesA.values i.valuesB.values (i.budget : ℝ) gamma scale) :
    ∃ chosen,(run i).1=some chosen := by
  rw [data]
  exact PlayerSpecificRecognition.complete i.valuesA.values i.valuesB.values (ids i) (ids_perm i) (ids_order i)
    _ gamma scale (by exact_mod_cast i.budget_pos) (by exact_mod_cast i.budget_le) h

theorem rejection_iff {n : ℕ} (i : RationalPlayerSpecificInput n) :
    (run i).1=none ↔ ¬∃ gamma scale,
      ValidParameters i.valuesA.values i.valuesB.values (i.budget : ℝ) gamma scale := by
  rw [data]
  exact PlayerSpecificRecognition.rejection_iff i.valuesA.values i.valuesB.values (ids i) (ids_perm i) (ids_order i)
    _ (by exact_mod_cast i.budget_pos) (by exact_mod_cast i.budget_le)

end PlayerSpecificRationalRecognition
end Blotto
