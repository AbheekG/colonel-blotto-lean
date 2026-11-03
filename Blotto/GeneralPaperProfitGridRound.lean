import Blotto.GeneralPaperProfitGridPrepare

/-! Actual floor-to-grid queries. Leaves compare pre-scaled grid entries
to P*F, and merges compare raw grid numerators to their sum. The two cached
arrays and their depth are reused by every query in every optimizer call.
-/
namespace Blotto.GeneralPaperProfitGridRound
open GeneralPaperProfitGridPoints GeneralPaperProfitGridPrepare
set_option autoImplicit false
set_option maxHeartbeats 3500000

def merge {q w B : ℕ} (grid : Prepared q w B) (numerator : ℕ) : GeneralPaperFloorSearch.Result grid.size :=
  let found := GeneralPaperFloorSearch.lookup grid.numerators grid.nonempty grid.depth (numerator+1)
  ⟨found.label,found.work+8⟩

def leaf {q w B : ℕ} (grid : Prepared q w B) (numerator : ℕ) : GeneralPaperFloorSearch.Result grid.size :=
  let found := GeneralPaperFloorSearch.lookup grid.leafNumerators grid.nonempty grid.depth (numerator*grid.profitDenominator+1)
  ⟨found.label,found.work+16⟩

theorem merge_down (q w B numerator : ℕ) :
    (prepare q w B).numerators.read (merge (prepare q w B) numerator).label≤numerator := by
  have he := GeneralPaperFloorSearch.lookup_value (prepare q w B).numerators (prepare q w B).nonempty
    (prepare q w B).depth (numerator+1) (strict q w B).monotone (prepare q w B).depthCap (by rw [zero]; omega)
  exact Nat.lt_succ_iff.mp he

theorem merge_maximal (q w B numerator : ℕ) (i : Fin (prepare q w B).size)
    (hI : (prepare q w B).numerators.read i≤numerator) : i≤(merge (prepare q w B) numerator).label :=
  GeneralPaperFloorSearch.lookup_maximal _ _ _ _ (strict q w B).monotone (prepare q w B).depthCap
    (by rw [zero]; omega) i (by omega)

theorem merge_value_maximal (q w B numerator : ℕ) (i : Fin (prepare q w B).size)
    (hI : (prepare q w B).numerators.read i≤numerator) :
    (prepare q w B).numerators.read i≤(prepare q w B).numerators.read (merge (prepare q w B) numerator).label :=
  (strict q w B).monotone (merge_maximal q w B numerator i hI)

theorem leaf_down (q w B numerator : ℕ) :
    q*(prepare q w B).numerators.read (leaf (prepare q w B) numerator).label≤numerator*denominator w B := by
  have he := GeneralPaperFloorSearch.lookup_value (prepare q w B).leafNumerators (prepare q w B).nonempty
    (prepare q w B).depth (numerator*denominator w B+1) (scaled_mono q w B) (prepare q w B).depthCap (by rw [scaled_zero]; omega)
  rw [scaled_read] at he
  exact Nat.lt_succ_iff.mp he

theorem leaf_maximal (q w B numerator : ℕ) (i : Fin (prepare q w B).size)
    (hI : q*(prepare q w B).numerators.read i≤numerator*denominator w B) : i≤(leaf (prepare q w B) numerator).label :=
  GeneralPaperFloorSearch.lookup_maximal _ _ _ _ (scaled_mono q w B) (prepare q w B).depthCap
    (by rw [scaled_zero]; omega) i (by rw [scaled_read,denominator_spec]; omega)

theorem leaf_value_maximal (q w B numerator : ℕ) (i : Fin (prepare q w B).size)
    (hI : q*(prepare q w B).numerators.read i≤numerator*denominator w B) :
    (prepare q w B).numerators.read i≤(prepare q w B).numerators.read (leaf (prepare q w B) numerator).label :=
  (strict q w B).monotone (leaf_maximal q w B numerator i hI)

theorem merge_zero (q w B : ℕ) : (prepare q w B).numerators.read (merge (prepare q w B) 0).label=0 := by
  have he := merge_down q w B 0
  omega

theorem leaf_zero (q w B : ℕ) (hQ : 0<q) : (prepare q w B).numerators.read (leaf (prepare q w B) 0).label=0 := by
  have he := leaf_down q w B 0
  simp only [Nat.zero_mul] at he
  nlinarith

theorem merge_work {q w B : ℕ} (grid : Prepared q w B) (numerator : ℕ) :
    (merge grid numerator).work≤grid.depth*(12*grid.depth+34)+32 := by
  have he := GeneralPaperFloorSearch.lookup_work grid.numerators grid.nonempty grid.depth (numerator+1)
  change (GeneralPaperFloorSearch.lookup grid.numerators grid.nonempty grid.depth (numerator+1)).work+8≤_
  omega

theorem leaf_work {q w B : ℕ} (grid : Prepared q w B) (numerator : ℕ) :
    (leaf grid numerator).work≤grid.depth*(12*grid.depth+34)+40 := by
  have he := GeneralPaperFloorSearch.lookup_work grid.leafNumerators grid.nonempty grid.depth (numerator*grid.profitDenominator+1)
  change (GeneralPaperFloorSearch.lookup grid.leafNumerators grid.nonempty grid.depth (numerator*grid.profitDenominator+1)).work+16≤_
  omega

end Blotto.GeneralPaperProfitGridRound
