import Blotto.GeneralPaperOrderedScatterArithmetic

/-! Actual empty-table construction and reusable index lists. The latter
are shared between merge rows/columns. Both indexed constructors price
their controls and every prefix, with W still supplied by the global caller. -/
namespace Blotto.GeneralPaperDPTableControls
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def empty (Witness : Type*) (index : ℕ → ℕ) (W A J : ℕ) : Table Tag Witness J × ℕ :=
  let filled := PaperIndexedArrayConstruction.run index A (fun _ : Fin J => ((none:Option (Selection Tag Witness)),64*W))
  (filled.1,filled.2+64*W)

def labels (index : ℕ → ℕ) (W A n : ℕ) : List (Fin n) × ℕ :=
  GeneralPaperIndexedListPrice.run index A (fun i : Fin n => (i,64*W))

theorem empty_data (Witness : Type*) (index : ℕ → ℕ) (W A J : ℕ) :
    (empty Witness index W A J).1=GeneralPaperOrderedProfitScatter.empty Witness J := by
  simp only [empty,PaperIndexedArrayConstruction.run_data,GeneralPaperOrderedProfitScatter.empty]

theorem labels_data (index : ℕ → ℕ) (W A n : ℕ) : (labels index W A n).1=List.finRange n := by
  simp only [labels,GeneralPaperIndexedListPrice.data,List.finRange]

def emptyProfile (W J : ℕ) : ℕ := 64*J*W+44*(J+1)*arrayWord W J+64*W
def labelsProfile (W n : ℕ) : ℕ := n*(64*W+72*arrayWord W (n+2))+18*arrayWord W (n+2)

theorem empty_bit_work (Witness : Type*) (W J : ℕ) :
    (empty Witness (fun x => x) W (arrayWord W J) J).2≤emptyProfile W J := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun x => x) (arrayWord W J) (64*W)
    (fun _ : Fin J => ((none:Option (Selection Tag Witness)),64*W))
    (GeneralPaperSummaryArrayControls.array_word_positive W J) (GeneralPaperSummaryArrayControls.array_index W J)
    (fun _ => Nat.le_refl _)
  change (PaperIndexedArrayConstruction.run (fun x => x) (arrayWord W J)
    (fun _ : Fin J => ((none:Option (Selection Tag Witness)),64*W))).2+64*W≤_
  unfold emptyProfile
  nlinarith only [h]

theorem labels_bit_work (W n : ℕ) :
    (labels (fun x => x) W (arrayWord W (n+2)) n).2≤labelsProfile W n := by
  apply GeneralPaperIndexedListPrice.work (fun x => x) (arrayWord W (n+2)) (64*W) _
    (GeneralPaperSummaryArrayControls.array_word_positive W (n+2))
  · intro r hr
    have hw := binaryWordWidth_mono (show r+1≤(n+2)+1 by omega)
    unfold arrayWord
    omega
  · intro i
    exact Nat.le_refl _

theorem empty_arithmetic_work (Witness : Type*) (J : ℕ) :
    (empty Witness (fun _ => 1) 1 1 J).2≤64*J+44*(J+1)+64 := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 64
    (fun _ : Fin J => ((none:Option (Selection Tag Witness)),64)) (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1
    (fun _ : Fin J => ((none:Option (Selection Tag Witness)),64))).2+64≤_
  nlinarith only [h]

theorem labels_arithmetic_work (n : ℕ) : (labels (fun _ => 1) 1 1 n).2≤136*n+18 := by
  have h := GeneralPaperIndexedListPrice.work (fun _ => 1) 1 64 (fun i : Fin n => (i,64))
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  change (GeneralPaperIndexedListPrice.run (fun _ => 1) 1 (fun i : Fin n => (i,64))).2≤_
  nlinarith only [h]

theorem empty_prefix (Witness : Type*) (index : ℕ → ℕ) (W A J count : ℕ) (hc : count≤J) :
    (PaperIndexedArrayConstruction.fill index A (fun _ : Fin J => ((none:Option (Selection Tag Witness)),64*W)) count hc).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperDPTableControls
