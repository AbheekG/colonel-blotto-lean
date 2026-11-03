import Blotto.GeneralPaperRootReturnedRows

/-! The literal catalogue zero fallback is materialized once, including
its full indexed fill and descriptor. Pricing it unconditionally also
covers a strict evaluation of getD's default argument on successful calls. -/
namespace Blotto.GeneralPaperZeroRowPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run (bits : Bool) (index : ℕ → ℕ) (W m k : ℕ) :
    FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) × ℕ :=
  let filled := PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W)
    (fun _ : Fin m => ((0:Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)),64*W))
  (filled.1,filled.2+64*W)

theorem data (bits : Bool) (index : ℕ → ℕ) (W m k : ℕ) :
    (run bits index W m k).1=GeneralPaperCatalogueOptimizer.zeroRow m k := by
  simp only [run,PaperIndexedArrayConstruction.run_data,GeneralPaperCatalogueOptimizer.zeroRow]

def profile (W m : ℕ) : ℕ := 64*m*W+44*(m+1)*arrayWord W m+64*W

theorem work (W m k : ℕ) : (run true (fun x => x) W m k).2≤profile W m := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun x => x) (arrayWord W m) (64*W)
    (fun _ : Fin m => ((0:Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)),64*W))
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
    (fun _ => Nat.le_refl _)
  change (PaperIndexedArrayConstruction.run (fun x => x) (arrayWord W m)
    (fun _ : Fin m => ((0:Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)),64*W))).2+64*W≤_
  unfold profile
  nlinarith only [h]

theorem arithmetic_work (m k : ℕ) : (run false (fun _ => 1) 1 m k).2≤108*m+108 := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 64
    (fun _ : Fin m => ((0:Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)),64))
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1
    (fun _ : Fin m => ((0:Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)),64))).2+64≤_
  nlinarith only [h]

end Blotto.GeneralPaperZeroRowPrice
