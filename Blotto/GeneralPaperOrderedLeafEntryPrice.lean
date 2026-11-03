import Blotto.GeneralPaperDPTableControls

/-! One leaf candidate borrows its exact tag and typed option predecessor,
and rounds its actual integer profit using the retained grid once. -/
namespace Blotto.GeneralPaperOrderedLeafEntryPrice
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {K q w B : ℕ} (bits : Bool) (price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K) (a : Fin K) :
    Option (Entry Tag (Fin K) grid.size) × ℕ :=
  let rounded := GeneralPaperProfitGridRoundExecution.leaf bits price W grid (field.read a).1
  (some ⟨rounded.1.label,⟨(field.read a).2,a⟩⟩,rounded.2+128*W)

theorem data {K q w B : ℕ} (bits : Bool) (price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K) (a : Fin K) :
    (run bits price W grid field a).1=some (leafEntry grid field a) := by
  simp only [run,GeneralPaperProfitGridRoundExecution.leaf_data,leafEntry]

theorem safe {K q w B : ℕ} (bits : Bool) (price : ℕ → ℕ) (W s : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K) (a : Fin K)
    (h : RationalHeight (field.read a).2.threshold s) :
    GeneralPaperOrderedTableHeight.OptionalSafe s (run bits price W grid field a).1 := by
  rw [data]
  intro e he
  cases Option.some.inj he
  exact h

theorem bit_work {K : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (field : Field Tag K) (a : Fin K) (hNum : (field.read a).1≤2*prepared.parameters.qProf) :
    (run true price W prepared.grid field a).2≤GeneralPaperCachedProfitGridPrice.profile price W m lambda k Qv+128*W := by
  subst prepared
  exact Nat.add_le_add_right (GeneralPaperCachedProfitGridPrice.leaf_work price hMono W m lambda k Qv _ rfl _ rfl _ hNum) _

theorem arithmetic_work {K q w B : ℕ} (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (field : Field Tag K) (a : Fin K) :
    (run false (fun _ => 1) 1 grid field a).2≤512*(grid.depth+1)^2+336 := by
  have h := GeneralPaperProfitGridRoundExecution.leaf_arithmetic_work grid (field.read a).1
  change (GeneralPaperProfitGridRoundExecution.leaf false (fun _ => 1) 1 grid (field.read a).1).2+128≤_
  omega

end Blotto.GeneralPaperOrderedLeafEntryPrice
