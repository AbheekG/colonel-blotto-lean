import Blotto.GeneralPaperFloorSearchStorage

/-! Native profit-grid leaf scaling and merge strict cuts retain all
integer temporaries, floor results and work additions. No resource-tag word
or grid reconstruction is hidden in these integer-only callback bounds. -/
namespace Blotto.GeneralPaperProfitGridQueryStorage
open GeneralPaperEncodedScalarStorage GeneralPaperRankOperands
open GeneralPaperProfitGridPrepare
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem floor_work {n : ℕ} (model : RationalCostModel) (W depth : ℕ) (values : FixedArrayTable n ℕ) (hn : 0<n) (cut : ℕ)
    (hs : n<2^depth) :
    (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.work≤depth*(12*depth+34)+24 := by
  rw [GeneralPaperFloorSearchPrice.data true model.rat W depth values hn cut hs]
  exact GeneralPaperFloorSearch.lookup_work values hn depth cut

theorem tagged_result {n : ℕ} (model : RationalCostModel) (W depth V : ℕ) (values : FixedArrayTable n ℕ) (hn : 0<n)
    (cut extra : ℕ) (hs : n<2^depth) (he : extra≤16) :
    GeneralPaperFloorSearchStorage.resultBits W
      ⟨(GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.label,
        (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.work+extra⟩≤2*width depth V+64*W := by
  have hi := (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.label.isLt
  have hw := floor_work model W depth values hn cut hs
  have hcap : depth*(12*depth+34)+40≤64*(depth+1)^2 := by nlinarith only [Nat.zero_le depth]
  have hb := basic n depth V
  have hword := word_bound n depth V hs
  have hl := (Nat.add_le_add_left (binaryWordWidth_mono (show
    (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.label.val≤magnitude n depth V by omega)) 1).trans hword
  have hw' := (Nat.add_le_add_left (binaryWordWidth_mono (show
    (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.work+extra≤magnitude n depth V by omega)) 1).trans hword
  dsimp only [GeneralPaperFloorSearchStorage.resultBits]
  unfold natBits
  omega

def leafControls {q w B : ℕ} (model : RationalCostModel) (W : ℕ) (grid : Prepared q w B) (num : ℕ) : ℕ :=
  let r := (GeneralPaperFloorSearchPrice.run true model.rat W grid.depth grid.leafNumerators grid.nonempty (num*grid.profitDenominator+1)).1
  fields W [grid.size,grid.depth,num,grid.profitDenominator,num*grid.profitDenominator,num*grid.profitDenominator+1,r.work,r.work+16,16,1]

theorem leaf_controls {q w B : ℕ} (model : RationalCostModel) (W V : ℕ) (grid : Prepared q w B) (num : ℕ)
    (hn : num≤V) (hd : grid.profitDenominator≤V) (hc : num*grid.profitDenominator+1≤V) :
    leafControls model W grid num≤10*(width grid.depth V+W)+32*W := by
  let r := (GeneralPaperFloorSearchPrice.run true model.rat W grid.depth grid.leafNumerators grid.nonempty (num*grid.profitDenominator+1)).1
  have hw := floor_work model W grid.depth grid.leafNumerators grid.nonempty (num*grid.profitDenominator+1) grid.depthCap
  change r.work≤_ at hw
  have hcap : grid.depth*(12*grid.depth+34)+40≤64*(grid.depth+1)^2 := by nlinarith only [Nat.zero_le grid.depth]
  have hb := basic grid.size grid.depth V
  have hword := word_bound grid.size grid.depth V grid.depthCap
  dsimp only [leafControls]
  change fields W [grid.size,grid.depth,num,grid.profitDenominator,num*grid.profitDenominator,num*grid.profitDenominator+1,r.work,r.work+16,16,1]≤_
  apply fields_bound
  intro x hx
  apply (Nat.add_le_add_left (binaryWordWidth_mono (show x≤magnitude grid.size grid.depth V from ?_)) 1).trans hword
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx
  all_goals (rw [hx]; omega)

def mergeControls {q w B : ℕ} (model : RationalCostModel) (W : ℕ) (grid : Prepared q w B) (num : ℕ) : ℕ :=
  let r := (GeneralPaperFloorSearchPrice.run true model.rat W grid.depth grid.numerators grid.nonempty (num+1)).1
  fields W [grid.size,grid.depth,num,num+1,r.work,r.work+8,8,1]

theorem merge_controls {q w B : ℕ} (model : RationalCostModel) (W V : ℕ) (grid : Prepared q w B) (num : ℕ) (hc : num+1≤V) :
    mergeControls model W grid num≤8*(width grid.depth V+W)+32*W := by
  let r := (GeneralPaperFloorSearchPrice.run true model.rat W grid.depth grid.numerators grid.nonempty (num+1)).1
  have hw := floor_work model W grid.depth grid.numerators grid.nonempty (num+1) grid.depthCap
  change r.work≤_ at hw
  have hcap : grid.depth*(12*grid.depth+34)+40≤64*(grid.depth+1)^2 := by nlinarith only [Nat.zero_le grid.depth]
  have hb := basic grid.size grid.depth V
  have hword := word_bound grid.size grid.depth V grid.depthCap
  dsimp only [mergeControls]
  change fields W [grid.size,grid.depth,num,num+1,r.work,r.work+8,8,1]≤_
  apply fields_bound
  intro x hx
  apply (Nat.add_le_add_left (binaryWordWidth_mono (show x≤magnitude grid.size grid.depth V from ?_)) 1).trans hword
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx|hx|hx|hx|hx
  all_goals (rw [hx]; omega)

def leafWindow {q w B : ℕ} (model : RationalCostModel) (W : ℕ) (grid : Prepared q w B) (num : ℕ) : ℕ :=
  GeneralPaperFloorSearchStorage.window model W grid.depth grid.leafNumerators grid.nonempty (num*grid.profitDenominator+1)+
    GeneralPaperFloorSearchStorage.resultBits W (GeneralPaperProfitGridRoundExecution.leaf true model.rat W grid num).1+
    leafControls model W grid num+(GeneralPaperProfitGridRoundExecution.leaf true model.rat W grid num).2+256*W

def mergeWindow {q w B : ℕ} (model : RationalCostModel) (W : ℕ) (grid : Prepared q w B) (num : ℕ) : ℕ :=
  GeneralPaperFloorSearchStorage.window model W grid.depth grid.numerators grid.nonempty (num+1)+
    GeneralPaperFloorSearchStorage.resultBits W (GeneralPaperProfitGridRoundExecution.merge true model.rat W grid num).1+
    mergeControls model W grid num+(GeneralPaperProfitGridRoundExecution.merge true model.rat W grid num).2+256*W

def profile (model : RationalCostModel) (W depth V : ℕ) : ℕ :=
  GeneralPaperFloorSearchStorage.profile model W depth V+(2*width depth V+64*W)+
    (10*(width depth V+W)+32*W)+GeneralPaperProfitGridRoundPrice.profile model.rat W depth V+256*W

theorem leaf_bounded {q w B : ℕ} (model : RationalCostModel) (W V : ℕ) (grid : Prepared q w B) (num : ℕ)
    (hn : num≤V) (hd : grid.profitDenominator≤V) (hc : num*grid.profitDenominator+1≤V) (hv : ∀ i,grid.leafNumerators.read i≤V) :
    leafWindow model W grid num≤profile model W grid.depth V := by
  have hf := GeneralPaperFloorSearchStorage.bounded model W grid.depth V grid.leafNumerators grid.nonempty
    (num*grid.profitDenominator+1) grid.depthCap hc hv
  have hr := tagged_result model W grid.depth V grid.leafNumerators grid.nonempty (num*grid.profitDenominator+1) 16 grid.depthCap (Nat.le_refl _)
  change GeneralPaperFloorSearchStorage.resultBits W (GeneralPaperProfitGridRoundExecution.leaf true model.rat W grid num).1≤_ at hr
  have hcontrols := leaf_controls model W V grid num hn hd hc
  have hp := GeneralPaperProfitGridRoundPrice.leaf_work model.rat model.monotone W V grid num hn hd hc hv
  unfold leafWindow profile
  omega

theorem merge_bounded {q w B : ℕ} (model : RationalCostModel) (W V : ℕ) (grid : Prepared q w B) (num : ℕ)
    (hc : num+1≤V) (hv : ∀ i,grid.numerators.read i≤V) : mergeWindow model W grid num≤profile model W grid.depth V := by
  have hf := GeneralPaperFloorSearchStorage.bounded model W grid.depth V grid.numerators grid.nonempty (num+1) grid.depthCap hc hv
  have hr := tagged_result model W grid.depth V grid.numerators grid.nonempty (num+1) 8 grid.depthCap (by omega)
  change GeneralPaperFloorSearchStorage.resultBits W (GeneralPaperProfitGridRoundExecution.merge true model.rat W grid num).1≤_ at hr
  have hcontrols := merge_controls model W V grid num hc
  have hp := GeneralPaperProfitGridRoundPrice.merge_work model.rat model.monotone W V grid num hc hv
  unfold mergeWindow profile
  omega

def compact (model : RationalCostModel) (W depth L : ℕ) : ℕ := 32768*(depth+1)*(W+L+model.rat L)

theorem profile_compact (model : RationalCostModel) (W depth V L : ℕ) (hw : width depth V≤L) :
    profile model W depth V≤compact model W depth L := by
  have hp := model.monotone hw
  have hs := Nat.mul_le_mul_left (depth+1) (Nat.add_le_add hw hp)
  have hf := Nat.mul_le_mul_left (depth+1) hw
  have hpr := Nat.mul_le_mul_left (depth+1) hp
  unfold profile GeneralPaperFloorSearchStorage.profile GeneralPaperProfitGridRoundPrice.profile compact
  dsimp only
  nlinarith only [hw,hp,hs,hf,hpr,Nat.zero_le (depth*W),Nat.zero_le (depth*L),Nat.zero_le (depth*model.rat L)]

end Blotto.GeneralPaperProfitGridQueryStorage
