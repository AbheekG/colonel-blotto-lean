import Blotto.GeneralPaperActualEpochCacheConstructionStorage

/-! The native floor callback retains its complete rank/floor results,
subtraction/clamping controls and selected rank stack. Prepared arrays are
borrowed; complete primitive scratch is charged without another traversal. -/
namespace Blotto.GeneralPaperFloorSearchStorage
open GeneralPaperEncodedScalarStorage GeneralPaperRankOperands
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def resultBits {n : ℕ} (W : ℕ) (r : GeneralPaperFloorSearch.Result n) : ℕ := natBits r.label.val+natBits r.work+64*W

theorem result_bound {n : ℕ} (model : RationalCostModel) (W depth V : ℕ) (values : FixedArrayTable n ℕ)
    (hn : 0<n) (cut : ℕ) (hs : n<2^depth) :
    resultBits W (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1≤2*width depth V+64*W := by
  have hi := (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.label.isLt
  have hw : (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.work≤depth*(12*depth+34)+24 := by
    rw [GeneralPaperFloorSearchPrice.data true model.rat W depth values hn cut hs]
    exact GeneralPaperFloorSearch.lookup_work values hn depth cut
  have hwork : depth*(12*depth+34)+24≤64*(depth+1)^2 := by nlinarith only [Nat.zero_le depth]
  have hb := basic n depth V
  have hword := word_bound n depth V hs
  have hl := (Nat.add_le_add_left (binaryWordWidth_mono (show
    (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.label.val≤magnitude n depth V by omega)) 1).trans hword
  have hw' := (Nat.add_le_add_left (binaryWordWidth_mono (show
    (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.work≤magnitude n depth V by omega)) 1).trans hword
  change natBits (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.label.val≤width depth V at hl
  change natBits (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1.work≤width depth V at hw'
  unfold resultBits
  omega

def controls {n : ℕ} (model : RationalCostModel) (W depth : ℕ) (values : FixedArrayTable n ℕ) (cut : ℕ) : ℕ :=
  let r := (GeneralPaperRankLookupPrice.run true model.rat W depth values cut).1
  fields W [n,cut,depth,r.position.val,r.position.val-1,n-1,min (r.position.val-1) (n-1),r.work,r.work+8,8,1]

theorem controls_bound {n : ℕ} (model : RationalCostModel) (W depth V : ℕ) (values : FixedArrayTable n ℕ) (cut : ℕ)
    (hs : n<2^depth) (hc : cut≤V) : controls model W depth values cut≤11*(width depth V+W)+32*W := by
  let r := (GeneralPaperRankLookupPrice.run true model.rat W depth values cut).1
  have hi : r.position.val≤n := Nat.le_of_lt_succ r.position.isLt
  have hw : r.work≤depth*(12*depth+34)+16 := by
    dsimp only [r]
    rw [GeneralPaperRankLookupPrice.data true model.rat W depth values cut hs]
    exact Nat.add_le_add_right (GeneralPaperRankSearch.run_work values cut depth depth 0 n) 8
  have hwork : depth*(12*depth+34)+24≤64*(depth+1)^2 := by nlinarith only [Nat.zero_le depth]
  have hb := basic n depth V
  have hword := word_bound n depth V hs
  dsimp only [controls]
  change fields W [n,cut,depth,r.position.val,r.position.val-1,n-1,min (r.position.val-1) (n-1),r.work,r.work+8,8,1]≤_
  apply fields_bound
  intro x hx
  apply (Nat.add_le_add_left (binaryWordWidth_mono (show x≤magnitude n depth V from ?_)) 1).trans hword
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx
  all_goals (rw [hx]; omega)

def window {n : ℕ} (model : RationalCostModel) (W depth : ℕ) (values : FixedArrayTable n ℕ) (hn : 0<n) (cut : ℕ) : ℕ :=
  GeneralPaperRankTraversalStorage.window model W depth values cut+
    GeneralPaperRankTraversalStorage.lookupBits W (GeneralPaperRankLookupPrice.run true model.rat W depth values cut).1+
    resultBits W (GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).1+
    controls model W depth values cut+(GeneralPaperFloorSearchPrice.run true model.rat W depth values hn cut).2+256*W

def profile (model : RationalCostModel) (W depth V : ℕ) : ℕ :=
  let L := width depth V
  ((depth+1)*(32*L+512*W)+3*L+64*W+1024*(depth+1)*(W+model.rat L)+256*W)+
    (3*L+64*W)+(2*L+64*W)+(11*(L+W)+32*W)+2048*(depth+1)*(W+model.rat L)+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W depth V : ℕ) (values : FixedArrayTable n ℕ) (hn : 0<n) (cut : ℕ)
    (hs : n<2^depth) (hc : cut≤V) (hv : ∀ i,values.read i≤V) : window model W depth values hn cut≤profile model W depth V := by
  have hstack := GeneralPaperRankTraversalStorage.query model W depth V values cut hs hc hv
  have hr := GeneralPaperRankTraversalStorage.lookup_bound true model.rat W depth V values cut hs
  have hout := result_bound model W depth V values hn cut hs
  have hcontrols := controls_bound model W depth V values cut hs hc
  have hp := GeneralPaperFloorSearchPrice.bit_work model.rat model.monotone W depth V values hn cut hs hc hv
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperFloorSearchStorage
