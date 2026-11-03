import Blotto.GeneralPaperOrderedRootExecution

/-! Complete native DP/root/backtracking prices. The global reference word
and actual budget rational word stay explicit. Native-call prices also
reserve construction of the literal closed budget tag once. -/
namespace Blotto.GeneralPaperOrderedRootPrice
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP
open GeneralPaperSummaryArrayExecution (arrayWord)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem compose {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W D S R : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag)
    (hd : (GeneralPaperOrderedDPExecution.run bits index price W grid tree).2≤D)
    (hs : (GeneralPaperRootSelectPrice.run bits index price W
      (GeneralPaperOrderedDPExecution.run bits index price W grid tree).1.table budget).2≤S)
    (hr : ∀ label,(GeneralPaperTypedDecodeExecution.run (if bits then arrayWord W (max K grid.size+2) else W)
      (GeneralPaperOrderedDPExecution.run bits index price W grid tree).1 label).2≤R) :
    (GeneralPaperOrderedRootExecution.run bits index price W grid tree budget).2≤D+S+R+128*W := by
  cases hSelected : (GeneralPaperRootSelectPrice.run bits index price W
    (GeneralPaperOrderedDPExecution.run bits index price W grid tree).1.table budget).1 with
  | none => simp only [GeneralPaperOrderedRootExecution.run,hSelected]; omega
  | some label =>
    have h := hr label
    simp only [GeneralPaperOrderedRootExecution.run,hSelected]
    omega

def profile (model : RationalCostModel) (W m lambda k Qv K J s h budgetWord : ℕ) : ℕ :=
  GeneralPaperOrderedDPAggregatePrice.profile model W m lambda k Qv K J s h+
    GeneralPaperRootSelectPrice.profile model.rat W J (expressionHeightBudget s h) budgetWord+
    256*2^h*(h+1)*arrayWord W (max K J+2)+128*W

def arithmeticProfile (K J depth h : ℕ) : ℕ :=
  GeneralPaperOrderedDPPrice.arithmeticProfile K J depth h+(459*J+210)+256*2^h*(h+1)+128

theorem work {K h : ℕ} (model : RationalCostModel) (W m lambda k Qv s : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (tree : Tree Tag K h) (budget : Tag) (hl : GeneralPaperOrderedDPHeight.Leaves s tree)
    (hNum : GeneralPaperOrderedDPProfitCaps.Leaves (2*prepared.parameters.qProf) tree) :
    (GeneralPaperOrderedRootExecution.run true (fun x => x) model.rat W prepared.grid tree budget).2≤
      profile model W m lambda k Qv K prepared.grid.size s h (rationalWordWidth budget.threshold) := by
  have hd := GeneralPaperOrderedDPAggregatePrice.work model W m lambda k Qv s prepared hp tree hl hNum
  have hs := GeneralPaperRootSelectPrice.work model.rat model.monotone W (expressionHeightBudget s h)
    (GeneralPaperOrderedDPExecution.run true (fun x => x) model.rat W prepared.grid tree).1.table budget
    (GeneralPaperOrderedDPExecution.states true (fun x => x) model.rat W s prepared.grid tree hl)
  have hr := fun label => GeneralPaperTypedDecodePrice.work (arrayWord W (max K prepared.grid.size+2))
    (GeneralPaperOrderedDPExecution.run true (fun x => x) model.rat W prepared.grid tree).1 label
  exact compose true (fun x => x) model.rat W _ _ _ prepared.grid tree budget hd hs hr

theorem arithmetic_work {K q w B h : ℕ} (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag) :
    (GeneralPaperOrderedRootExecution.run false (fun _ => 1) (fun _ => 1) 1 grid tree budget).2≤arithmeticProfile K grid.size grid.depth h := by
  have hd := GeneralPaperOrderedDPPrice.arithmetic_work grid tree
  have hs := GeneralPaperRootSelectPrice.arithmetic_work
    (GeneralPaperOrderedDPExecution.run false (fun _ => 1) (fun _ => 1) 1 grid tree).1.table budget
  have hr := fun label => GeneralPaperTypedDecodePrice.work 1
    (GeneralPaperOrderedDPExecution.run false (fun _ => 1) (fun _ => 1) 1 grid tree).1 label
  simpa only [arithmeticProfile,Nat.mul_one] using
    compose false (fun _ => 1) (fun _ => 1) 1 _ _ _ grid tree budget hd hs hr

theorem native_work {m k : ℕ} (model : RationalCostModel) (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) (B : ℚ)
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows) (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m ready.alphabet.lambda k Qv (prefixes.read j)) :
    let tree := GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached
    let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
    (GeneralPaperOrderedRootExecution.run true (fun x => x) model.rat W prepared.grid tree (budget B)).2+64*W≤
      profile model W m ready.alphabet.lambda k Qv K prepared.grid.size (ready.alphabet.lambda+1) prepared.parameters.height (rationalWordWidth B)+64*W ∧
    (GeneralPaperOrderedRootExecution.run false (fun _ => 1) (fun _ => 1) 1 prepared.grid tree (budget B)).2+64≤
      arithmeticProfile K prepared.grid.size prepared.grid.depth prepared.parameters.height+64 :=
  ⟨Nat.add_le_add_right (work model W m ready.alphabet.lambda k Qv _ prepared hp _ (budget B)
      (GeneralPaperOrderedDPHeight.native_tree prepared T ready weights prefixes)
      (GeneralPaperOrderedDPProfitCaps.native_tree Qv T prepared ready weights prefixes hp hT hWeights hGood)) _,
    Nat.add_le_add_right (arithmetic_work prepared.grid _ (budget B)) _⟩

end Blotto.GeneralPaperOrderedRootPrice
