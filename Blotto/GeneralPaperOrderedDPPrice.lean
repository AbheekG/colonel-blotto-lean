import Blotto.GeneralPaperOrderedDPProfitCaps

/-! Complete recursive arithmetic/bit prices for the actual retained DP
computation. Per-level resource words remain in the bit profile; only the
actual leaf tags and source profits supply its invariants. -/
namespace Blotto.GeneralPaperOrderedDPPrice
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000

def bitProfile (price : ℕ → ℕ) (W m lambda k Qv K J s : ℕ) : ℕ → ℕ
  | 0 => GeneralPaperOrderedTablePrice.leafProfile price W m lambda k Qv K J s+128*W
  | h+1 => 2*bitProfile price W m lambda k Qv K J s h+
    GeneralPaperOrderedTablePrice.mergeProfile price W m lambda k Qv J s h+128*W

def arithmeticProfile (K J depth : ℕ) : ℕ → ℕ
  | 0 => GeneralPaperOrderedTableArithmetic.leafProfile K J depth+128
  | h+1 => 2*arithmeticProfile K J depth h+GeneralPaperOrderedTableArithmetic.mergeProfile J depth+128

theorem bit_work {K h : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv s : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (tree : Tree Tag K h) (hl : GeneralPaperOrderedDPHeight.Leaves s tree)
    (hNum : GeneralPaperOrderedDPProfitCaps.Leaves (2*prepared.parameters.qProf) tree) :
    (GeneralPaperOrderedDPExecution.run true (fun x => x) price W prepared.grid tree).2≤
      bitProfile price W m lambda k Qv K prepared.grid.size s h := by
  induction tree with
  | leaf field =>
    have hw := GeneralPaperOrderedTablePrice.leaf_work price hMono W m lambda k Qv s prepared hp field hl hNum
    change (GeneralPaperOrderedTableExecution.leaf true (fun x => x) price W prepared.grid field).2+128*W≤_
    exact Nat.add_le_add_right hw _
  | @node h left right ihl ihr =>
    have hLeft := ihl hl.1 hNum.1
    have hRight := ihr hl.2 hNum.2
    have hsLeft := GeneralPaperOrderedDPExecution.states true (fun x => x) price W s prepared.grid left hl.1
    have hsRight := GeneralPaperOrderedDPExecution.states true (fun x => x) price W s prepared.grid right hl.2
    have hm := GeneralPaperOrderedTablePrice.merge_work price hMono W m lambda k Qv s h prepared hp
      (GeneralPaperOrderedDPExecution.run true (fun x => x) price W prepared.grid left).1.table
      (GeneralPaperOrderedDPExecution.run true (fun x => x) price W prepared.grid right).1.table hsLeft hsRight
    change (GeneralPaperOrderedDPExecution.run true (fun x => x) price W prepared.grid left).2+
      (GeneralPaperOrderedDPExecution.run true (fun x => x) price W prepared.grid right).2+
      (GeneralPaperOrderedTableExecution.merge true (fun x => x) price W prepared.grid
        (GeneralPaperOrderedDPExecution.run true (fun x => x) price W prepared.grid left).1.table
        (GeneralPaperOrderedDPExecution.run true (fun x => x) price W prepared.grid right).1.table).2+128*W≤_
    rw [bitProfile]
    nlinarith only [hLeft,hRight,hm]

theorem arithmetic_work {K q w B h : ℕ} (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) :
    (GeneralPaperOrderedDPExecution.run false (fun _ => 1) (fun _ => 1) 1 grid tree).2≤arithmeticProfile K grid.size grid.depth h := by
  induction tree with
  | leaf field =>
    have hw := GeneralPaperOrderedTableArithmetic.leaf_work grid field
    change (GeneralPaperOrderedTableExecution.leaf false (fun _ => 1) (fun _ => 1) 1 grid field).2+128≤_
    exact Nat.add_le_add_right hw _
  | @node h left right ihl ihr =>
    have hm := GeneralPaperOrderedTableArithmetic.merge_work grid
      (GeneralPaperOrderedDPExecution.run false (fun _ => 1) (fun _ => 1) 1 grid left).1.table
      (GeneralPaperOrderedDPExecution.run false (fun _ => 1) (fun _ => 1) 1 grid right).1.table
    change (GeneralPaperOrderedDPExecution.run false (fun _ => 1) (fun _ => 1) 1 grid left).2+
      (GeneralPaperOrderedDPExecution.run false (fun _ => 1) (fun _ => 1) 1 grid right).2+
      (GeneralPaperOrderedTableExecution.merge false (fun _ => 1) (fun _ => 1) 1 grid
        (GeneralPaperOrderedDPExecution.run false (fun _ => 1) (fun _ => 1) 1 grid left).1.table
        (GeneralPaperOrderedDPExecution.run false (fun _ => 1) (fun _ => 1) 1 grid right).1.table).2+128≤_
    rw [arithmeticProfile]
    nlinarith only [ihl,ihr,hm]

theorem arithmetic_exact (K J depth h : ℕ) :
    arithmeticProfile K J depth h+(GeneralPaperOrderedTableArithmetic.mergeProfile J depth+128)=
      2^h*(GeneralPaperOrderedTableArithmetic.leafProfile K J depth+
        GeneralPaperOrderedTableArithmetic.mergeProfile J depth+256) := by
  induction h with
  | zero => rw [arithmeticProfile,pow_zero,one_mul]; omega
  | succ h ih => rw [arithmeticProfile,pow_succ]; nlinarith only [ih]

theorem native_work {m k : ℕ} (model : RationalCostModel) (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k))
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows) (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m ready.alphabet.lambda k Qv (prefixes.read j)) :
    let tree := GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached
    let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
    (GeneralPaperOrderedDPExecution.run true (fun x => x) model.rat W prepared.grid tree).2≤
      bitProfile model.rat W m ready.alphabet.lambda k Qv K prepared.grid.size (ready.alphabet.lambda+1) prepared.parameters.height ∧
    (GeneralPaperOrderedDPExecution.run false (fun _ => 1) (fun _ => 1) 1 prepared.grid tree).2≤
      arithmeticProfile K prepared.grid.size prepared.grid.depth prepared.parameters.height :=
  ⟨bit_work model.rat model.monotone W m ready.alphabet.lambda k Qv _ prepared hp _
    (GeneralPaperOrderedDPHeight.native_tree prepared T ready weights prefixes)
    (GeneralPaperOrderedDPProfitCaps.native_tree Qv T prepared ready weights prefixes hp hT hWeights hGood),
    arithmetic_work prepared.grid _⟩

end Blotto.GeneralPaperOrderedDPPrice
