import Blotto.PlayerSpecificRationalRootStages

/-! Whole cached rational-root enumeration price from the original encoded
input. All preparation, queries, traversal, conversions and output copies
refer to the same actual return; no aggregate source/precision oracle. -/
namespace Blotto.PlayerSpecificRationalRootExecutionCost
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalMagnitude PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 300000

theorem traversal_width (p : Data) :
    PlayerSpecificReconstructionTraversalPrice.width p≤PlayerSpecificIntegerBudget.width (inputHeight p) := by
  have hc : PlayerSpecificReconstructionTraversalPrice.widthCoefficient≤4096*PlayerSpecificIntegerBudget.coefficient := by
    unfold PlayerSpecificReconstructionTraversalPrice.widthCoefficient PlayerSpecificIntegerBudget.coefficient
    omega
  have hm:=Nat.mul_le_mul_right (inputHeight p+1) hc
  unfold PlayerSpecificReconstructionTraversalPrice.width PlayerSpecificIntegerBudget.width PlayerSpecificIntegerBudget.height
  nlinarith

theorem initial_width (p : Data) : PlayerSpecificTraversalPrice.width p≤PlayerSpecificIntegerBudget.width (inputHeight p) := by
  have hc : PlayerSpecificTraversalPrice.widthCoefficient≤PlayerSpecificReconstructionTraversalPrice.widthCoefficient := by
    unfold PlayerSpecificTraversalPrice.widthCoefficient PlayerSpecificReconstructionTraversalPrice.widthCoefficient
    omega
  exact (Nat.mul_le_mul_right (inputHeight p+1) hc).trans (traversal_width p)

theorem cast_size (H J m : ℕ) (hm : m=2*H+3) (hH : H≤J) : 64*(1+m)≤256*(J+1) := by omega

theorem combined_price (J R cache initial forest roots cast output word : ℕ)
    (hc : cache≤21000000000*(J+1)*R) (hi : initial≤9000*R)
    (hf : forest≤40000*(J+1)*R) (hr : roots≤80040000*(J+1)*R)
    (hb : cast≤256*(J+1)*R) (ho : output≤15*R) (hw : word≤R) :
    cache+initial+forest+roots+cast+output+32*word≤22000000000*(J+1)*R := by
  nlinarith only [hc,hi,hf,hr,hb,ho,hw]

theorem traversal_coefficient :
    30600*(PlayerSpecificIsolationDepthHeight.linearConstant+26)+5100≤40000*PlayerSpecificIntegerBudget.coefficient := by
  unfold PlayerSpecificIntegerBudget.coefficient
  omega

theorem intervals_length (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificRationalRoots.intervals p).length≤3 := by
  have hc:=PlayerSpecificIsolationBounds.count_bound (prepare p) hp
    (PlayerSpecificRootMagnitude.initial p (prepare p)) (PlayerSpecificRootMagnitude.initial_valid p (prepare p))
  have hf:=PlayerSpecificIsolationForest.length_bound (prepare p) hp (PlayerSpecificReconstructionPrecision.depth p)
    (PlayerSpecificRootMagnitude.initial p (prepare p)) (PlayerSpecificRootMagnitude.initial_valid p (prepare p))
  change (PlayerSpecificRationalRoots.intervals p).length≤_ at hf
  omega

theorem rows_price (J R N cost : ℕ) (hn : N≤3)
    (hc : cost≤20010000*(N+1)*(J+1)*R) : cost≤80040000*(J+1)*R := by
  have hfactor : 20010000*(N+1)≤80040000 := by nlinarith only [hn]
  have hm:=Nat.mul_le_mul_right ((J+1)*R) hfactor
  nlinarith only [hc,hm]

theorem scaled_coefficient (A K H : ℕ) (hc : A≤40000*K) : A*(H+1)≤40000*(K*(H+1)+1) := by
  have hm:=Nat.mul_le_mul_right (H+1) hc
  nlinarith only [hm]

theorem initial_price (model : RationalCostModel) (p : Data) (hlen : p.length≤4) :
    price model (PlayerSpecificRationalRootStages.initial model p).2≤9000*model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)) := by
  have h : price model (PlayerSpecificRationalRootStages.initial model p).2≤9000*model.rat (PlayerSpecificTraversalPrice.width p) := by
    rw [PlayerSpecificRationalRootStages.initial,PlayerSpecificRationalRootStages.magnitude_value]
    exact PlayerSpecificInitialExecution.run_cost model p (PlayerSpecificRationalRootStages.prepared model p) hlen
  exact h.trans (Nat.mul_le_mul_left 9000 (model.monotone (initial_width p)))

theorem forest_price (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    price model (PlayerSpecificRationalRootStages.forest model p).2≤40000*(PlayerSpecificIntegerBudget.height (inputHeight p)+1)*
      model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)) := by
  have ht : price model (PlayerSpecificRationalRootStages.forest model p).2≤
      (30600*(PlayerSpecificIsolationDepthHeight.linearConstant+26)+5100)*(inputHeight p+1)*
        model.rat (PlayerSpecificReconstructionTraversalPrice.width p) := by
    rw [PlayerSpecificRationalRootStages.forest,PlayerSpecificRationalRootStages.depth_value,
      PlayerSpecificRationalRootStages.initial_value,PlayerSpecificRootExecution.prepared_eq (PlayerSpecificRationalRootStages.prepared model p)]
    exact PlayerSpecificReconstructionForestCost.traversal_cost model p hp hlen
  have htp:=ht.trans (Nat.mul_le_mul_left ((30600*(PlayerSpecificIsolationDepthHeight.linearConstant+26)+5100)*(inputHeight p+1))
    (model.monotone (traversal_width p)))
  exact htp.trans (Nat.mul_le_mul_right (model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)))
    (scaled_coefficient _ _ (inputHeight p) traversal_coefficient))

theorem forest_length (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificRationalRootStages.forest model p).1.length≤3 := by
  rw [PlayerSpecificRationalRootStages.forest_value]
  exact intervals_length p hp hlen

theorem enumeration_price (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificRationalRootStages.roots model p).2≤80040000*(PlayerSpecificIntegerBudget.height (inputHeight p)+1)*
      model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)) := by
  have hcap:=forest_length model p hp hlen
  have hnodes : ∀ node∈(PlayerSpecificRationalRootStages.forest model p).1,node∈PlayerSpecificRationalRoots.intervals p := by
    rw [PlayerSpecificRationalRootStages.forest_value]
    intro node hn
    exact hn
  have h:=PlayerSpecificRationalRootRowsCost.run_cost model p hp hlen (PlayerSpecificRationalRootStages.forest model p).1 hcap hnodes
  exact rows_price _ _ _ _ hcap h

theorem output_price (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    price model (copyRow (PlayerSpecificRationalRootStages.roots model p).1)≤15*model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)) :=
  PlayerSpecificRationalRootRowsCost.copy_cost model p hp hlen (PlayerSpecificRationalRootStages.forest model p).1 (forest_length model p hp hlen)

theorem cast_price (model : RationalCostModel) (p : Data) :
    64*(1+binaryWordWidth (PlayerSpecificRationalRootStages.cache model p).isolation.magnitude)≤
      256*(PlayerSpecificIntegerBudget.height (inputHeight p)+1)*model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)) := by
  have hm : binaryWordWidth (PlayerSpecificRationalRootStages.cache model p).isolation.magnitude=2*inputHeight p+3 := by
    rw [PlayerSpecificRationalRootStages.magnitude_value,PlayerSpecificIsolationDepthHeight.root_width]
  have h:=cast_size (inputHeight p) _ _ hm (PlayerSpecificIntegerBudget.input_le _)
  have hW : 1≤PlayerSpecificIntegerBudget.width (inputHeight p) := (by decide : 1≤32).trans (PlayerSpecificIntegerBudget.width_large _)
  have hP:=hW.trans (model.word_le _)
  exact h.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (256*(PlayerSpecificIntegerBudget.height (inputHeight p)+1)) hP)

theorem word_price (model : RationalCostModel) (p : Data) (hlen : p.length≤4) :
    (PlayerSpecificRationalRootStages.cache model p).word≤model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)) :=
  (PlayerSpecificReconstructionCacheBudget.source_word model p hlen).trans (model.word_le _)

theorem run_cost (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificRationalRootExecution.run model p).2≤22000000000*(PlayerSpecificIntegerBudget.height (inputHeight p)+1)*
      model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)) := by
  rw [PlayerSpecificRationalRootExecution.run]
  dsimp only
  exact combined_price (PlayerSpecificIntegerBudget.height (inputHeight p))
    (model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)))
    (PlayerSpecificReconstructionCache.run model p).2
    (price model (PlayerSpecificRationalRootStages.initial model p).2)
    (price model (PlayerSpecificRationalRootStages.forest model p).2)
    (PlayerSpecificRationalRootStages.roots model p).2
    (64*(1+binaryWordWidth (PlayerSpecificRationalRootStages.cache model p).isolation.magnitude))
    (price model (copyRow (PlayerSpecificRationalRootStages.roots model p).1))
    (PlayerSpecificRationalRootStages.cache model p).word
    (PlayerSpecificReconstructionCacheCost.run_cost model p hlen) (initial_price model p hlen)
    (forest_price model p hp hlen) (enumeration_price model p hp hlen) (cast_price model p)
    (output_price model p hp hlen) (word_price model p hlen)

end Blotto.PlayerSpecificRationalRootExecutionCost
