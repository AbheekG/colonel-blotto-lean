import Blotto.PlayerSpecificFlatCoinBlocks

/-! Exact whole-continuation expectations of the executing resource loop.
The first H-bit block and remaining packet are the actual flat blocks;
later requests, probabilities and state updates may depend on the branch. -/
namespace Blotto.PlayerSpecificResourceExpectation
open MeasureTheory
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def mean {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H C : ℕ) (s : State N) (f : State N → ℝ) : ℝ :=
  ∫ bits,f (PlayerSpecificFiniteResourceLoop.run model p H C s (PlayerSpecificFiniteResourceLoop.blocks C H bits)).1
    ∂(fairBitLaw (C*H) : Measure (Fin (C*H) → Bool))

theorem zero {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H : ℕ) (s : State N) (f : State N → ℝ) : mean model p H 0 s f=f s := by
  simp only [mean,PlayerSpecificFiniteResourceLoop.run,integral_const,probReal_univ,one_smul]

theorem stopped {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H C : ℕ) (s : State N) (f : State N → ℝ) (hs : request model p s=none) : mean model p H C s f=f s := by
  cases C <;> simp only [mean,PlayerSpecificFiniteResourceLoop.run,hs,integral_const,probReal_univ,one_smul]

theorem step {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H C : ℕ) (s : State N) (frame : Frame N) (hf : request model p s=some frame) (f : State N → ℝ) :
    mean model p H (C+1) s f=
      PlayerSpecificAlgebraicMidpointCoin.success model p.parameters.root frame.pair.probability H*
        mean model p H C (advance model p s frame true) f+
      (1-PlayerSpecificAlgebraicMidpointCoin.success model p.parameters.root frame.pair.probability H)*
        mean model p H C (advance model p s frame false) f := by
  have he : ∀ bits : Fin ((C+1)*H) → Bool,
      f (PlayerSpecificFiniteResourceLoop.run model p H (C+1) s (PlayerSpecificFiniteResourceLoop.blocks (C+1) H bits)).1=
        if PlayerSpecificAlgebraicMidpointCoin.run model p.parameters.root frame.pair.probability H
            (PlayerSpecificFlatCoinBlocks.headBits C H bits)
          then f (PlayerSpecificFiniteResourceLoop.run model p H C (advance model p s frame true)
            (PlayerSpecificFiniteResourceLoop.blocks C H (PlayerSpecificFlatCoinBlocks.restBits C H bits))).1
          else f (PlayerSpecificFiniteResourceLoop.run model p H C (advance model p s frame false)
            (PlayerSpecificFiniteResourceLoop.blocks C H (PlayerSpecificFlatCoinBlocks.restBits C H bits))).1 := by
    intro bits
    rw [PlayerSpecificFlatCoinBlocks.blocks_cons,PlayerSpecificFiniteResourceLoop.run,hf]
    simp only [List.headD_cons,List.tail_cons]
    cases PlayerSpecificAlgebraicMidpointCoin.run model p.parameters.root frame.pair.probability H
      (PlayerSpecificFlatCoinBlocks.headBits C H bits) <;> rfl
  unfold mean
  simp_rw [he]
  exact PlayerSpecificFlatCoinBlocks.binary_continuation C H
    (PlayerSpecificAlgebraicMidpointCoin.run model p.parameters.root frame.pair.probability H)
    (fun bits => f (PlayerSpecificFiniteResourceLoop.run model p H C (advance model p s frame true)
      (PlayerSpecificFiniteResourceLoop.blocks C H bits)).1)
    (fun bits => f (PlayerSpecificFiniteResourceLoop.run model p H C (advance model p s frame false)
      (PlayerSpecificFiniteResourceLoop.blocks C H bits)).1)

theorem unit_bounds {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H C : ℕ) (s : State N) (f : State N → ℝ) (hf : ∀ t,0 ≤ f t ∧ f t ≤ 1) :
    0 ≤ mean model p H C s f ∧ mean model p H C s f ≤ 1 :=
  PlayerSpecificAlgebraicCoinExpectation.unit_mean (C*H) _ (fun _bits => hf _)

end Blotto.PlayerSpecificResourceExpectation
