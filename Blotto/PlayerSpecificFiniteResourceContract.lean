import Blotto.PlayerSpecificFiniteResourceLoop

/-! The actual bounded-bit resource program inherits every-path input,
box, mass, termination and row-size guarantees. Each reached pair uses
the exact requested probability; whole-output TV and terminal allocation
construction are separate joins. -/
namespace Blotto.PlayerSpecificFiniteResourceContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
open PlayerSpecificAlgebraicResourceLoop PlayerSpecificAlgebraicResourceLineage
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem request_coin {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (hf : request model p s=some f) (x : ℝ) (hc : Context p x)
    (hs : Valid p x s) (H : ℕ) (bits : Fin H → Bool) :
    (PlayerSpecificAlgebraicMidpointCoin.run model p.parameters.root f.pair.probability H bits=true ↔
      (dyadicMidpointSample H bits:ℝ)<(realPair model p s f hf x hs).probability) ∧
      |PlayerSpecificAlgebraicMidpointCoin.success model p.parameters.root f.pair.probability H-
        (realPair model p s f hf x hs).probability|≤1/(2:ℝ)^H := by
  have hp:=probability model p s f hf hc.normalized hc.irreducible hc.interval x hc.root hs
  have hb : 0≤realEvaluate f.pair.probability x ∧ realEvaluate f.pair.probability x≤1 := by
    rw [hp]
    exact ⟨(realPair model p s f hf x hs).probability_pos.le,(realPair model p s f hf x hs).probability_lt_one.le⟩
  constructor
  · simpa only [hp] using PlayerSpecificAlgebraicMidpointCoin.correct model p.parameters.root f.pair.probability H bits
      hc.normalized hc.irreducible hc.interval x hc.root
  · simpa only [hp] using PlayerSpecificAlgebraicMidpointCoin.paper_discrepancy model p.parameters.root f.pair.probability H
      hc.normalized hc.irreducible hc.interval x hc.root hb

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      ∀ (player : Bool) (H : ℕ) (bits : Fin ((N-1)*H) → Bool),
        let result:=PlayerSpecificFiniteResourceLoop.draw p player H bits
        Valid p x result.1 ∧ InBox (lengths p x) (eval result.1 x) ∧
          (∑ j,eval result.1 x j)=(if player then 2 else 2*(i.budget:ℝ)) ∧
          result.2≤N-1 ∧ result.1.active.length≤1 ∧
          Nonempty (Certificate p player result.1) ∧
          (∀ k,HasHeight (result.1.data.read k) (PlayerSpecificAlgebraicPathContract.height N (PlayerSpecificInitialPositivePrecision.inputSize i))) := by
  obtain ⟨x,hx,hpath⟩:=PlayerSpecificAlgebraicPathContract.original_input i r hr
  refine ⟨x,hx,?_⟩
  intro player H bits
  obtain ⟨choices,_,heq⟩:=PlayerSpecificFiniteResourceLoop.draw_refinement _ player H bits
  rw [heq]
  exact hpath player choices

theorem random_bit_budget (N H : ℕ) : (N-1)*H≤(N+1000)*H :=
  Nat.mul_le_mul_right H (by omega)

end Blotto.PlayerSpecificFiniteResourceContract
