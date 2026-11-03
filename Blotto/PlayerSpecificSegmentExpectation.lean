import Blotto.PlayerSpecificSegmentIdealMean

/-! Exact expectations for the actual cached segment selector. Each
failed choice subtracts the selected weight and uses the untouched flat
suffix; successful choice output ignores that suffix. -/
namespace Blotto.PlayerSpecificSegmentExpectation
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def mean {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) (items : List (Fin slots)) (remaining : Data) (f : Fin slots → ℝ) : ℝ :=
  ∫ bits,f (PlayerSpecificAlgebraicSegmentSample.select model root weights fallback H items remaining
      (PlayerSpecificFiniteResourceLoop.blocks items.length H bits)).1
    ∂(fairBitLaw (items.length*H) : Measure (Fin (items.length*H) → Bool))

theorem nil {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) (remaining : Data) (f : Fin slots → ℝ) :
    mean model root weights fallback H [] remaining f=f fallback := by
  simp only [mean,PlayerSpecificAlgebraicSegmentSample.select,integral_const,probReal_univ,one_smul]

theorem step {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) (slot : Fin slots) (rest : List (Fin slots)) (remaining : Data) (f : Fin slots → ℝ) :
    mean model root weights fallback H (slot::rest) remaining f=
      PlayerSpecificAlgebraicMidpointCoin.success model root
        (PlayerSpecificAlgebraicField.divide root.polynomial (weights.read slot) remaining) H*f slot+
      (1-PlayerSpecificAlgebraicMidpointCoin.success model root
        (PlayerSpecificAlgebraicField.divide root.polynomial (weights.read slot) remaining) H)*
        mean model root weights fallback H rest (PlayerSpecificAlgebraicField.minus root.polynomial remaining (weights.read slot)) f := by
  have he : ∀ bits : Fin ((rest.length+1)*H) → Bool,
      f (PlayerSpecificAlgebraicSegmentSample.select model root weights fallback H (slot::rest) remaining
        (PlayerSpecificFiniteResourceLoop.blocks (rest.length+1) H bits)).1=
      if PlayerSpecificAlgebraicMidpointCoin.run model root (PlayerSpecificAlgebraicField.divide root.polynomial (weights.read slot) remaining) H
          (PlayerSpecificFlatCoinBlocks.headBits rest.length H bits) then f slot else
        f (PlayerSpecificAlgebraicSegmentSample.select model root weights fallback H rest
          (PlayerSpecificAlgebraicField.minus root.polynomial remaining (weights.read slot))
          (PlayerSpecificFiniteResourceLoop.blocks rest.length H (PlayerSpecificFlatCoinBlocks.restBits rest.length H bits))).1 := by
    intro bits
    rw [PlayerSpecificFlatCoinBlocks.blocks_cons,PlayerSpecificAlgebraicSegmentSample.select]
    simp only [List.headD_cons,List.tail_cons]
    by_cases hc : PlayerSpecificAlgebraicMidpointCoin.run model root
        (PlayerSpecificAlgebraicField.divide root.polynomial (weights.read slot) remaining) H
        (PlayerSpecificFlatCoinBlocks.headBits rest.length H bits)=true
    · simp [hc]
    · simp [hc]
  unfold mean
  simp only [List.length_cons]
  simp_rw [he]
  have h := PlayerSpecificFlatCoinBlocks.binary_continuation rest.length H
    (PlayerSpecificAlgebraicMidpointCoin.run model root (PlayerSpecificAlgebraicField.divide root.polynomial (weights.read slot) remaining) H)
    (fun _ => f slot)
    (fun bits => f (PlayerSpecificAlgebraicSegmentSample.select model root weights fallback H rest
      (PlayerSpecificAlgebraicField.minus root.polynomial remaining (weights.read slot))
      (PlayerSpecificFiniteResourceLoop.blocks rest.length H bits)).1)
  simp only [integral_const,probReal_univ,one_smul] at h
  exact h

theorem unit_bounds {slots : ℕ} (model : RationalCostModel) (root : Candidate) (weights : FixedArrayTable slots Data)
    (fallback : Fin slots) (H : ℕ) (items : List (Fin slots)) (remaining : Data) (f : Fin slots → ℝ)
    (hf : ∀ j,0 ≤ f j ∧ f j ≤ 1) :
    0 ≤ mean model root weights fallback H items remaining f ∧ mean model root weights fallback H items remaining f ≤ 1 :=
  PlayerSpecificAlgebraicCoinExpectation.unit_mean (items.length*H) _ (fun _bits => hf _)

end Blotto.PlayerSpecificSegmentExpectation
