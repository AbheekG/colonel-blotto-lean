import Blotto.PlayerSpecificFiniteSamplerMeasuredExecution

/-! The measured public draw calls the complete rational finite packet
with the same prepared root and computed precision fields. Its finite
source expression, native return, and every-packet hard budget all join. -/
namespace Blotto.PlayerSpecificFiniteSamplerMeasuredSourceJoin
open PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

theorem accepted_draws {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ)
    (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p) :
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique
        p.base.initial.parameters.root.polynomial p.base.initial.parameters.root.interval x ∧
      ∀ (player : Bool) (bits : Fin (bitCount p) → Bool),
        (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).1=
          PlayerSpecificFiniteSampler.draw p player bits ∧
        Blotto.Feasible (if player then 1 else (i.budget:ℝ))
          (PlayerSpecificRationalOutput.allocation
            (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).1) ∧
        (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).2≤
          PlayerSpecificRationalFiniteMeasuredSourceCost.work i
            p.accuracy.coinBits p.accuracy.scalarBits p.accuracy.outputBits := by
  have hpublic : PlayerSpecificFiniteSampler.prepare i epsilon=some p := by
    rw [←PlayerSpecificFiniteSamplerMeasuredExecution.prepare_value i epsilon he]
    exact hp
  obtain ⟨base,hb,rfl⟩:=PlayerSpecificFiniteSampler.selected i epsilon p hpublic
  obtain ⟨r,hr,hbase⟩:=PlayerSpecificInitialMinimumContract.selected i base hb
  have hi : base.initial=PlayerSpecificAlgebraicInitialVector.prepare
      RationalCostModel.schoolbook i r := by
    rw [hbase]
    exact PlayerSpecificInitialMinimumValues.initial_value i r
  obtain ⟨x,hx,hdraw⟩:=PlayerSpecificFiniteSamplerContract.base_constraints i base hb
  refine ⟨x,hx,?_⟩
  intro player bits
  have hs:=PlayerSpecificRationalFiniteMeasuredSourceCost.original_input i r hr
    player (PlayerSpecificFiniteAccuracy.prepare N base.minimum.exponent epsilon).coinBits
    (PlayerSpecificFiniteAccuracy.prepare N base.minimum.exponent epsilon).scalarBits
    (PlayerSpecificFiniteAccuracy.prepare N base.minimum.exponent epsilon).outputBits bits
  have hsource : (PlayerSpecificFiniteSamplerMeasuredExecution.draw
      (ofBase i.budget base epsilon) player bits).2≤
      PlayerSpecificRationalFiniteMeasuredSourceCost.work i
        (PlayerSpecificFiniteAccuracy.prepare N base.minimum.exponent epsilon).coinBits
        (PlayerSpecificFiniteAccuracy.prepare N base.minimum.exponent epsilon).scalarBits
        (PlayerSpecificFiniteAccuracy.prepare N base.minimum.exponent epsilon).outputBits := by
    change (PlayerSpecificRationalFiniteMeasuredExecution.run base.initial i.budget player
      _ _ _ bits).2≤_
    rw [hi]
    exact hs.2
  refine ⟨PlayerSpecificFiniteSamplerMeasuredExecution.draw_value _ player bits,?_,hsource⟩
  rw [PlayerSpecificFiniteSamplerMeasuredExecution.draw_value]
  exact (hdraw player _ _ _ bits).1

end Blotto.PlayerSpecificFiniteSamplerMeasuredSourceJoin
