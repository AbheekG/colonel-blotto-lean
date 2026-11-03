import Blotto.PlayerSpecificPublicFieldLaw

/-! The actual public rational sample and its unrounded field sample
use the same complete fair packet, with a pathwise downward displacement. -/
namespace Blotto.PlayerSpecificPublicRoundingCoupling
open MeasureTheory PlayerSpecificSturmVariations PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

noncomputable def fieldSample {N : ℕ} (p : Prepared N) (player : Bool) (x : ℝ) (bits : Fin (bitCount p) → Bool) : Allocation N :=
  PlayerSpecificAlgebraicSegment.values (PlayerSpecificAlgebraicFiniteDraw.draw p.base.initial p.budget player
    p.accuracy.coinBits p.accuracy.scalarBits bits) x

theorem field_law {N : ℕ} (p : Prepared N) (player : Bool) (x : ℝ) :
    PlayerSpecificPublicFieldLaw.fieldLaw p player x=(fairBitLaw (bitCount p)).map (fieldSample p player x) := rfl

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (p : Prepared N)
    (hp : prepare i epsilon=some p) :
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique p.base.initial.parameters.root.polynomial p.base.initial.parameters.root.interval x ∧
      ∀ (player : Bool) (bits : Fin (bitCount p) → Bool) (j : Fin N),
        0 ≤ PlayerSpecificFiniteSamplerLaw.sample p player bits j ∧
        PlayerSpecificFiniteSamplerLaw.sample p player bits j ≤ fieldSample p player x bits j ∧
        fieldSample p player x bits j-PlayerSpecificFiniteSamplerLaw.sample p player bits j < 1/(2:ℝ)^p.accuracy.outputBits := by
  obtain ⟨r,hr,hbudget,hinitial⟩ := PlayerSpecificPublicFieldLaw.underlying i epsilon p hp
  obtain ⟨x,hx,hdraw⟩ := PlayerSpecificRationalFiniteDraw.original_input i r hr
  refine ⟨x,?_,?_⟩
  · rw [hinitial]
    exact hx
  · intro player bits j
    change 0 ≤ PlayerSpecificRationalOutput.allocation (PlayerSpecificRationalFiniteDraw.draw p.base.initial p.budget player
        p.accuracy.coinBits p.accuracy.scalarBits p.accuracy.outputBits bits) j ∧ _
    unfold fieldSample PlayerSpecificFiniteSamplerLaw.sample PlayerSpecificFiniteSampler.draw
    rw [hinitial,hbudget]
    have h := hdraw player p.accuracy.coinBits p.accuracy.scalarBits p.accuracy.outputBits bits
    exact ⟨h.1.1 j,(h.2 j).1,(h.2 j).2.1⟩

end Blotto.PlayerSpecificPublicRoundingCoupling
