import Blotto.PlayerSpecificNestedDrawLaw
import Blotto.PlayerSpecificAlgebraicNestedTerminalDraw
import Blotto.TerminalResourcesDyadic

/-! The actual reached nested-terminal draw restores its native focus
permutation and has the same complete finite-bit approximation bound. -/
namespace Blotto.PlayerSpecificNestedTerminalDrawLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicNestedTerminalInput PlayerSpecificAlgebraicNestedTerminalSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 3 :=
  (fairBitLaw ((17*H+K)+K)).map (fun bits => values (PlayerSpecificAlgebraicNestedTerminalDraw.draw model root a H K bits) x)

theorem law_eq (model : RationalCostModel) (root : Candidate) (a : Input) (i : TerminalResources)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedTerminalInput.Values a i x) (T : ℕ) (hfit : Fits root a T) (H K : ℕ) :
    law model root a H K x=permuteLaw i.permutation
      (PlayerSpecificNestedDrawChoiceLaw.law model root (prepare model root a).input H K x) := by
  have hp := PlayerSpecificAlgebraicNestedTerminalInput.values model root a i hm hirr hv x hx ha (fun j => (hfit.capacity j).1)
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits => values (PlayerSpecificAlgebraicNestedTerminalDraw.draw model root a H K bits) x) _=
    Measure.map (permuteAllocation i.permutation) (Measure.map (fun bits => values
      (PlayerSpecificAlgebraicNestedSpecDraw.draw model root (prepare model root a).input H K bits) x)
        (fairBitLaw ((17*H+K)+K) : Measure (Fin ((17*H+K)+K) → Bool)))
  rw [Measure.map_map (measurable_permuteAllocation _) (measurable_of_countable _)]
  congr 1
  funext bits
  rw [PlayerSpecificAlgebraicNestedTerminalDraw.draw,PlayerSpecificAlgebraicNestedTerminalDraw.restore_value,hp.2]
  rfl

theorem event_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : TerminalResources)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedTerminalInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (H K : ℕ)
    (A : Set (Allocation 3)) (hA : MeasurableSet A) :
    |(law model root a H K x : Measure (Allocation 3)).real A-(i.dyadicLaw K : Measure (Allocation 3)).real A|
      ≤ 17/(2:ℝ)^H := by
  have hm0 : root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hp := PlayerSpecificAlgebraicNestedTerminalInput.values model root a i hm hirr hv x hx ha (fun j => (hfit.capacity j).1)
  have hf := PlayerSpecificAlgebraicNestedTerminalSizes.bounds model root a T hfit hm hm0 hml hmT (by omega)
  have hi : T ≤ step T := (Nat.le_succ _).trans (large T)
  rw [law_eq model root a i hm hirr hv x hx ha T hfit H K]
  change |(Measure.map (permuteAllocation i.permutation) _).real A-(Measure.map (permuteAllocation i.permutation) _).real A| ≤ _
  rw [map_measureReal_apply (measurable_permuteAllocation _) hA,map_measureReal_apply (measurable_permuteAllocation _) hA]
  exact PlayerSpecificNestedDrawLaw.event_error model root _ i.input H K hm hirr hv x hx hp.1 (step T) hf hml
    (mono hmT hi) (hT.trans hi) _ ((measurable_permuteAllocation _) hA)

theorem CDF_error (model : RationalCostModel) (root : Candidate) (a : Input) (i : TerminalResources)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedTerminalInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (H K : ℕ) :
    CDFClose (law model root a H K x) i.law (17/(2:ℝ)^H+3/(2*(2:ℝ)^K)) := by
  have hm0 : root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hp := PlayerSpecificAlgebraicNestedTerminalInput.values model root a i hm hirr hv x hx ha (fun j => (hfit.capacity j).1)
  have hf := PlayerSpecificAlgebraicNestedTerminalSizes.bounds model root a T hfit hm hm0 hml hmT (by omega)
  have hi : T ≤ step T := (Nat.le_succ _).trans (large T)
  rw [law_eq model root a i hm hirr hv x hx ha T hfit H K]
  exact permuteLaw_CDFClose (PlayerSpecificNestedDrawLaw.CDF_error model root _ i.input H K hm hirr hv x hx hp.1
    (step T) hf hml (mono hmT hi) (hT.trans hi)) _

end Blotto.PlayerSpecificNestedTerminalDrawLaw
