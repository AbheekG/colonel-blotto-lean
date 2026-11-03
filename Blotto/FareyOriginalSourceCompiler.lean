import Blotto.FareyCertifiedSourceRestart
import Blotto.BudgetScalingRegret

/-! The original positive rational budgets determine the source ratio and
guards. Every accepted normalized pair is scaled back to the original hard
budgets, preserving both continuous regrets and the rejection event exactly.
This is the semantic compiler join for normalized rational field values;
finite representation, efficient extrema/output sampling and full execution
prices are not asserted by this law-valued construction. -/

namespace Blotto.FareyOriginalSourceCompiler
open FareyUnitSourceInputs
open scoped Classical

structure Input (fields : ℕ) where
  values : RationalFieldSelector fields
  richBudget : ℚ
  poorBudget : ℚ
  rich_positive : 0 < richBudget
  poor_positive : 0 < poorBudget
  poor_le_rich : poorBudget ≤ richBudget

def Input.ratio {fields : ℕ} (i : Input fields) : ℚ := i.poorBudget / i.richBudget

theorem Input.ratio_guards {fields : ℕ} (i : Input fields) :
    0 < i.ratio ∧ i.ratio ≤ 1 :=
  ⟨div_pos i.poor_positive i.rich_positive, (div_le_one₀ i.rich_positive).mpr i.poor_le_rich⟩

theorem Input.scaled_ratio {fields : ℕ} (i : Input fields) :
    (i.richBudget : ℝ) * (i.ratio : ℝ) = (i.poorBudget : ℝ) := by
  unfold Input.ratio
  rw [Rat.cast_div]
  have hPositive : (0 : ℝ) < i.richBudget := by exact_mod_cast i.rich_positive
  field_simp

def Input.seedCap {n : ℕ} (i : Input (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) : ℕ :=
  sourceSeedCap i.ratio i.ratio_guards i.values epsilon he accuracy

noncomputable def Input.run {n : ℕ} (i : Input (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (attempts : ℕ)
    (bits : Fin (attempts * i.seedCap epsilon he accuracy) → Bool) :
    Option (Mixed (n + 1) × Mixed (n + 1)) :=
  (certifiedSourceRestart i.ratio i.ratio_guards i.values epsilon he accuracy attempts bits).map
    (fun pair => (scaleLaw (i.richBudget : ℝ) pair.1, scaleLaw (i.richBudget : ℝ) pair.2))

theorem Input.run_sound {n : ℕ} (i : Input (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (attempts : ℕ)
    (bits : Fin (attempts * i.seedCap epsilon he accuracy) → Bool)
    (richLaw poorLaw : Mixed (n + 1)) (hResult : i.run epsilon he accuracy attempts bits = some (richLaw, poorLaw)) :
    Supported (i.richBudget : ℝ) richLaw ∧ Supported (i.poorBudget : ℝ) poorLaw ∧
      regret i.values.values (i.richBudget : ℝ) richLaw poorLaw ≤ (epsilon : ℝ) ∧
        regret i.values.values (i.poorBudget : ℝ) poorLaw richLaw ≤ (epsilon : ℝ) := by
  cases hNormalized : certifiedSourceRestart i.ratio i.ratio_guards i.values
      epsilon he accuracy attempts bits with
  | none => simp only [Input.run, hNormalized, Option.map_none, reduceCtorEq] at hResult
  | some pair =>
    obtain ⟨normalizedRich,normalizedPoor⟩ := pair
    simp only [Input.run, hNormalized, Option.map_some] at hResult
    have hPair := Option.some.inj hResult
    have hRichLaw := congrArg Prod.fst hPair
    have hPoorLaw := congrArg Prod.snd hPair
    dsimp only at hRichLaw hPoorLaw
    rw [← hRichLaw, ← hPoorLaw]
    obtain ⟨hRich,hPoor,hRegretR,hRegretP⟩ := source_restart_sound
      i.ratio i.ratio_guards i.values epsilon he accuracy attempts bits _ _ hNormalized
    have hBudget : (0 : ℝ) < i.richBudget := by exact_mod_cast i.rich_positive
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [mul_one] using scaleLaw_supported hBudget.le normalizedRich hRich
    · simpa only [i.scaled_ratio] using scaleLaw_supported hBudget.le normalizedPoor hPoor
    · have hScale := regret_scale i.values.values hBudget 1 normalizedRich normalizedPoor
      rw [mul_one] at hScale
      rw [hScale]
      exact hRegretR
    · have hScale := regret_scale i.values.values hBudget (i.ratio : ℝ) normalizedPoor normalizedRich
      rw [i.scaled_ratio] at hScale
      rw [hScale]
      exact hRegretP

theorem Input.run_rejection_iff {n : ℕ} (i : Input (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (attempts : ℕ)
    (bits : Fin (attempts * i.seedCap epsilon he accuracy) → Bool) :
    i.run epsilon he accuracy attempts bits = none ↔
      certifiedSourceRestart i.ratio i.ratio_guards i.values epsilon he accuracy attempts bits = none := by
  unfold Input.run
  cases certifiedSourceRestart i.ratio i.ratio_guards i.values epsilon he accuracy attempts bits <;> simp

theorem Input.run_failure_bound {n : ℕ} (i : Input (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy ∧ accuracy ≤ 1 / 16) (attempts : ℕ) :
    (fairBitKernel (attempts * i.seedCap epsilon he accuracy)).mean (fun bits =>
      if i.run epsilon he accuracy attempts bits = none then 1 else 0) ≤ (1 / 4 : ℝ) ^ attempts := by
  simp_rw [i.run_rejection_iff]
  exact source_restart_failure_bound i.ratio i.ratio_guards i.values epsilon he accuracy ha attempts

end Blotto.FareyOriginalSourceCompiler
