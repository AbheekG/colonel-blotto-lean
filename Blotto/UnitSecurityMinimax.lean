import Blotto.RichMinimax
import Blotto.PRGEquilibrium

/-! Boundary completion of the continuous security-value identity. Exact
one-field and equal-unit-budget equilibria join the strict unequal-budget
regular-rich argument. The result ranges over original at-most whole laws;
the equal-budget small-field case uses an actual checked PRG coupling. -/

namespace Blotto.UnitSecurityMinimax
open ContinuousSecurityValues PureBoundaryEquilibria
open scoped Classical

theorem lossInfimum_sum_eq_one_of_equilibrium {n : ℕ} (values : Values n)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (lawA lawB : Mixed n)
    (hLawA : Supported A lawA) (hLawB : Supported B lawB)
    (hRegretA : regret values A lawA lawB = 0) (hRegretB : regret values B lawB lawA = 0) :
    lossInfimum values A B + lossInfimum values B A = 1 := by
  have hSum := regret_sum values A B lawA lawB
  rw [hRegretA, hRegretB] at hSum
  have hInfA := lossInfimum_le_of_supported values A B hB lawA hLawA
  have hInfB := lossInfimum_le_of_supported values B A hA lawB hLawB
  have hWeak := lossInfimum_sum_ge_one values A B hA hB
  linarith

theorem equal_unit_lossInfimum {n : ℕ} (values : Values n) :
    lossInfimum values 1 1 = 1 / 2 := by
  by_cases hHeavy : ∃ chosen, 1 / 2 ≤ values.weight chosen
  · obtain ⟨chosen,hChosen⟩ := hHeavy
    have hExact := dominant_vertex_equilibrium values 1 (by norm_num) chosen hChosen
    have hSum := lossInfimum_sum_eq_one_of_equilibrium values 1 1 (by norm_num) (by norm_num)
      (pointLaw (vertex 1 chosen)) (pointLaw (vertex 1 chosen))
      hExact.1 hExact.1 hExact.2 hExact.2
    linarith
  · have hSmall : ∀ chosen, values.weight chosen ≤ 1 / 2 := by
      intro chosen
      exact (lt_of_not_ge (fun h => hHeavy ⟨chosen,h⟩)).le
    obtain ⟨rich,poor,hRich,hPoor,_hRichMarginal,_hPoorMarginal,hRegretR,hRegretP,_⟩ :=
      exists_prg_equilibrium values (b := 1) (by norm_num) le_rfl hSmall
    have hSum := lossInfimum_sum_eq_one_of_equilibrium values 1 1 (by norm_num) (by norm_num)
      rich poor hRich hPoor hRegretR hRegretP
    linarith

theorem lossInfimum_sum_eq_one {n : ℕ} (values : Values (n + 1))
    (ratio : ℝ) (hr : 0 < ratio ∧ ratio ≤ 1) :
    lossInfimum values 1 ratio + lossInfimum values ratio 1 = 1 := by
  by_cases hStrict : ratio < 1
  · by_cases hn : 0 < n
    · exact RichMinimax.lossInfimum_sum_eq_one values hr.1 (by omega) hStrict
    · have hnZero : n = 0 := by omega
      subst n
      obtain ⟨hRich,hPoor,hRegretR,hRegretP⟩ :=
        oneField_equilibrium values 1 ratio (by norm_num) hr.1.le
      exact lossInfimum_sum_eq_one_of_equilibrium values 1 ratio (by norm_num) hr.1.le
        (pointLaw (oneFieldRow 1)) (pointLaw (oneFieldRow ratio)) hRich hPoor hRegretR hRegretP
  · have hEqual : ratio = 1 := le_antisymm hr.2 (le_of_not_gt hStrict)
    rw [hEqual, equal_unit_lossInfimum]
    norm_num

end Blotto.UnitSecurityMinimax
