import Blotto.GeneralPaperEqualRealBranchDraw

/-! One-field preparation returns both constructed full-budget rows before
any accuracy selection or source optimization. Its deterministic draw reads
and writes the stored row and requests no random primitive. -/
namespace Blotto.GeneralPaperOneFieldRealPreparation
open MeasureTheory
open PureBoundaryEquilibria
set_option autoImplicit false
set_option maxHeartbeats 1400000

def run (richBudget poorBudget : ℚ) : (RationalResourceArray 1 × RationalResourceArray 1) × ℕ :=
  let rich := GeneralPaperEqualRealBoundaryScan.vertex richBudget (0 : Fin 1)
  let poor := GeneralPaperEqualRealBoundaryScan.vertex poorBudget (0 : Fin 1)
  ((rich.1, poor.1), rich.2 + poor.2 + 32)

theorem vertex_one (budget : ℚ) :
    (GeneralPaperEqualRealBoundaryScan.vertex budget (0 : Fin 1)).1.realAllocation = oneFieldRow (budget : ℝ) := by
  rw [GeneralPaperEqualRealBoundaryScan.vertex_data]
  funext j
  fin_cases j
  rfl

theorem data (richBudget poorBudget : ℚ) :
    (run richBudget poorBudget).1.1.realAllocation = oneFieldRow (richBudget : ℝ) ∧
    (run richBudget poorBudget).1.2.realAllocation = oneFieldRow (poorBudget : ℝ) :=
  ⟨vertex_one richBudget, vertex_one poorBudget⟩

theorem work (richBudget poorBudget : ℚ) : (run richBudget poorBudget).2 ≤ 288 := by
  have hA := GeneralPaperEqualRealBoundaryScan.vertex_work richBudget (0 : Fin 1)
  have hB := GeneralPaperEqualRealBoundaryScan.vertex_work poorBudget (0 : Fin 1)
  dsimp only [run]
  omega

theorem equilibrium (values : Values 1) (richBudget poorBudget : ℚ)
    (hA : 0 ≤ richBudget) (hB : 0 ≤ poorBudget) :
    let rows := (run richBudget poorBudget).1
    let μ := pointLaw rows.1.realAllocation
    let ν := pointLaw rows.2.realAllocation
    Supported (richBudget : ℝ) μ ∧ Supported (poorBudget : ℝ) ν ∧
      regret values (richBudget : ℝ) μ ν = 0 ∧ regret values (poorBudget : ℝ) ν μ = 0 := by
  dsimp only
  rw [(data richBudget poorBudget).1, (data richBudget poorBudget).2]
  exact oneField_equilibrium values _ _ (by exact_mod_cast hA) (by exact_mod_cast hB)

theorem every_output (richBudget poorBudget : ℚ) (hA : 0 ≤ richBudget) (hB : 0 ≤ poorBudget) :
    FullBudget (richBudget : ℝ) (run richBudget poorBudget).1.1.realAllocation ∧
      FullBudget (poorBudget : ℝ) (run richBudget poorBudget).1.2.realAllocation := by
  rw [(data richBudget poorBudget).1, (data richBudget poorBudget).2]
  exact ⟨oneFieldRow_fullBudget _ (by exact_mod_cast hA), oneFieldRow_fullBudget _ (by exact_mod_cast hB)⟩

noncomputable def draw (row : RationalResourceArray 1) : GeneralPaperEqualRealDraw.Result 1 :=
  let copied := GeneralPaperEqualRealBranchDraw.copyRow row
  ⟨copied.value, 0, 0, copied.cost + 16⟩

theorem draw_data (row : RationalResourceArray 1) : (draw row).output.read = row.realAllocation :=
  GeneralPaperEqualRealBranchDraw.copy_data row

theorem draw_resources (row : RationalResourceArray 1) :
    (draw row).uniformReads = 0 ∧ (draw row).bitReads = 0 ∧ (draw row).work = 21 := by
  norm_num [draw, GeneralPaperEqualRealBranchDraw.copy_work]

end Blotto.GeneralPaperOneFieldRealPreparation
