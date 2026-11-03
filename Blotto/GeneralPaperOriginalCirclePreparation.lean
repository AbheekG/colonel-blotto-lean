import Blotto.GeneralPaperPhysicalFieldCast

/-! Original-input reconstruction consumes the retained native reduction
and physical unit columns. Light weights are materialized once, field size
casts erase, and all circle rows are prepared once. A draw reads only that
prepared table and retained total/field maps, then applies its budget scale. -/
namespace Blotto.GeneralPaperOriginalCirclePreparation
set_option autoImplicit false
set_option maxHeartbeats 2400000

def run {n T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K)) :
    FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)×ℕ :=
  let weights := GeneralPaperNativeLightWeights.run index A o
  let prepared := GeneralPaperStoredCirclePreparation.fromColumns price index A o.classified.lightWeight o.classified
    weights.1 (GeneralPaperPhysicalFieldCast.columns hm columns)
  (prepared.1,weights.2+prepared.2+64*A)

theorem data {n T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K)) :
    (run price index A o hm columns).1=
      (GeneralPaperStoredCirclePreparation.fromColumns price index A o.classified.lightWeight o.classified
        (GeneralPaperNativeLightWeights.run index A o).1 (GeneralPaperPhysicalFieldCast.columns hm columns)).1 := rfl

def draw {n T S : ℕ} (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n)
    (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives))
    (i : Fin T) (l : Fin S) : FixedArrayTable n ℚ×ℕ :=
  GeneralPaperStoredCirclePreparation.draw model o.classified.lightWeight S o.classified hR c prepared i l

theorem arithmetic_work {n T K : ℕ} (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K)) :
    (run (fun _ => 1) (fun _ => 1) 1 o hm columns).2≤108*o.classified.light.size+44+
      GeneralPaperStoredCirclePreparationPrice.columnsProfile T o.classified.heavy.size o.classified.light.size o.representatives+64 := by
  have hs : (∑ j,(GeneralPaperNativeLightWeights.run (fun _ => 1) 1 o).1.read j)=o.classified.lightWeight := by
    rw [GeneralPaperNativeLightWeights.data]
    simp only [FixedArrayTable.read_ofFn]
    exact hConserved
  have hw : ∀ j,(GeneralPaperNativeLightWeights.run (fun _ => 1) 1 o).1.read j≤o.classified.lightWeight := by
    rw [←hs]
    intro j
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hWeights := GeneralPaperNativeLightWeights.arithmetic_work o
  have hPrepare := GeneralPaperStoredCirclePreparationPrice.columns_work model o.classified.lightWeight o.classified
    (GeneralPaperNativeLightWeights.run (fun _ => 1) 1 o).1 hw hs (GeneralPaperPhysicalFieldCast.columns hm columns)
  unfold run
  dsimp only
  omega

end Blotto.GeneralPaperOriginalCirclePreparation
