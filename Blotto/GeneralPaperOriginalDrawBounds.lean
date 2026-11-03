import Blotto.GeneralPaperOriginalDrawEquilibrium

/-! Whole original-coordinate output heights, hard budgets and local
arithmetic prices derive from retained native reduction/column data. These
do not supply any runtime height, sorting, capacity or security oracle. -/
namespace Blotto.GeneralPaperOriginalDrawBounds
open GeneralPaperOriginalCirclePreparation GeneralPaperLightFieldIndexEquiv
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2800000

theorem height {n T K S : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=o.classified.heavy.size+o.representatives)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K)) (hR : 0<o.representatives) (c : ℚ)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o) (hBijective : Function.Bijective (mapping o.classified))
    (C H : ℕ) (hc : RationalHeight c C) (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (i : Fin T) (l : Fin S) (j : Fin n) :
    RationalHeight ((draw model o hR c (run price index A o hm columns).1 i l).1.read j)
      (C+(binaryWordWidth o.representatives+2*binaryWordWidth o.classified.lightWeight+H)) := by
  have hs : (∑ j,(GeneralPaperNativeLightWeights.run index A o).1.read j)=o.classified.lightWeight := by
    rw [GeneralPaperNativeLightWeights.data]
    simp only [FixedArrayTable.read_ofFn]
    exact hConserved
  have hw : ∀ j,(GeneralPaperNativeLightWeights.run index A o).1.read j≤o.classified.lightWeight := by
    rw [←hs]
    intro j
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  change RationalHeight ((GeneralPaperStoredCirclePreparation.draw model o.classified.lightWeight S o.classified hR c
    (GeneralPaperStoredCirclePreparation.fromColumns price index A o.classified.lightWeight o.classified
      (GeneralPaperNativeLightWeights.run index A o).1 (GeneralPaperPhysicalFieldCast.columns hm columns)).1 i l).1.read j) _
  exact GeneralPaperStoredCircleLaw.columns_height price index A model _ S o.classified hR c _ hw _ hBijective C H hc
    (GeneralPaperPhysicalFieldCast.height hm columns H hColumns) i l j

theorem arithmetic_draw_work {n T K S : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=o.classified.heavy.size+o.representatives)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K))
    (hR : 0<o.representatives) (hW : 0<o.classified.lightWeight) (hS : 0<S) (c : ℚ)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o) (hBijective : Function.Bijective (mapping o.classified))
    (i : Fin T) (l : Fin S) :
    (draw model o hR c (run price index A o hm columns).1 i l).2≤
      1024*(binaryWordWidth (o.representatives*o.classified.lightWeight)+1)+24*o.representatives+816*(n+1)+64 := by
  have hs : (∑ j,(GeneralPaperNativeLightWeights.run index A o).1.read j)=o.classified.lightWeight := by
    rw [GeneralPaperNativeLightWeights.data]
    simp only [FixedArrayTable.read_ofFn]
    exact hConserved
  change (GeneralPaperStoredCirclePreparation.draw model o.classified.lightWeight S o.classified hR c
    (GeneralPaperStoredCirclePreparation.run price index A o.classified.lightWeight o.classified
      (GeneralPaperNativeLightWeights.run index A o).1
      (GeneralPaperStoredDictionaryRows.run index A (GeneralPaperPhysicalFieldCast.columns hm columns)).1).1 i l).2≤_
  exact GeneralPaperStoredCircleLaw.arithmetic_work price index A model _ S o.classified hR hW hS c _ hs _ hBijective i l

theorem original_preparation_work {n T K : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (columns : FixedArrayTable (GeneralPaperOriginalValueReduction.run bits model W k input).1.m (GeneralPaperQuantizedColumn.Column T K)) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    (run (fun _ => 1) (fun _ => 1) 1 o hm columns).2≤108*o.classified.light.size+44+
      GeneralPaperStoredCirclePreparationPrice.columnsProfile T o.classified.heavy.size o.classified.light.size o.representatives+64 :=
  arithmetic_work model _ hm (GeneralPaperCircleActualWeights.original_sum bits model W k input) columns

theorem original_feasible {n T K S : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (columns : FixedArrayTable (GeneralPaperOriginalValueReduction.run bits model W k input).1.m (GeneralPaperQuantizedColumn.Column T K))
    (hT : 0<T) (hK : 0<K) (hUnit : GeneralPaperTransferPreparation.UnitDictionary (GeneralPaperRowQuantizer.dictionary columns) hT hK)
    (hS : 0<S) (price index : ℕ → ℕ) (A : ℕ) (c : ℚ) (hc : 0≤c) (i : Fin T) (l : Fin S) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input
    Feasible (c:ℝ) (fun j => ((draw model o hR c (run price index A o hm columns).1 i l).1.read j:ℝ)) :=
  GeneralPaperOriginalCirclePointwise.feasible price index A model _ hm columns hT hK hUnit
    (GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input)
    (GeneralPaperCircleActualWeights.original_total_positive bits model W k input v hv
      (GeneralPaperNativeCircleLoss.original_light_positive bits model W k input hReplace)) hS c hc
    (GeneralPaperCircleActualWeights.original_sum bits model W k input) (original_bijective bits model W k input) i l

end Blotto.GeneralPaperOriginalDrawBounds
