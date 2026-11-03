import Blotto.GeneralPaperOriginalCirclePreparation

/-! Exact original-field data from native retained reduction, physical
unit columns and once-materialized original light weights. The same whole
source row and selected shift are used for every output coordinate. -/
namespace Blotto.GeneralPaperOriginalCirclePointwise
open GeneralPaperOriginalCirclePreparation GeneralPaperLightFieldIndexEquiv
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2800000

theorem data {n T K S : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=o.classified.heavy.size+o.representatives)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K)) (hT : 0<T)
    (hR : 0<o.representatives) (hW : 0<o.classified.lightWeight) (hS : 0<S) (c : ℚ)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o) (hBijective : Function.Bijective (mapping o.classified))
    (i : Fin T) (l : Fin S) :
    (fun j => ((draw model o hR c (run price index A o hm columns).1 i l).1.read j:ℝ))=
      scaleAllocation (c:ℝ) (GeneralPaperFieldRelabel.allocation (Equiv.ofBijective (mapping o.classified) hBijective).symm
        (GeneralPaperCircleCanonicalLift.row o.representatives o.classified.lightWeight hR hW
          (GeneralPaperCircleActualWeights.weights o)
          (GeneralPaperFieldRelabel.allocation (finCongr hm.symm)
            ((GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) hT).realRow i))
          (GeneralPaperSelectedShift.selected (o.representatives*o.classified.lightWeight) S (Nat.mul_pos hR hW) hS l).val)) := by
  let weights := (GeneralPaperNativeLightWeights.run index A o).1
  let castColumns := GeneralPaperPhysicalFieldCast.columns hm columns
  let inputs := (GeneralPaperStoredDictionaryRows.run index A castColumns).1
  have hs : (∑ j,weights.read j)=o.classified.lightWeight := by
    dsimp only [weights]
    rw [GeneralPaperNativeLightWeights.data]
    simp only [FixedArrayTable.read_ofFn]
    exact hConserved
  have hw : weights.read=GeneralPaperCircleActualWeights.weights o := by
    funext j
    dsimp only [weights]
    rw [GeneralPaperNativeLightWeights.data,FixedArrayTable.read_ofFn]
  have hRow : (fun j => ((inputs.read i).read j:ℝ))=
      GeneralPaperFieldRelabel.allocation (finCongr hm.symm)
        ((GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) hT).realRow i) :=
    (GeneralPaperStoredDictionaryRows.run_real_row index A castColumns hT i).trans
      (GeneralPaperPhysicalFieldCast.real_row hm columns hT i)
  change (fun j => ((GeneralPaperStoredCirclePreparation.draw model o.classified.lightWeight S o.classified hR c
    (GeneralPaperStoredCirclePreparation.run price index A o.classified.lightWeight o.classified weights inputs).1 i l).1.read j:ℝ))=_
  calc
    _ = scaleAllocation (c:ℝ) (GeneralPaperFieldRelabel.allocation (Equiv.ofBijective (mapping o.classified) hBijective).symm
      (GeneralPaperCircleCanonicalLift.row o.representatives o.classified.lightWeight hR hW weights.read
        (fun j => ((inputs.read i).read j:ℝ))
        (GeneralPaperSelectedShift.selected (o.representatives*o.classified.lightWeight) S (Nat.mul_pos hR hW) hS l).val)) :=
      GeneralPaperStoredCircleLaw.data price index A model _ S o.classified hR hW hS c weights hs inputs hBijective i l
    _ = _ := by rw [hw,hRow]

theorem feasible {n T K S : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=o.classified.heavy.size+o.representatives)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K)) (hT : 0<T) (hK : 0<K)
    (hUnit : GeneralPaperTransferPreparation.UnitDictionary (GeneralPaperRowQuantizer.dictionary columns) hT hK)
    (hR : 0<o.representatives) (hW : 0<o.classified.lightWeight) (hS : 0<S) (c : ℚ) (hc : 0≤c)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o) (hBijective : Function.Bijective (mapping o.classified))
    (i : Fin T) (l : Fin S) :
    Feasible (c:ℝ) (fun j => ((draw model o hR c (run price index A o hm columns).1 i l).1.read j:ℝ)) := by
  have hs : (∑ j,(GeneralPaperNativeLightWeights.run index A o).1.read j)=o.classified.lightWeight := by
    rw [GeneralPaperNativeLightWeights.data]
    simp only [FixedArrayTable.read_ofFn]
    exact hConserved
  change Feasible _ (fun j => ((GeneralPaperStoredCirclePreparation.draw model o.classified.lightWeight S o.classified hR c
    (GeneralPaperStoredCirclePreparation.fromColumns price index A o.classified.lightWeight o.classified
      (GeneralPaperNativeLightWeights.run index A o).1 (GeneralPaperPhysicalFieldCast.columns hm columns)).1 i l).1.read j:ℝ))
  exact GeneralPaperStoredCircleLaw.columns_feasible price index A model _ S o.classified hR hW hS c hc _ hs _ hT hK
    (GeneralPaperPhysicalFieldCast.unit hm columns hT hK hUnit) hBijective i l

end Blotto.GeneralPaperOriginalCirclePointwise
