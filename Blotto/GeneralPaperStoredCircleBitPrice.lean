import Blotto.GeneralPaperNativeFairBitDraw

/-! Full bit draw prices for the actual stored circle table built from
physical unit columns. Input/anchor heights are erased properties; every
sort, coefficient and metadata object is consumed from preparation. -/
namespace Blotto.GeneralPaperStoredCircleBitPrice
open GeneralPaperNamedCircleExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem row_work {n R : ℕ} (model : RationalCostModel) (A W S C H : ℕ) (hA : 1≤A)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ)
    (price index : ℕ → ℕ) (Ap : ℕ) (weights : FixedArrayTable state.light.size ℕ) (hs : ∑ j,weights.read j=W)
    (input : FixedArrayTable (state.heavy.size+R) ℚ) (hInput : ∀ j,RationalHeight (input.read j) H)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping state)) (hc : RationalHeight c C)
    (hCapacity : 1+binaryWordWidth (2*n+R+2)≤A) (l : Fin S) :
    (GeneralPaperNamedCircleBitDraw.run model A W S state hR c
      (GeneralPaperStoredCirclePreparation.row price index Ap W state weights input).1 l).2≤
      GeneralPaperNamedCircleBitPrice.drawProfile model A R W S C H n state.light.size := by
  let parts := GeneralPaperStoredCirclePreparation.split index Ap input
  have hk (j : Fin state.heavy.size) : RationalHeight (parts.1.1.read j) H := by
    dsimp only [parts]
    rw [GeneralPaperStoredCirclePreparation.split_data,FixedArrayTable.read_ofFn]
    exact hInput _
  have hr (j : Fin R) : RationalHeight (parts.1.2.read j) H := by
    dsimp only [parts]
    rw [GeneralPaperStoredCirclePreparation.split_data,FixedArrayTable.read_ofFn]
    exact hInput _
  exact GeneralPaperNamedCircleBitPrice.draw_work model A W S C H hA state hR hW hS c price index Ap
    parts.1.1 parts.1.2 weights hs hBijective hc hk hr hCapacity l

theorem columns_work {T n R K : ℕ} (model : RationalCostModel) (A W S C H : ℕ) (hA : 1≤A)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ)
    (price index : ℕ → ℕ) (Ap : ℕ) (weights : FixedArrayTable state.light.size ℕ) (hs : ∑ j,weights.read j=W)
    (columns : FixedArrayTable (state.heavy.size+R) (GeneralPaperQuantizedColumn.Column T K))
    (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping state)) (hc : RationalHeight c C)
    (hCapacity : 1+binaryWordWidth (2*n+R+2)≤A) (_hRowAddress : binaryWordWidth (T+1)≤A) (i : Fin T) (l : Fin S) :
    (GeneralPaperStoredCircleBitDraw.run model A W S state hR c
      (GeneralPaperStoredCirclePreparation.fromColumns price index Ap W state weights columns).1 i l).2≤
      GeneralPaperNamedCircleBitPrice.drawProfile model A R W S C H n state.light.size+64*A := by
  dsimp only [GeneralPaperStoredCircleBitDraw.run]
  rw [GeneralPaperStoredCirclePreparation.columns_row]
  exact Nat.add_le_add_right (row_work model A W S C H hA state hR hW hS c price index Ap weights hs
    (GeneralPaperStoredDictionaryRows.row index Ap columns i).1 (GeneralPaperStoredDictionaryRows.row_height index Ap columns H hColumns i)
    hBijective hc hCapacity l) _

theorem original_work {n T K S : ℕ} (model : RationalCostModel) (A C H : ℕ) (hA : 1≤A)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=o.classified.heavy.size+o.representatives)
    (hR : 0<o.representatives) (hW : 0<o.classified.lightWeight) (hS : 0<S) (c : ℚ)
    (price index : ℕ → ℕ) (Ap : ℕ) (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K))
    (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping o.classified)) (hc : RationalHeight c C)
    (hCapacity : 1+binaryWordWidth (2*n+o.representatives+2)≤A) (hRowAddress : binaryWordWidth (T+1)≤A)
    (i : Fin T) (l : Fin S) :
    (GeneralPaperStoredCircleBitDraw.original model A o hR c
      (GeneralPaperOriginalCirclePreparation.run price index Ap o hm columns).1 i l).2≤
      GeneralPaperNamedCircleBitPrice.drawProfile model A o.representatives o.classified.lightWeight S C H n o.classified.light.size+64*A := by
  have hs : (∑ j,(GeneralPaperNativeLightWeights.run index Ap o).1.read j)=o.classified.lightWeight := by
    rw [GeneralPaperNativeLightWeights.data]
    simp only [FixedArrayTable.read_ofFn]
    exact hConserved
  exact columns_work model A o.classified.lightWeight S C H hA o.classified hR hW hS c price index Ap
    (GeneralPaperNativeLightWeights.run index Ap o).1 hs (GeneralPaperPhysicalFieldCast.columns hm columns)
    (GeneralPaperPhysicalFieldCast.height hm columns H hColumns) hBijective hc hCapacity hRowAddress i l

end Blotto.GeneralPaperStoredCircleBitPrice
