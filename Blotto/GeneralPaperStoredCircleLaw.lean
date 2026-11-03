import Blotto.GeneralPaperStoredCirclePreparation

/-! Draws from the retained prepared whole-row table equal the selected
circle law after original-field restoration and budget scaling. Every
realization preserves the hard budget; row dependence is never resampled. -/
namespace Blotto.GeneralPaperStoredCircleLaw
open GeneralPaperStoredCirclePreparation GeneralPaperLightFieldIndexEquiv
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2800000

theorem data {T n R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (W S : ℕ)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ)
    (weights : FixedArrayTable state.light.size ℕ) (hs : ∑ j,weights.read j=W)
    (inputs : FixedArrayTable T (FixedArrayTable (state.heavy.size+R) ℚ))
    (hBijective : Function.Bijective (mapping state)) (i : Fin T) (l : Fin S) :
    (fun j => ((draw model W S state hR c (run price index A W state weights inputs).1 i l).1.read j:ℝ))=
      scaleAllocation (c:ℝ) (GeneralPaperFieldRelabel.allocation (Equiv.ofBijective (mapping state) hBijective).symm
        (GeneralPaperCircleHardBudget.reconstruct R W hR hW weights.read
          (fun j => ((inputs.read i).read (Fin.castAdd R j):ℝ))
          (GeneralPaperCircleSortedComparison.sorted (fun a => ((inputs.read i).read (Fin.natAdd state.heavy.size a):ℝ)))
          (GeneralPaperSelectedShift.selected (R*W) S (Nat.mul_pos hR hW) hS l).val)) := by
  change (fun j => ((GeneralPaperNamedCircleExecution.drawArithmetic model W S state hR c
    ((run price index A W state weights inputs).1.read i) l).1.read j:ℝ))=_
  rw [read_row,row_data]
  simpa only [FixedArrayTable.read_ofFn] using GeneralPaperNamedCircleLaw.draw_data model W S state hR hW hS c
    (FixedArrayTable.ofFn (fun j => (inputs.read i).read (Fin.castAdd R j)))
    (FixedArrayTable.ofFn (fun a => (inputs.read i).read (Fin.natAdd state.heavy.size a))) weights hs hBijective l

theorem feasible {T n R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (W S : ℕ)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ) (hc : 0≤c)
    (weights : FixedArrayTable state.light.size ℕ) (hs : ∑ j,weights.read j=W)
    (inputs : FixedArrayTable T (FixedArrayTable (state.heavy.size+R) ℚ))
    (hBijective : Function.Bijective (mapping state)) (B : ℝ)
    (hRows : ∀ i,Feasible B (fun j => ((inputs.read i).read j:ℝ))) (i : Fin T) (l : Fin S) :
    Feasible ((c:ℝ)*B) (fun j => ((draw model W S state hR c (run price index A W state weights inputs).1 i l).1.read j:ℝ)) := by
  change Feasible _ (fun j => ((GeneralPaperNamedCircleExecution.drawArithmetic model W S state hR c
    ((run price index A W state weights inputs).1.read i) l).1.read j:ℝ))
  rw [read_row,row_data]
  apply GeneralPaperNamedCircleLaw.draw_feasible model W S state hR hW hS c hc _ _ weights hs hBijective l B
  simp only [FixedArrayTable.read_ofFn]
  have he := split_real (fun _ => 1) 1 (inputs.read i)
  rw [split_data] at he
  simp only [FixedArrayTable.read_ofFn] at he
  rw [he]
  exact hRows i

theorem height {T n R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (W S : ℕ)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (c : ℚ)
    (weights : FixedArrayTable state.light.size ℕ) (hw : ∀ j,weights.read j≤W)
    (inputs : FixedArrayTable T (FixedArrayTable (state.heavy.size+R) ℚ))
    (hBijective : Function.Bijective (mapping state)) (C H : ℕ) (hc : RationalHeight c C)
    (hRows : ∀ i j,RationalHeight ((inputs.read i).read j) H) (i : Fin T) (l : Fin S) (j : Fin n) :
    RationalHeight ((draw model W S state hR c (run price index A W state weights inputs).1 i l).1.read j)
      (C+(binaryWordWidth R+2*binaryWordWidth W+H)) := by
  change RationalHeight ((GeneralPaperNamedCircleExecution.drawArithmetic model W S state hR c
    ((run price index A W state weights inputs).1.read i) l).1.read j) _
  rw [read_row,row_data]
  apply GeneralPaperNamedCircleHeight.draw_height model W S state hR c _ _ weights hw hBijective C H hc
  · intro a
    rw [FixedArrayTable.read_ofFn]
    exact hRows i _
  · intro a
    rw [FixedArrayTable.read_ofFn]
    exact hRows i _

theorem arithmetic_work {T n R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (W S : ℕ)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ)
    (weights : FixedArrayTable state.light.size ℕ) (hs : ∑ j,weights.read j=W)
    (inputs : FixedArrayTable T (FixedArrayTable (state.heavy.size+R) ℚ))
    (hBijective : Function.Bijective (mapping state)) (i : Fin T) (l : Fin S) :
    (draw model W S state hR c (run price index A W state weights inputs).1 i l).2≤
      1024*(binaryWordWidth (R*W)+1)+24*R+816*(n+1)+64 := by
  change (GeneralPaperNamedCircleExecution.drawArithmetic model W S state hR c
    ((run price index A W state weights inputs).1.read i) l).2+64≤_
  rw [read_row,row_data]
  exact Nat.add_le_add_right (GeneralPaperNamedCirclePrice.draw_arithmetic_work model W S state hR hW hS c _ _ weights hs hBijective l) 64

theorem columns_feasible {T n R K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (W S : ℕ)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ) (hc : 0≤c)
    (weights : FixedArrayTable state.light.size ℕ) (hs : ∑ j,weights.read j=W)
    (columns : FixedArrayTable (state.heavy.size+R) (GeneralPaperQuantizedColumn.Column T K))
    (hT : 0<T) (hK : 0<K)
    (hUnit : GeneralPaperTransferPreparation.UnitDictionary (GeneralPaperRowQuantizer.dictionary columns) hT hK)
    (hBijective : Function.Bijective (mapping state)) (i : Fin T) (l : Fin S) :
    Feasible (c:ℝ) (fun j => ((draw model W S state hR c (fromColumns price index A W state weights columns).1 i l).1.read j:ℝ)) := by
  have h := feasible price index A model W S state hR hW hS c hc weights hs
    (GeneralPaperStoredDictionaryRows.run index A columns).1 hBijective 1
    (GeneralPaperStoredDictionaryRows.run_feasible index A columns hT hK hUnit) i l
  dsimp only [fromColumns]
  simpa only [mul_one] using h

theorem columns_height {T n R K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (W S : ℕ)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (c : ℚ)
    (weights : FixedArrayTable state.light.size ℕ) (hw : ∀ j,weights.read j≤W)
    (columns : FixedArrayTable (state.heavy.size+R) (GeneralPaperQuantizedColumn.Column T K))
    (hBijective : Function.Bijective (mapping state)) (C H : ℕ) (hc : RationalHeight c C)
    (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H) (i : Fin T) (l : Fin S) (j : Fin n) :
    RationalHeight ((draw model W S state hR c (fromColumns price index A W state weights columns).1 i l).1.read j)
      (C+(binaryWordWidth R+2*binaryWordWidth W+H)) := by
  dsimp only [fromColumns]
  exact height price index A model W S state hR c weights hw (GeneralPaperStoredDictionaryRows.run index A columns).1
    hBijective C H hc (GeneralPaperStoredDictionaryRows.run_height index A columns H hColumns) i l j

end Blotto.GeneralPaperStoredCircleLaw
