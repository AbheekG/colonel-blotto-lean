import Blotto.GeneralPaperStoredCircleLaw

/-! Complete local arithmetic prices for stored whole-row preparation,
including extraction, split, native sort, coefficients and metadata. The
source and compiler run before this phase; draws reuse the returned table. -/
namespace Blotto.GeneralPaperStoredCirclePreparationPrice
open GeneralPaperStoredCirclePreparation GeneralPaperNamedCircleExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem split_work {h R : ℕ} (input : FixedArrayTable (h+R) ℚ) :
    (split (fun _ => 1) 1 input).2≤192*(h+R+1) := by
  have hk := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 64
    (fun j : Fin h => (input.read (Fin.castAdd R j),64)) (by decide) (fun _ _ => le_rfl) (fun _ => le_rfl)
  have hr := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 66
    (fun a : Fin R => (input.read (Fin.natAdd h a),GeneralPaperNaturalPrimitivePrice.binary (fun _ => 1) (fun a b => a+b) h a.val+64))
    (by decide) (fun _ _ => le_rfl) (by intro a;simp only [GeneralPaperNaturalPrimitivePrice.binary];decide)
  unfold split
  dsimp only
  nlinarith only [hk,hr]

theorem metadata_work {g : ℕ} (R W : ℕ) (weights : FixedArrayTable g ℕ) (hw : ∀ j,weights.read j≤W)
    (hs : ∑ j,weights.read j=W) : (GeneralPaperNativeChoiceArray.prepare (fun _ => 1) 1 R weights).2≤104*(g+1) := by
  have h := GeneralPaperCircleArcMetadata.work_bound (fun _ => 1) (fun _ _ _ => le_rfl) 1 R (List.ofFn weights.read) 0
    (R*W+R+W+1) (by omega) (by rw [List.sum_ofFn,hs];omega) (by
      intro w hm
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm
      exact (hw j).trans (by omega))
  rw [List.length_ofFn] at h
  unfold GeneralPaperNativeChoiceArray.prepare
  dsimp only
  nlinarith only [h]

theorem prepared_work {n R : ℕ} (model : RationalCostModel) (W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (input : FixedArrayTable R ℚ) (weights : FixedArrayTable state.light.size ℕ)
    (hw : ∀ j,weights.read j≤W) (hs : ∑ j,weights.read j=W) :
    (prepare (fun _ => 1) (fun _ => 1) 1 W state kept input weights).2≤
      GeneralPaperNativeSortedRows.oneProfile R 1 1+217*state.light.size+293 := by
  have hSort := GeneralPaperNativeSortedModels.one_arithmetic_work model input
  have hCoeff := GeneralPaperCircleRationalCoefficients.work (fun _ => 1) (fun _ => 1) (fun _ _ _ => le_rfl)
    1 R W (by decide) weights hw (fun _ _ => le_rfl)
  have hMetadata := metadata_work R W weights hw hs
  change (GeneralPaperNativeSortedRows.one (fun _ => 1) (fun _ => 1) 1 input).2≤_ at hSort
  unfold prepare
  dsimp only
  nlinarith only [hSort,hCoeff,hMetadata]

def rowProfile (h g R : ℕ) : ℕ := GeneralPaperNativeSortedRows.oneProfile R 1 1+217*g+192*(h+R+1)+325

theorem row_work {n R : ℕ} (model : RationalCostModel) (W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ) (hw : ∀ j,weights.read j≤W) (hs : ∑ j,weights.read j=W)
    (input : FixedArrayTable (state.heavy.size+R) ℚ) :
    (row (fun _ => 1) (fun _ => 1) 1 W state weights input).2≤rowProfile state.heavy.size state.light.size R := by
  have hSplit := split_work input
  have hPrepared := prepared_work model W state (split (fun _ => 1) 1 input).1.1 (split (fun _ => 1) 1 input).1.2 weights hw hs
  unfold row rowProfile
  dsimp only
  omega

theorem work {T n R : ℕ} (model : RationalCostModel) (W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ) (hw : ∀ j,weights.read j≤W) (hs : ∑ j,weights.read j=W)
    (inputs : FixedArrayTable T (FixedArrayTable (state.heavy.size+R) ℚ)) :
    (run (fun _ => 1) (fun _ => 1) 1 W state weights inputs).2≤
      T*(rowProfile state.heavy.size state.light.size R+64)+44*(T+1) := by
  unfold run
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 (rowProfile state.heavy.size state.light.size R+64)
    (fun i : Fin T => let prepared := row (fun _ => 1) (fun _ => 1) 1 W state weights (inputs.read i); (prepared.1,prepared.2+64))
    (by decide) (fun _ _ => le_rfl)
    (fun i => Nat.add_le_add_right (row_work model W state weights hw hs (inputs.read i)) 64)
  simpa only [Nat.mul_one] using h

def columnsProfile (T h g R : ℕ) : ℕ :=
  T*((h+R)*128+44*(h+R+1)+64)+44*(T+1)+T*(rowProfile h g R+64)+44*(T+1)+64

theorem columns_work {T n R K : ℕ} (model : RationalCostModel) (W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ) (hw : ∀ j,weights.read j≤W) (hs : ∑ j,weights.read j=W)
    (columns : FixedArrayTable (state.heavy.size+R) (GeneralPaperQuantizedColumn.Column T K)) :
    (fromColumns (fun _ => 1) (fun _ => 1) 1 W state weights columns).2≤
      columnsProfile T state.heavy.size state.light.size R := by
  have hExtract := GeneralPaperStoredDictionaryRows.work (fun _ => 1) 1 (by decide) columns (fun _ _ => le_rfl)
  have hPrepared := work model W state weights hw hs (GeneralPaperStoredDictionaryRows.run (fun _ => 1) 1 columns).1
  unfold fromColumns columnsProfile
  dsimp only
  nlinarith only [hExtract,hPrepared]

end Blotto.GeneralPaperStoredCirclePreparationPrice
