import Blotto.GeneralPaperBasisDenseWork

/-! One priced native original-row basis extension. Original sparse row
construction, dense zero/scatter, next-column/prefix materialization, cached
Schur update and retained-row reference append each execute once.
-/
namespace Blotto.GeneralPaperBasisAdvanceWork
open RationalOrderCell GeneralPaperBasisState GeneralPaperBasisStoredProducts
open GeneralPaperBasisOriginalDirection GeneralPaperBasisDenseRow
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {T m K j : ℕ} (labels : Fin T → Fin m → Fin K) (state : State j (m*(K-1)))
    (hj : j<m*(K-1)) (answer : GeneralPaperRayEndpoint.Answer T m K) : State (j+1) (m*(K-1)) × ℕ :=
  let original := GeneralPaperBlockerRowPrice.run 1 labels answer.blocker
  let dense := GeneralPaperBasisDenseWork.run original.1
  let row := dense.1
  let u := GeneralPaperBasisPreparationWork.columnRun state.rows (next hj)
  let v := GeneralPaperBasisArrayPrice.prefixRun (fun _ => 1) 1 row (Nat.le_of_lt hj)
  let updated := GeneralPaperBasisCacheWork.run state.determinant state.adjugate u.1 v.1 (row.coefficients.read (next hj))
  let rows := GeneralPaperBasisArrayPrice.appendRun (fun _ => 1) 1 state.rows row
  (⟨rows.1,updated.determinant,updated.adjugate⟩,original.2+dense.2+u.2+v.2+updated.work+rows.2+32)

theorem data {T m K j : ℕ} (labels : Fin T → Fin m → Fin K) (state : State j (m*(K-1)))
    (hj : j<m*(K-1)) (answer : GeneralPaperRayEndpoint.Answer T m K) :
    (run labels state hj answer).1=advance labels state hj answer := by
  simp only [run,GeneralPaperBlockerRowPrice.data,GeneralPaperBasisDenseWork.data,GeneralPaperBasisPreparationWork.column_data,GeneralPaperBasisArrayPrice.prefix_data,
    GeneralPaperBasisCacheWork.determinant_data,GeneralPaperBasisCacheWork.adjugate_data,GeneralPaperBasisArrayPrice.append_data,advance]

def profile (j d m : ℕ) : ℕ := 4096*((j+2)^2+d+m+1)

theorem work {T m K j : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K) (state : State j (m*(K-1)))
    (hj : j<m*(K-1)) (answer : GeneralPaperRayEndpoint.Answer T m K) :
    (run labels state hj answer).2≤profile j (m*(K-1)) m := by
  let original := GeneralPaperBlockerRowPrice.run 1 labels answer.blocker
  let dense := GeneralPaperBasisDenseWork.run original.1
  let row := dense.1
  let u := GeneralPaperBasisPreparationWork.columnRun state.rows (next hj)
  let v := GeneralPaperBasisArrayPrice.prefixRun (fun _ => 1) 1 row (Nat.le_of_lt hj)
  let updated := GeneralPaperBasisCacheWork.run state.determinant state.adjugate u.1 v.1 (row.coefficients.read (next hj))
  let rows := GeneralPaperBasisArrayPrice.appendRun (fun _ => 1) 1 state.rows row
  have hOriginal : original.2≤256*(m+1) := by simpa only [Nat.mul_one] using GeneralPaperBlockerRowPrice.work 1 labels answer.blocker
  have hLen : original.1.terms.length≤m+1 := by rw [GeneralPaperBlockerRowPrice.data]; exact GeneralPaperBlockerRowPrice.length hm labels answer.blocker
  have hDense := GeneralPaperBasisDenseWork.work original.1
  change dense.2≤_ at hDense
  have hU := GeneralPaperBasisPreparationWork.column_work state.rows (next hj)
  have hV := GeneralPaperBasisArrayPrice.prefix_work row (Nat.le_of_lt hj)
  have hUpdate := GeneralPaperBasisCacheWork.work state.determinant state.adjugate u.1 v.1 (row.coefficients.read (next hj))
  have hRows := GeneralPaperBasisArrayPrice.append_work state.rows row
  change original.2+dense.2+u.2+v.2+updated.work+rows.2+32≤profile j (m*(K-1)) m
  unfold profile
  nlinarith only [hOriginal,hLen,hDense,hU,hV,hUpdate,hRows]

theorem profile_mono (j d m : ℕ) (hj : j≤d) : profile j d m≤profile d d m := by
  unfold profile
  nlinarith only [hj]

end Blotto.GeneralPaperBasisAdvanceWork
