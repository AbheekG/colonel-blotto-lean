import Blotto.GeneralPaperBasisAppendBits

/-! Complete original-row basis extension with bit prices: literal blocker
construction, coordinate arithmetic/scatter, column/prefix materialization,
full cached update and retained-row append. Native states agree exactly.
-/
namespace Blotto.GeneralPaperBasisAdvanceBits
open RationalOrderCell GeneralPaperBasisState GeneralPaperBasisStoredProducts GeneralPaperBasisOriginalDirection
open GeneralPaperBasisInvariant GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 4096

def run {T m K j : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K) (state : State j (m*(K-1)))
    (hj : j<m*(K-1)) (answer : GeneralPaperRayEndpoint.Answer T m K) : State (j+1) (m*(K-1)) × ℕ :=
  let original := GeneralPaperBlockerRowPrice.run W labels answer.blocker
  let dense := GeneralPaperBasisDenseBits.run primitive W original.1
  let u := GeneralPaperBasisAssemblyBits.columnRun W state.rows (next hj)
  let v := GeneralPaperBasisArrayPrice.prefixRun (fun w => w) W dense.1 (Nat.le_of_lt hj)
  let updated := GeneralPaperBasisCacheBits.run primitive W state.determinant state.adjugate u.1 v.1 (dense.1.coefficients.read (next hj))
  let rows := GeneralPaperBasisArrayPrice.appendRun (fun w => w) W state.rows dense.1
  (⟨rows.1,updated.determinant,updated.adjugate⟩,original.2+dense.2+u.2+v.2+updated.work+rows.2+32*W)

theorem data {T m K j : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (labels : Fin T → Fin m → Fin K) (state : State j (m*(K-1)))
    (hj : j<m*(K-1)) (answer : GeneralPaperRayEndpoint.Answer T m K) :
    (run primitive W labels state hj answer).1=advance labels state hj answer := by
  simp only [run,GeneralPaperBlockerRowPrice.data,GeneralPaperBasisDenseBits.data,GeneralPaperBasisAssemblyBits.column_data,
    GeneralPaperBasisArrayPrice.prefix_data,GeneralPaperBasisCacheBits.determinant_data,GeneralPaperBasisCacheBits.adjugate_data,
    GeneralPaperBasisArrayPrice.append_data,advance]

def width (j d m H : ℕ) : ℕ := 2+binaryWordWidth (d+1)+binaryWordWidth (m+1)+GeneralPaperBasisCacheBitFacts.width j H (m+1)

theorem component_widths (j d m H : ℕ) :
    1+binaryWordWidth (d+1)≤width j d m H ∧ 1+binaryWordWidth (m+1)≤width j d m H ∧
    GeneralPaperBasisCacheBitFacts.width j H (m+1)≤width j d m H := by unfold width; omega

theorem work {T m j : ℕ} (model : RationalCostModel) (W k : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state)
    (answer : GeneralPaperRayEndpoint.Answer T m (prepare m k).K)
    (hContract : GeneralPaperRayEndpointSound.Contract (S:=S) dict v h ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity) answer)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W) :
    (run model.rat W dict.label state hj answer).2≤8192*((j+2)^2+m*((prepare m k).K-1)+m+j+3)*
      (W+model.rat (width j (m*((prepare m k).K-1)) m (prepare m k).H)) := by
  let d := m*((prepare m k).K-1)
  let Q := model.rat (width j d m (prepare m k).H)
  let original := GeneralPaperBlockerRowPrice.run W dict.label answer.blocker
  let dense := GeneralPaperBasisDenseBits.run model.rat W original.1
  let u := GeneralPaperBasisAssemblyBits.columnRun W state.rows (next hj)
  let p := GeneralPaperBasisArrayPrice.prefixRun (fun w => w) W dense.1 (Nat.le_of_lt hj)
  let updated := GeneralPaperBasisCacheBits.run model.rat W state.determinant state.adjugate u.1 p.1 (dense.1.coefficients.read (next hj))
  let rows := GeneralPaperBasisArrayPrice.appendRun (fun w => w) W state.rows dense.1
  have hw := component_widths j d m (prepare m k).H
  have hJ : binaryWordWidth (j+1)≤W := (binaryWordWidth_mono (show j+1≤d+1 by omega)).trans hDim
  have hJ2 : binaryWordWidth (j+2)≤W := (binaryWordWidth_mono (show j+2≤d+1 by omega)).trans hDim
  have hLen : original.1.terms.length≤m+1 := by rw [GeneralPaperBlockerRowPrice.data]; exact GeneralPaperBlockerRowPrice.length hm dict.label answer.blocker
  have hUnit : ∀ t∈original.1.terms,t.2.natAbs≤1 := by rw [GeneralPaperBlockerRowPrice.data]; exact GeneralPaperBasisAppendBits.blocker_unit_terms dict.label answer.blocker
  have hOriginal := GeneralPaperBlockerRowPrice.work W dict.label answer.blocker
  have hDense := GeneralPaperBasisDenseBits.work model.rat model.monotone W hW hDim original.1 hUnit
  change dense.2≤1024*(d+original.1.terms.length+1)*(W+model.rat (1+binaryWordWidth (d+1))+model.rat (1+binaryWordWidth original.1.terms.length)) at hDense
  have hPi := model.monotone hw.1
  have hPs := model.monotone ((Nat.add_le_add_left (binaryWordWidth_mono hLen) 1).trans hw.2.1)
  have hDense' : dense.2≤2048*(d+m+2)*(W+Q) := by
    apply hDense.trans
    have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 1024 (show d+original.1.terms.length+1≤d+m+2 by omega))
      (show W+model.rat (1+binaryWordWidth (d+1))+model.rat (1+binaryWordWidth original.1.terms.length)≤2*(W+Q) by omega)
    nlinarith only [hh]
  have hU := GeneralPaperBasisAssemblyBits.column_work W hW hJ state.rows (next hj)
  have hP := GeneralPaperBasisAppendBits.prefix_work W hW hJ dense.1 (Nat.le_of_lt hj)
  have hRows := GeneralPaperBasisAppendBits.append_work W hW hJ2 state.rows dense.1
  have hUpdate : updated.work≤4096*(j+2)^2*(W+Q) := by
    dsimp only [updated,p,u,dense,original]
    rw [GeneralPaperBasisDenseBits.data,GeneralPaperBlockerRowPrice.data,GeneralPaperBasisAssemblyBits.column_data,GeneralPaperBasisArrayPrice.prefix_data]
    exact (GeneralPaperBasisCacheStageBits.from_ray model W k hm dict v S h N hN betaN initialGrid state hj inv answer hContract hW hJ2).trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hw.2.2) W))
  change original.2+dense.2+u.2+p.2+updated.work+rows.2+32*W≤8192*((j+2)^2+d+m+j+3)*(W+Q)
  nlinarith only [hOriginal,hDense',hU,hP,hRows,hUpdate,Nat.zero_le (d*W),Nat.zero_le (m*W),Nat.zero_le (j*W),
    Nat.zero_le (d*Q),Nat.zero_le (m*Q),Nat.zero_le (j*Q),Nat.zero_le (j*j*Q),Nat.zero_le (j*j*W),Nat.zero_le Q]

end Blotto.GeneralPaperBasisAdvanceBits
