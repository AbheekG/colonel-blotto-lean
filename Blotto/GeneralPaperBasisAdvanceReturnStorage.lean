import Blotto.GeneralPaperBasisArrayStorage

/-! Complete native advance prefix/append and parent return. Actual old/
new states, original sparse/dense row, column/prefix and cached return
coexist with the checked array windows and every parent partial-work field.
Original endpoint/invariant facts derive all payload and work premises. -/
namespace Blotto.GeneralPaperBasisAdvanceReturnStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile rowFootprint rowProfile)
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def operandWidth (m k : ℕ) : ℕ := GeneralPaperSourceBasisCacheStorageRates.operandWidth m k
def rowCap (W m k : ℕ) : ℕ := rowProfile W (m*((prepare m k).K-1)) (m+1)
  (GeneralPaperEncodedBasisStorage.rowWork (m*((prepare m k).K-1)) m)
def price (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  let d := m*((prepare m k).K-1)
  8192*((d+2)^2+d+m+d+3)*(W+model.rat (operandWidth m k))
def metadataCap (model : RationalCostModel) (W m k : ℕ) : ℕ := 2*(m*((prepare m k).K-1))+2+3*price model W m k
def controls (j d W original dense u p cache rows total : ℕ) : List ℕ :=
  [j,d,original,dense,u,p,cache,rows,32*W,total,original+dense,original+dense+u,
    original+dense+u+p,original+dense+u+p+cache,original+dense+u+p+cache+rows]

def window {T m K j : ℕ} (model : RationalCostModel) (W prefixCopied appendCopied : ℕ)
    (labels : Fin T → Fin m → Fin K) (state : State j (m*(K-1))) (hj : j<m*(K-1))
    (answer : GeneralPaperRayEndpoint.Answer T m K) : ℕ :=
  let original := GeneralPaperBlockerRowPrice.run W labels answer.blocker
  let dense := GeneralPaperBasisDenseBits.run model.rat W original.1
  let u := GeneralPaperBasisAssemblyBits.columnRun W state.rows (next hj)
  let p := GeneralPaperBasisArrayPrice.prefixRun (fun w => w) W dense.1 (Nat.le_of_lt hj)
  let updated := GeneralPaperBasisCacheBits.run model.rat W state.determinant state.adjugate u.1 p.1 (dense.1.coefficients.read (next hj))
  let rows := GeneralPaperBasisArrayPrice.appendRun (fun w => w) W state.rows dense.1
  let result := GeneralPaperBasisAdvanceBits.run model.rat W labels state hj answer
  GeneralPaperEncodedBasisStorage.footprint W state+GeneralPaperEncodedBasisStorage.footprint W result.1+
    GeneralPaperStaticRowResidualStorage.rowFoot W (GeneralPaperStaticRowResidualStorage.termFoot W) original.1+
    rowFootprint W dense.1+arrayFootprint W integerBits u.1+arrayFootprint W integerBits p.1+
    integerBits updated.determinant+GeneralPaperBasisCacheStorage.matrixFootprint W updated.adjugate+
    GeneralPaperBasisArrayStorage.prefixWindow W prefixCopied dense.1 (Nat.le_of_lt hj)+
    GeneralPaperBasisArrayStorage.appendWindow W appendCopied state.rows dense.1+
    fields W (controls j (m*(K-1)) W original.2 dense.2 u.2 p.2 updated.work rows.2 result.2)+256*W

def profile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  let d := m*((prepare m k).K-1)
  let R := operandWidth m k
  3*GeneralPaperEncodedBasisStorage.paperProfile W m k+GeneralPaperStaticRowResidualStorage.rowProfile W m (prepare m k).K+
    rowCap W m k+2*arrayProfile W d R+GeneralPaperBasisArrayStorage.prefixProfile W d d R+
    GeneralPaperBasisArrayStorage.appendProfile W d d (rowCap W m k)+15*(natBits (metadataCap model W m k)+W)+288*W

theorem original_row {T m j : ℕ} (W k : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (hj : j≤m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (i : Fin j) : rowFootprint W (state.rows.read i)≤rowCap W m k :=
  GeneralPaperEncodedBasisStorage.row_bound W (m+1) (GeneralPaperEncodedBasisStorage.rowWork _ m) _
    (GeneralPaperBasisRowSize.coefficient hm dict v S h N betaN initialGrid hj state inv i)
    ⟨GeneralPaperBasisRowSize.rhs_entry hm dict v S h N betaN initialGrid hj state inv i false,
      GeneralPaperBasisRowSize.rhs_entry hm dict v S h N betaN initialGrid hj state inv i true⟩
    (GeneralPaperEncodedBasisStorage.original_work hm dict v S h N betaN initialGrid hj state inv i)

theorem advance_width (m k j : ℕ) (hj : j≤m*((prepare m k).K-1)) :
    GeneralPaperBasisAdvanceBits.width j (m*((prepare m k).K-1)) m (prepare m k).H≤operandWidth m k := by
  let T := (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
  have h := GeneralPaperBasisCacheStageBits.paper_width m k j (prepare m k).S T hj
  have hd : binaryWordWidth (m*((prepare m k).K-1)+1)≤binaryWordWidth ((prepare m k).d+m+(prepare m k).K+(prepare m k).S+T+2) := by
    apply binaryWordWidth_mono
    rw [←(GeneralPaperProxyParameters.data m k).2.2.1]
    omega
  have hm' := binaryWordWidth_mono (show m+1≤(prepare m k).d+m+(prepare m k).K+(prepare m k).S+T+2 by omega)
  unfold GeneralPaperBasisAdvanceBits.width operandWidth GeneralPaperSourceBasisCacheStorageRates.operandWidth
    GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth
  dsimp only [T] at h hd hm' ⊢
  ring_nf at h hd hm' ⊢
  omega

theorem from_ray {T m j : ℕ} (model : RationalCostModel) (W k prefixCopied appendCopied : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state)
    (answer : GeneralPaperRayEndpoint.Answer T m (prepare m k).K)
    (hContract : GeneralPaperRayEndpointSound.Contract (S:=S) dict v h ((betaN:ℚ)/(N:ℚ))
      (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
      (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity) answer)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W) :
    window model W prefixCopied appendCopied dict.label state hj answer≤profile model W m k := by
  let dim := m*((prepare m k).K-1)
  let R := operandWidth m k
  let original := GeneralPaperBlockerRowPrice.run W dict.label answer.blocker
  let dense := GeneralPaperBasisDenseBits.run model.rat W original.1
  let u := GeneralPaperBasisAssemblyBits.columnRun W state.rows (next hj)
  let p := GeneralPaperBasisArrayPrice.prefixRun (fun w => w) W dense.1 (Nat.le_of_lt hj)
  let updated := GeneralPaperBasisCacheBits.run model.rat W state.determinant state.adjugate u.1 p.1 (dense.1.coefficients.read (next hj))
  let rows := GeneralPaperBasisArrayPrice.appendRun (fun w => w) W state.rows dense.1
  let result := GeneralPaperBasisAdvanceBits.run model.rat W dict.label state hj answer
  let pureNext := advance dict.label state hj answer
  have hInv := GeneralPaperBasisStepSound.advance_valid dict v S h N hN betaN initialGrid state hj inv answer hContract
  have hOld := GeneralPaperEncodedBasisStorage.invariant_bound W k hm dict v S h N betaN initialGrid (Nat.le_of_lt hj) state inv
  have hNew := GeneralPaperEncodedBasisStorage.invariant_bound W k hm dict v S h N betaN initialGrid (Nat.succ_le_of_lt hj) pureNext hInv
  have hData : result.1=pureNext := GeneralPaperBasisAdvanceBits.data model.rat W dict.label state hj answer
  rw [←hData] at hNew
  have hDense : rowFootprint W dense.1≤rowCap W m k := by
    have hLast : pureNext.rows.read (GeneralPaperBasisAppendIndex.encode j none)=dense.1 := by
      dsimp only [pureNext,dense,original]
      rw [GeneralPaperBasisDenseBits.data,GeneralPaperBlockerRowPrice.data]
      exact GeneralPaperBasisAppendRows.last_read _ _
    rw [←hLast]
    exact original_row W k hm dict v S h N betaN initialGrid (Nat.succ_le_of_lt hj) pureNext hInv _
  have hSparse := GeneralPaperBlockerRowConstructionStorage.output_bound W hm dict.label answer.blocker
  have hCache : integerBits updated.determinant+GeneralPaperBasisCacheStorage.matrixFootprint W updated.adjugate≤
      GeneralPaperEncodedBasisStorage.footprint W result.1 := by
    change _+_≤arrayFootprint W (rowFootprint W) rows.1+integerBits updated.determinant+
      GeneralPaperBasisCacheStorage.matrixFootprint W updated.adjugate+32*W
    omega
  have hCacheOwner := hCache.trans hNew
  have hBound := GeneralPaperBasisAdvanceSize.from_ray k hm dict v S h N betaN initialGrid state hj inv answer hContract
  have hWidth := advance_width m k j (Nat.le_of_lt hj)
  have hMR := (GeneralPaperBasisAdvanceBits.component_widths j dim m (prepare m k).H).2.1.trans hWidth
  have hCoeff (i) : integerBits (dense.1.coefficients.read i)≤R := by
    have hLast : pureNext.rows.read (GeneralPaperBasisAppendIndex.encode j none)=dense.1 := by
      dsimp only [pureNext,dense,original]
      rw [GeneralPaperBasisDenseBits.data,GeneralPaperBlockerRowPrice.data]
      exact GeneralPaperBasisAppendRows.last_read _ _
    have hb := GeneralPaperBasisRowSize.coefficient hm dict v S h N betaN initialGrid (Nat.succ_le_of_lt hj) pureNext hInv
      (GeneralPaperBasisAppendIndex.encode j none) i
    rw [hLast] at hb
    exact (Nat.add_le_add_left (binaryWordWidth_mono hb) 1).trans hMR
  have hU := GeneralPaperEncodedBasisStorage.array_bound W R integerBits u.1 (by
    intro i
    rw [GeneralPaperBasisAssemblyBits.column_data]
    exact (Nat.add_le_add_left (binaryWordWidth_mono (hBound.1 i)) 1).trans hMR)
  have hP := GeneralPaperEncodedBasisStorage.array_bound W R integerBits p.1 (by
    intro i
    rw [GeneralPaperBasisArrayPrice.prefix_data]
    dsimp only [dense,original]
    rw [GeneralPaperBasisDenseBits.data,GeneralPaperBlockerRowPrice.data]
    exact (Nat.add_le_add_left (binaryWordWidth_mono (hBound.2.1 i)) 1).trans hMR)
  have hUD := hU.trans (show arrayProfile W j R≤arrayProfile W dim R by unfold arrayProfile; gcongr)
  have hPD := hP.trans (show arrayProfile W j R≤arrayProfile W dim R by unfold arrayProfile; gcongr)
  have hJ : binaryWordWidth (j+1)≤W := (binaryWordWidth_mono (show j+1≤dim+1 by omega)).trans hDim
  have hJ2 : binaryWordWidth (j+2)≤W := (binaryWordWidth_mono (show j+2≤dim+1 by omega)).trans hDim
  have hPrefix := GeneralPaperBasisArrayStorage.prefix_bound W prefixCopied R dense.1 (Nat.le_of_lt hj) hCoeff hW hJ
  have hAppend := GeneralPaperBasisArrayStorage.append_bound W appendCopied (rowCap W m k) state.rows dense.1
    (original_row W k hm dict v S h N betaN initialGrid (Nat.le_of_lt hj) state inv) hDense hW hJ2
  have hPrefixD := hPrefix.trans (show GeneralPaperBasisArrayStorage.prefixProfile W j dim R≤GeneralPaperBasisArrayStorage.prefixProfile W dim dim R by
    unfold GeneralPaperBasisArrayStorage.prefixProfile GeneralPaperBasisArrayStorage.prefixCap GeneralPaperBasisArrayStorage.callbackProfile
      GeneralPaperBasisArrayStorage.callbackCap GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
      GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap natBits
    gcongr)
  have hAppendD := hAppend.trans (show GeneralPaperBasisArrayStorage.appendProfile W j dim (rowCap W m k)≤GeneralPaperBasisArrayStorage.appendProfile W dim dim (rowCap W m k) by
    unfold GeneralPaperBasisArrayStorage.appendProfile GeneralPaperBasisArrayStorage.appendCap GeneralPaperBasisArrayStorage.callbackProfile
      GeneralPaperBasisArrayStorage.callbackCap GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
      GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap natBits
    gcongr)
  have hWork := (GeneralPaperBasisAdvanceBits.work model W k hm dict v S h N hN betaN initialGrid state hj inv answer hContract hW hDim).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hWidth) W))
  have hWorkD : result.2≤price model W m k := hWork.trans (by unfold price; dsimp only; gcongr)
  have hShape : result.2=original.2+dense.2+u.2+p.2+updated.work+rows.2+32*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W m k))
    (controls j dim W original.2 dense.2 u.2 p.2 updated.work rows.2 result.2) (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at ha
      unfold metadataCap
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals dsimp only [dim] at *; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤15*(natBits (metadataCap model W m k)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [dim,R,original,dense,u,p,updated,rows,result] at hNew hDense hCacheOwner hUD hPD hPrefixD hAppendD hf
  omega

end Blotto.GeneralPaperBasisAdvanceReturnStorage
