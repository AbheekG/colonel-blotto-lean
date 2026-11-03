import Blotto.GeneralPaperRayPredicateStorage

/-! Retained original score matrix and actual native packed point/direction
arrays during a query. Native preparation-return work counters are encoded.
The basis record, original grid and enclosing source/compiler owners remain
outside this window and must be counted once by their enclosing scopes. -/
namespace Blotto.GeneralPaperSourceRayQueryOwners
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedScoreMatrixStorage
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 8192

def preparationPrice (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  16384*(m*((prepare m k).K-1)+1)^2*(W+model.rat (128*GeneralPaperSourceRayStorageWidth.width m k))

def window {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : ℕ :=
  let point := GeneralPaperBasisPreparationBits.point model.rat W inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid
  let direction := GeneralPaperBasisPreparationBits.direction model.rat W state.determinant state.adjugate state.rows (next hj)
  matrixFootprint W inputs.matrix+GeneralPaperEncodedRationalRows.rowFootprint W point.point+
    GeneralPaperEncodedRationalRows.rowFootprint W direction.velocity+
    fields W [j,m*((prepare m k).K-1),point.work,direction.work,point.work+direction.work]+256*W

def profile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  matrixProfile W m (prepare m k).K (prepare m k).S (GeneralPaperSourceScoreHeights.anchorHeight m k)+
    2*GeneralPaperEncodedRationalRows.rowProfile W (m*((prepare m k).K-1)) (GeneralPaperSourceRayStorageWidth.width m k)+
    5*(natBits (m*((prepare m k).K-1)+1+preparationPrice model W m k)+W)+32*W+256*W

theorem preparation_width (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    GeneralPaperBasisPreparationWidths.envelope (m*((prepare m k).K-1)) (m+1)
      (GeneralPaperInitializerSelectedControls.controls m k b reciprocal).N (prepare m k).H
      (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)≤128*GeneralPaperSourceRayStorageWidth.width m k := by
  have hp := GeneralPaperBasisPreparationWidths.paper_envelope m k
    (GeneralPaperInitializerSelectedControls.controls m k b reciprocal).N (prepare m k).S
    (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
  have hn := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  unfold GeneralPaperSourceRayStorageWidth.width GeneralPaperSourceRayStorageWidth.rootWidth
  nlinarith only [hp,hn,Nat.zero_le (GeneralPaperSourceRayStorageWidth.gridWord m k),
    Nat.zero_le (((prepare m k).d+2)*binaryWordWidth (m+3)),
    Nat.zero_le (binaryWordWidth ((prepare m k).d+m+(prepare m k).K+(prepare m k).S+
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+2))]

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ j (hj : j<m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1))),
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state →
      window model W k inputs state hj≤profile model W m k := by
  dsimp only
  intro j hj state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let point := GeneralPaperBasisPreparationBits.point model.rat W inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid
  let direction := GeneralPaperBasisPreparationBits.direction model.rat W state.determinant state.adjugate state.rows (next hj)
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hD := Int.natAbs_pos.mpr inv.nonzero
  have hx := GeneralPaperRayAnchorBound.point k prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N hN
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv
  have hw := GeneralPaperRayAnchorBound.direction k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv (next hj) rfl
  have hCache := (GeneralPaperBasisCacheSize.cache_H k hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv).1
  have hAux : inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k :=
    GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  have hRoot := GeneralPaperSourceRayStorageWidth.root_bound m k j b hb reciprocal state.determinant.natAbs
    inputs.betaN.natAbs (Nat.le_of_lt hj) hCache hAux
  have hRoot' : GeneralPaperSourceRayStorageWidth.rootWidth m k≤GeneralPaperSourceRayStorageWidth.width m k := by
    unfold GeneralPaperSourceRayStorageWidth.width
    omega
  have hPoint := GeneralPaperRayOperandStorageHeight.packed_bound W (GeneralPaperSourceRayStorageWidth.width m k) point.point (by
    intro a
    dsimp only [point]
    rw [GeneralPaperBasisPreparationBits.point_data]
    exact (GeneralPaperRayOperandStorageHeight.point (E:=state.determinant.natAbs) (m:=m)
      (V:=j*(prepare m k).H*(m+1)+1) (P:=inputs.betaN.natAbs) (Nat.mul_pos hN hD) (hx a)).mono (hRoot.trans hRoot'))
  have hDirection := GeneralPaperRayOperandStorageHeight.packed_bound W (GeneralPaperSourceRayStorageWidth.width m k) direction.velocity (by
    intro a
    dsimp only [direction]
    rw [GeneralPaperBasisPreparationBits.direction_data]
    exact (GeneralPaperRayOperandStorageHeight.direction (D:=inputs.controls.N*state.determinant.natAbs) (m:=m)
      (X:=1) (P:=inputs.betaN.natAbs) hD (hw a)).mono (hRoot.trans hRoot'))
  have hMatrix : matrixFootprint W inputs.matrix≤matrixProfile W m (prepare m k).K (prepare m k).S
      (GeneralPaperSourceScoreHeights.anchorHeight m k) := by
    rw [GeneralPaperSharedBasisInputs.matrix_eq]
    erw [GeneralPaperScoreMatrixWork.matrix_data (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
      (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)]
    apply matrix_bound
    · intro a l
      simp only [FixedArrayTable.read_ofFn]
      convert GeneralPaperEncodedScoreMatrixStorage.score_bound v (prepare m k).S
        (GeneralPaperScoreScaleParameters.labels_positive m k) a l using 1
      rfl
    · intro a l
      simp only [FixedArrayTable.read_ofFn]
      exact GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal a l
  have hWork := (GeneralPaperBasisPreparationStageBits.actual_source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hDim j hj state inv).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left
      (model.monotone (preparation_width m k b hb reciprocal)) W))
  change point.work+direction.work≤preparationPrice model W m k at hWork
  have hf := fields_bound W (natBits (m*((prepare m k).K-1)+1+preparationPrice model W m k))
    [j,m*((prepare m k).K-1),point.work,direction.work,point.work+direction.work] (by
      intro n hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤
    5*(natBits (m*((prepare m k).K-1)+1+preparationPrice model W m k)+W)+32*W at hf
  change matrixFootprint W inputs.matrix+GeneralPaperEncodedRationalRows.rowFootprint W point.point+
    GeneralPaperEncodedRationalRows.rowFootprint W direction.velocity+
    fields W [j,m*((prepare m k).K-1),point.work,direction.work,point.work+direction.work]+256*W≤_
  unfold profile
  omega

end Blotto.GeneralPaperSourceRayQueryOwners
