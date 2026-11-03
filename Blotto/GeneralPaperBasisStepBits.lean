import Blotto.GeneralPaperBasisBitEnvelope

/-! Complete native basis stage in the declared bit model. Fresh point/
velocity, rational budget construction, full ray search and conditional
original-row extension are each executed and charged once. Native invariants
derive every success/price premise; all returned states agree exactly.
-/
namespace Blotto.GeneralPaperBasisStepBits
open RationalOrderCell GeneralPaperBasisState GeneralPaperBasisStoredProducts GeneralPaperBasisInvariant
open GeneralPaperBasisOriginalDirection GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def run {T m K j : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (state : State j (m*(K-1))) (hj : j<m*(K-1)) :
    Option (State (j+1) (m*(K-1))) × ℕ :=
  let point := GeneralPaperBasisPreparationBits.point model.rat W N betaN state.determinant state.adjugate state.rows initialGrid
  let velocity := GeneralPaperBasisPreparationBits.direction model.rat W state.determinant state.adjugate state.rows (next hj)
  let budget := GeneralPaperBasisBudgetBits.run model.rat W N betaN
  let ray := GeneralPaperEndpointBits.run model W labels matrix S h budget.1 (reader point.point) (reader velocity.velocity)
  match ray.1 with
  | none => (none,point.work+velocity.work+budget.2+ray.2+24*W)
  | some answer =>
    let updated := GeneralPaperBasisAdvanceBits.run model.rat W labels state hj answer
    (some updated.1,point.work+velocity.work+budget.2+ray.2+updated.2+32*W)

theorem data {T m K j : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (state : State j (m*(K-1))) (hj : j<m*(K-1)) :
    (run model W labels matrix S h N betaN initialGrid state hj).1=step labels matrix S h N betaN initialGrid state hj := by
  unfold run step
  simp only [GeneralPaperBasisPreparationBits.point_data,GeneralPaperBasisPreparationBits.direction_data,GeneralPaperBasisBudgetBits.data,GeneralPaperEndpointBits.data]
  cases GeneralPaperRayEndpoint.prepared labels matrix S h ((betaN:ℚ)/(N:ℚ))
    (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point)
    (reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity)
  · rfl
  · simp only [GeneralPaperBasisAdvanceBits.data,Option.map_some]

def profile (T m K S W Q : ℕ) : ℕ := 131072*(m*(K-1)+1)^2*(W+Q)+GeneralPaperEndpointPriceControl.profile T m K S W Q

theorem work {T m j : ℕ} (model : RationalCostModel) (W k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_of_lt hj) state)
    (hBeta : betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k) (hGrid : ∀ i,(initialGrid.read i).natAbs≤N)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth (S+4)≤W) :
    (run model W dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1 S h N betaN initialGrid state hj).2≤
      profile T m (prepare m k).K S W (model.rat (GeneralPaperBasisBitEnvelope.width m k N S T)) := by
  let d := m*((prepare m k).K-1)
  let Q := model.rat (GeneralPaperBasisBitEnvelope.width m k N S T)
  let matrix := (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1
  let point := GeneralPaperBasisPreparationBits.point model.rat W N betaN state.determinant state.adjugate state.rows initialGrid
  let velocity := GeneralPaperBasisPreparationBits.direction model.rat W state.determinant state.adjugate state.rows (next hj)
  let budget := GeneralPaperBasisBudgetBits.run model.rat W N betaN
  let ray := GeneralPaperEndpointBits.run model W dict.label matrix S h budget.1 (reader point.point) (reader velocity.velocity)
  have hI := GeneralPaperBasisBitEnvelope.index_capacities m k W hm hDim
  have hw := GeneralPaperBasisBitEnvelope.components m k j N S T (Nat.le_of_lt hj)
  have hPrep := (GeneralPaperBasisPreparationStageBits.from_invariant model W k hm dict v S h N _ betaN initialGrid state
    (Nat.le_of_lt hj) inv hBeta hGrid (next hj) hW hI.1).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hw.1) W))
  have hBudget : budget.2≤24*W+4*Q := by
    have hh := GeneralPaperBasisBudgetBits.work model.rat model.monotone W N _ betaN hBeta
    have hp := model.monotone hw.2.2
    change budget.2≤_ at hh
    change _≤Q at hp
    omega
  have hc := GeneralPaperBasisCacheSize.cache_H k hm dict v S h N betaN initialGrid (Nat.le_of_lt hj) state inv
  have hK : 0<(prepare m k).K := GeneralPaperScoreScaleParameters.labels_positive m k
  have hRay : ray.2≤GeneralPaperEndpointPriceControl.profile T m (prepare m k).K S W Q := by
    dsimp only [ray,point,velocity,budget]
    rw [GeneralPaperBasisPreparationBits.point_data,GeneralPaperBasisPreparationBits.direction_data,GeneralPaperBasisBudgetBits.data]
    exact (GeneralPaperBasisEndpointPrice.bits model W k hm scoreDepth dict v hK S h N hN hCap betaN initialGrid state hj inv
      hW hI.2.1 hI.2.2 hIndex hBatch hFinal).trans
      (GeneralPaperBasisBitEnvelope.endpoint_profile_mono _ _ _ _ _ _ _ (model.monotone
        (GeneralPaperBasisBitEnvelope.ray_width m k j N state.determinant.natAbs betaN.natAbs S T (Nat.le_of_lt hj) hc.1 hBeta)))
  obtain ⟨a,ha⟩ := next_velocity state.determinant state.adjugate state.rows (next hj) rfl
  have hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h
      (((betaN:ℚ)/(N:ℚ):ℚ):ℝ)
      (fun b => (reader (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point b:ℝ)) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,reader,GeneralPaperBasisFreshPointSound.values] using inv.feasible
  obtain ⟨answer,hNative,hContract⟩ := GeneralPaperRayEndpointSound.endpoint_sound scoreDepth dict v hK hCap h ((betaN:ℚ)/(N:ℚ)) _ _ hStart a ha
  have hRayData : ray.1=some answer := by
    dsimp only [ray,point,velocity,budget]
    rw [GeneralPaperBasisPreparationBits.point_data,GeneralPaperBasisPreparationBits.direction_data,GeneralPaperBasisBudgetBits.data,GeneralPaperEndpointBits.data]
    exact hNative
  have hAdvance := ((GeneralPaperBasisAdvanceBits.work model W k hm dict v S h N hN betaN initialGrid state hj inv answer hContract hW hI.1).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hw.2.1) W))).trans
    (GeneralPaperBasisBitEnvelope.advance_scale j d m W Q (Nat.le_of_lt hj) (GeneralPaperBasisBitEnvelope.dimension_bounds m k hm).1)
  change point.work+velocity.work≤16384*(d+1)^2*(W+Q) at hPrep
  change (GeneralPaperBasisAdvanceBits.run model.rat W dict.label state hj answer).2≤65536*(d+1)^2*(W+Q) at hAdvance
  rw [run,hRayData]
  change point.work+velocity.work+budget.2+ray.2+(GeneralPaperBasisAdvanceBits.run model.rat W dict.label state hj answer).2+32*W≤profile T m (prepare m k).K S W Q
  unfold profile
  change _≤131072*(d+1)^2*(W+Q)+GeneralPaperEndpointPriceControl.profile T m (prepare m k).K S W Q
  nlinarith only [hPrep,hBudget,hRay,hAdvance,Nat.zero_le (d*d*W),Nat.zero_le (d*W),Nat.zero_le (d*d*Q),Nat.zero_le (d*Q),Nat.zero_le Q]

end Blotto.GeneralPaperBasisStepBits
