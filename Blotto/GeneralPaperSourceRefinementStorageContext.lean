import Blotto.GeneralPaperRayParametricRefinementCoverage

/-! Actual source-state instantiation of the complete refinement window.
The basis invariant supplies native point/direction/budget bounds; the
actual grid and determinant cache supply every sorted-array query height,
common-lattice width, native query price and local owner/predicate window.
No height, price, query-space or size oracle enters the executable code. -/
namespace Blotto.GeneralPaperSourceRefinementStorageContext
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def AtBound {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (limit : ℕ) (lo hi : ℚ) (points : List ℚ) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
  ∀ phase : ∀ t,GeneralPaperRayQueryStorage.Phase model W inputs.matrix x w t (prepare m k).S,
    ∀ p : GeneralPaperCrossingRefinementStorage.Phase,
      owner+GeneralPaperCrossingRefinementStorage.window model W
        (GeneralPaperRayPredicateBits.run model W inputs.matrix x w (prepare m k).S prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)))
        (fun t => owner+GeneralPaperRayPredicateStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
          ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) t (phase t)) lo hi points p≤
        limit

def BatchBound {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (lo hi : ℚ) (points : List ℚ) : Prop :=
  AtBound model W k prep inputs state hj (GeneralPaperSourceCrossingRefinementRates.reservation model W m k) lo hi points

theorem at_bound_mono {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (B C : ℕ) (hBC : B≤C)
    (lo hi : ℚ) (points : List ℚ) (h : AtBound model W k prep inputs state hj B lo hi points) :
    AtBound model W k prep inputs state hj C lo hi points := by
  intro phase p
  exact (h phase p).trans hBC

def Ready {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let R := GeneralPaperRayUniformSize.width (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
    m 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs
  ∀ lo hi points,0≤lo → lo≤hi → hi≤1 → RationalHeight lo R → RationalHeight hi R →
    points.length≤((prepare m k).S+1)*((prepare m k).K*(prepare m k).K) →
    (∀ t∈points,RationalHeight t R) → BatchBound model W k prep inputs state hj lo hi points

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ j (hj : j<m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1))),
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state →
      Ready model W k prep inputs state hj := by
  dsimp only
  intro j hj state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let R := GeneralPaperRayUniformSize.width (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
    m 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs
  let H := GeneralPaperSourceRayStorageWidth.width m k
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
  have hOwners := GeneralPaperSourceRayQueryOwners.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim j hj state inv
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hD := Int.natAbs_pos.mpr inv.nonzero
  have hx := GeneralPaperRayAnchorBound.point k prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N hN
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv
  have hw := GeneralPaperRayAnchorBound.direction k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv (next hj) rfl
  have hBeta := GeneralPaperRayAnchorBound.budget inputs.controls.N hN state.determinant.natAbs inputs.betaN
  have hDiv : state.determinant.natAbs∣inputs.controls.N*state.determinant.natAbs := ⟨inputs.controls.N,by ring⟩
  have hCache := (GeneralPaperBasisCacheSize.cache_H k hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv).1
  have hAux : inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k :=
    GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  have hRoot := GeneralPaperSourceRayStorageWidth.root_bound m k j b hb reciprocal state.determinant.natAbs
    inputs.betaN.natAbs (Nat.le_of_lt hj) hCache hAux
  change R≤GeneralPaperSourceRayStorageWidth.rootWidth m k at hRoot
  have hRH : R≤H := by dsimp only [H]; unfold GeneralPaperSourceRayStorageWidth.width; omega
  have hCompare : R+R≤H := by dsimp only [H]; unfold GeneralPaperSourceRayStorageWidth.width; omega
  have hThreshold : prep.threshold≤(prepare m k).S := GeneralPaperTransferPreparation.threshold_le _ _ _ _ _ _ _ _
  have hScores : ∀ a l,((inputs.matrix.read a).read l).1≤(prepare m k).S := by
    intro a l
    rw [GeneralPaperSharedBasisInputs.matrix_eq]
    erw [GeneralPaperScoreMatrixWork.matrix_data (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
      (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)]
    simp only [FixedArrayTable.read_ofFn]
    convert GeneralPaperEncodedScoreMatrixStorage.score_bound v (prepare m k).S
      (GeneralPaperScoreScaleParameters.labels_positive m k) a l using 1
    rfl
  intro lo hi points hLo ho hHi hl hh hn hp phase p
  have query_bounds (t : ℚ) (ht : t∈GeneralPaperRaySortedCrossings.ordered lo hi points) :
      0≤t ∧ t≤1 ∧ RationalHeight t R := by
    have hInterval := GeneralPaperRaySortedCrossings.ordered_bound lo hi ho points t ht
    exact ⟨hLo.trans hInterval.1,hInterval.2.trans hHi,
      GeneralPaperCrossingSearchStorage.ordered_height lo hi points R hl hh hp t ht⟩
  have hQuery (t : ℚ) (ht : t∈GeneralPaperRaySortedCrossings.ordered lo hi points) :
      (GeneralPaperRayPredicateBits.run model W inputs.matrix x w (prepare m k).S prep.threshold
        ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) t).2≤
        GeneralPaperCrossingSearchStorage.nativePrice model W m (prepare m k).K (prepare m k).S H := by
    have hbq := query_bounds t ht
    have hc := GeneralPaperRayPredicateBits.work model W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
      1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs R (Nat.mul_pos hN hD) hDiv inputs.matrix x w hx hw _ hBeta
      t ⟨hbq.1,hbq.2.1⟩ hbq.2.2 (prepare m k).S prep.threshold hW hK hM hIndex
    apply hc.trans
    change 4096*(m+1)*((prepare m k).K+1)*((prepare m k).S+1)*(W+model.rat (1+2*(R+R)))≤_
    unfold GeneralPaperCrossingSearchStorage.nativePrice
    gcongr
    apply model.monotone
    omega
  have hSpace (t : ℚ) (ht : t∈GeneralPaperRaySortedCrossings.ordered lo hi points) :
      owner+GeneralPaperRayPredicateStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
        ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) t (phase t)≤GeneralPaperSourceEndpointOwnerStorage.profile model W m k := by
    have hbq := query_bounds t ht
    have hT : RationalHeight t (2*GeneralPaperSourceRayStorageWidth.rootWidth m k+3) := (hbq.2.2.mono hRoot).mono (by omega)
    have hCommon := GeneralPaperSourceRayStorageWidth.probe_word m k j b hb reciprocal state.determinant.natAbs
      inputs.betaN.natAbs (Nat.le_of_lt hj) hCache hAux t hT
    have hPred := GeneralPaperRayPredicateStorage.bounded model W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
      1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs R (prepare m k).S prep.threshold H (Nat.mul_pos hN hD) hDiv
      inputs.matrix hScores x w hx hw _ hBeta t ⟨hbq.1,hbq.2.1⟩ hbq.2.2 hCommon hCompare hThreshold hW hK hM hIndex (phase t)
    exact Nat.add_le_add hOwners hPred
  have hWhole : GeneralPaperCrossingRefinementStorage.window model W
      (GeneralPaperRayPredicateBits.run model W inputs.matrix x w (prepare m k).S prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)))
      (fun t => owner+GeneralPaperRayPredicateStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
        ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) t (phase t)) lo hi points p≤
      GeneralPaperSourceCrossingRefinementRates.sourceProfile model W m k :=
    GeneralPaperCrossingRefinementStorage.all_phases model W _ H _ _ _ _ lo hi points hn (hl.mono hRH) (hh.mono hRH)
      (fun t ht => (hp t ht).mono hRH) hW hBatch hQuery hSpace p
  have hOuter : owner≤GeneralPaperSourceEndpointOwnerStorage.profile model W m k :=
    hOwners.trans (by unfold GeneralPaperSourceEndpointOwnerStorage.profile; omega)
  exact (Nat.add_le_add hOuter hWhole).trans (by unfold GeneralPaperSourceCrossingRefinementRates.reservation; omega)

end Blotto.GeneralPaperSourceRefinementStorageContext
