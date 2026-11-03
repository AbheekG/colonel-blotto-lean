import Blotto.GeneralPaperSourceFieldValuesStorageRates
import Blotto.GeneralPaperPreparedBitCompilerPair

/-! Actual prepared bit-pair parent. Both full shared records, original
ratio and weights, classifier/control/alphabet, complete materialized grid,
value construction, both source callers and selected compiler coexist.
Every observer is erased; the native once-only driver is unchanged. -/
namespace Blotto.GeneralPaperSourcePreparedPairOwners
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint GeneralPaperEncodedScalarStorage
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

noncomputable def front (W m k : ℕ) (b : ℚ) : ℕ :=
  GeneralPaperClassifierResultStorage.frontFootprint W
    ((GeneralPaperPrecallCachePrice.specification m k,alphabet m k),GeneralPaperProxyClassifier.classify m k (b:ℝ))

noncomputable def run {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℚ) :=
  GeneralPaperPreparedBitCompilerPair.run model W k Qv hQv weights hp hs (GeneralPaperPrecallCachePrice.specification m k) (grid_positive m k)
    (alphabet m k) (GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv) rfl
    (GeneralPaperProxyClassifier.classify m k (b:ℝ)) (GeneralPaperProxyClassifier.classify m k (b:ℝ)).choice.proxy.value
    (GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights 1 (GeneralPaperProxyClassifier.classify m k (b:ℝ)).choice.proxy.value)
    (GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights (GeneralPaperProxyClassifier.classify m k (b:ℝ)).choice.proxy.value 1) rfl rfl rfl rfl
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)

theorem checked {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hs : ∑ j,weights.read j=Qv) (b : ℚ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    (GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) reciprocal).1.2=true :=
  GeneralPaperRetainedSourceColumnBits.actual_checked model W k Qv hm hQv (b:ℝ) (by exact_mod_cast hb) reciprocal _ rfl weights hs _ rfl rfl

theorem run_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℚ) (hm : 0<m) (hb : 0<b ∧ b<1) :
    run model W k Qv hQv weights hp hs b=
      ((GeneralPaperSourceCompilerPairStorage.run model W k Qv hQv weights hp hs (b:ℝ)).1,
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).2+
        (GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) false).2+
        (GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) true).2+
        (GeneralPaperSourceCompilerPairStorage.run model W k Qv hQv weights hp hs (b:ℝ)).2+128*W) := by
  have hr := checked model W k Qv hm hQv weights hs b hb false
  have hpoor := checked model W k Qv hm hQv weights hs b hb true
  have hrc := GeneralPaperSourceColumnCallerStorage.native_columns model W k Qv weights (b:ℝ) false
  have hpc := GeneralPaperSourceColumnCallerStorage.native_columns model W k Qv weights (b:ℝ) true
  let f := fun cols : GeneralPaperOriginalDrawEquilibrium.Columns (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K =>
    GeneralPaperRetainedCompilerPairBits.run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H (prepare m k).Qg
      (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperProxyClassifier.classify m k (b:ℝ))
      (GeneralPaperProxyClassifier.classify m k (b:ℝ)).choice.proxy.value
      (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1 cols
  have hCols := congrArg₂ (fun rr pp => (⟨rr,pp⟩ : GeneralPaperOriginalDrawEquilibrium.Columns
    (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)) hrc hpc
  have hCompile := congrArg f hCols
  unfold run GeneralPaperPreparedBitCompilerPair.run
  change (if (GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) false).1.2 &&
      (GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) true).1.2 then _ else _)=_
  rw [hr,hpoor]
  simp only [Bool.and_self,ite_true]
  exact congrArg (fun out => (out.1,
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).2+
    (GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) false).2+
    (GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) true).2+out.2+128*W)) hCompile

noncomputable def price (model : RationalCostModel) (C d W m k Qv : ℕ) : ℕ :=
  GeneralPaperRetainedFieldValuesStorage.price model W m Qv+
    2*GeneralPaperRetainedSourceColumnCallerStorage.price W (GeneralPaperSourceRowsCallerStorageRates.sourceWorkCap C d W m k Qv)
      (GeneralPaperSourceColumnCallerStorageRates.unitPrice model W m k)+
    GeneralPaperSourceCompilerPairStorageRates.price model W m k Qv+128*W
noncomputable def metadataCap (model : RationalCostModel) (C d W m k Qv : ℕ) : ℕ :=
  m+k+Qv+(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+(prepare m k).K+price model C d W m k Qv+W+1

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℚ) (cursor : ℕ) (hc : cursor≤m)
    (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K) : ℕ :=
  let values := GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs
  let rich := GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) false
  let poor := GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) true
  let compiled := GeneralPaperSourceCompilerPairStorage.run model W k Qv hQv weights hp hs (b:ℝ)
  let result := run model W k Qv hQv weights hp hs b
  rationalWordWidth b+GeneralPaperEncodedNatArray.footprint W weights+front W m k b+
    GeneralPaperMaterializedCacheStorage.gridFootprint W (GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv)+
    GeneralPaperSourceRowsCallerStorage.window model W k Qv weights (b:ℝ) false+
    GeneralPaperSourceRowsCallerStorage.window model W k Qv weights (b:ℝ) true+
    GeneralPaperRetainedFieldValuesStorage.window model W Qv hQv weights hp hs cursor hc+
    GeneralPaperSourceColumnCallerStorage.window model W k Qv weights (b:ℝ) false+
    GeneralPaperSourceColumnCallerStorage.window model W k Qv weights (b:ℝ) true+
    GeneralPaperSourceCompilerPairStorage.window model W k Qv hQv weights hp hs (b:ℝ) outer ho inner hi+
    GeneralPaperRetainedCompilerPairStorage.optionFoot W result.1+
    fields W [m,k,Qv,(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows,(prepare m k).K,cursor,
      values.2,rich.2,poor.2,compiled.2,result.2,values.2+rich.2,values.2+rich.2+poor.2,values.2+rich.2+poor.2+compiled.2,128*W,64*W,
      GeneralPaperFinalStaticLoopStorage.bit rich.1.2,GeneralPaperFinalStaticLoopStorage.bit poor.1.2,
      GeneralPaperFinalStaticLoopStorage.bit (rich.1.2 && poor.1.2),GeneralPaperFinalStaticLoopStorage.bit result.1.isSome]+192*W

noncomputable def profile (model : RationalCostModel) (C d W m k Qv B : ℕ) : ℕ :=
  (1+2*B)+(m*(natBits Qv+W)+32*W)+GeneralPaperClassifierResultStorage.frontProfile W m k+
    3*GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv+
    GeneralPaperRetainedFieldValuesStorage.profile model W m Qv+
    2*GeneralPaperSourceColumnCallerStorageRates.sourceProfile model C d W m k Qv+
    2*GeneralPaperSourceCompilerPairStorageRates.sourceProfile model W m k Qv+
    20*(natBits (metadataCap model C d W m k Qv)+W)+224*W

theorem grid_bound {m : ℕ} (C d W k Qv : ℕ) (weights : FixedArrayTable m ℕ) (hs : ∑ j,weights.read j=Qv)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    GeneralPaperMaterializedCacheStorage.gridFootprint W (GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv)≤
      GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv := by
  let upper := GeneralPaperFastRationalMajorant.model C d
  let a := alphabet m k
  let Bc := ownBudget m k (b:ℝ) false
  let Br := opposingBudget m k (b:ℝ) false
  let t := a.lambda+1
  let F := GeneralPaperSourceInputEnvelopeStorage.inputCap W m Qv t
  have hBc := GeneralPaperSourceBudgetWidths.own_height m k (b:ℝ) (by exact_mod_cast hb) false
  have hBr := GeneralPaperSourceBudgetWidths.opposing_height m k (b:ℝ) (by exact_mod_cast hb) false
  have hF := GeneralPaperSourceInputEnvelopeStorage.input_bound W Qv t weights hs Bc Br hBc hBr
  have hP := GeneralPaperSourceInputEnvelopeStorage.prepared_bound upper W k Qv t F (1+2*t) (1+2*t) a weights Bc Br hF
    (rationalWordWidth_of_height hBc) (rationalWordWidth_of_height hBr)
  have hGrid : GeneralPaperMaterializedCacheStorage.gridProfile W m a.lambda k Qv≤
      GeneralPaperPreparedReferenceCapacity.profile upper W k Qv 0 t t a weights Bc Br := by
    unfold GeneralPaperPreparedReferenceCapacity.profile GeneralPaperPrecallResidentStorage.residentProfile
      GeneralPaperPreparationResidentStorage.residentProfile
    omega
  have hE : GeneralPaperSourceInputEnvelopeStorage.profile upper W m k Qv t a F (1+2*t) (1+2*t)≤
      GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv := by
    unfold GeneralPaperSourceRowsCallerStorageRates.sourceProfile GeneralPaperRetainedSourceRowsCallerStorage.profile
    dsimp only [upper,t,F,a]
    omega
  exact (GeneralPaperMaterializedCacheStorage.grid_native W m a.lambda k Qv).trans (hGrid.trans (hP.trans hE))

theorem shared_inputs {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℚ) (cursor : ℕ) (hc : cursor≤m)
    (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K) :
    rationalWordWidth b+GeneralPaperEncodedNatArray.footprint W weights+front W m k b+
      GeneralPaperMaterializedCacheStorage.gridFootprint W (GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv)+
      GeneralPaperEncodedSharedSource.footprint W (GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights
        (ownBudget m k (b:ℝ) false) (opposingBudget m k (b:ℝ) false))+
      GeneralPaperEncodedSharedSource.footprint W (GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights
        (ownBudget m k (b:ℝ) true) (opposingBudget m k (b:ℝ) true))+
      GeneralPaperEncodedRationalRows.rowFootprint W (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1.values≤
      window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi := by
  have hShared (reciprocal : Bool) :
      GeneralPaperEncodedSharedSource.footprint W (GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights
        (ownBudget m k (b:ℝ) reciprocal) (opposingBudget m k (b:ℝ) reciprocal))≤
      GeneralPaperSourceRowsCallerStorage.window model W k Qv weights (b:ℝ) reciprocal := by
    simp only [GeneralPaperSourceRowsCallerStorage.window,GeneralPaperRetainedSourceRowsCallerStorage.window]
    omega
  have hValues : GeneralPaperEncodedRationalRows.rowFootprint W (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1.values≤
      GeneralPaperRetainedFieldValuesStorage.window model W Qv hQv weights hp hs cursor hc := by
    simp only [GeneralPaperRetainedFieldValuesStorage.window]
    omega
  have hr := hShared false
  have hpoor := hShared true
  simp only [window]
  omega

theorem bounded {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℚ) (C d B : ℕ) (hg : GeneralPaperFastRationalModel.Growth model C d)
    (hm : 0<m) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W)
    (hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (cursor : ℕ) (hc : cursor≤m) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K) :
    window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi≤profile model C d W m k Qv B ∧
      (run model W k Qv hQv weights hp hs b).2≤price model C d W m k Qv := by
  let values := GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs
  let rich := GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) false
  let poor := GeneralPaperSourceColumnCallerStorage.run model W k Qv weights (b:ℝ) true
  let compiled := GeneralPaperSourceCompilerPairStorage.run model W k Qv hQv weights hp hs (b:ℝ)
  let result := run model W k Qv hQv weights hp hs b
  have hbReal : (0:ℝ)<b ∧ (b:ℝ)<1 := by exact_mod_cast hb
  have hV := GeneralPaperRetainedFieldValuesStorage.bounded model W Qv hQv weights hp hs cursor hc
  have hR := GeneralPaperSourceColumnCallerStorage.source_column hg W k Qv weights hs (b:ℝ) hbReal false hW hK hM hScatter
  have hP := GeneralPaperSourceColumnCallerStorage.source_column hg W k Qv weights hs (b:ℝ) hbReal true hW hK hM hScatter
  have hPair := GeneralPaperSourceCompilerPairStorage.source_pair model W k Qv hQv weights hp hs (b:ℝ) hm hbReal hW hK hM hIndex hDim hBatch hFinal
  have hVR : values.2≤GeneralPaperRetainedFieldValuesStorage.price model W m Qv := hV.2
  have hRR : rich.2≤GeneralPaperRetainedSourceColumnCallerStorage.price W (GeneralPaperSourceRowsCallerStorageRates.sourceWorkCap C d W m k Qv)
      (GeneralPaperSourceColumnCallerStorageRates.unitPrice model W m k) := hR.2
  have hPR : poor.2≤GeneralPaperRetainedSourceColumnCallerStorage.price W (GeneralPaperSourceRowsCallerStorageRates.sourceWorkCap C d W m k Qv)
      (GeneralPaperSourceColumnCallerStorageRates.unitPrice model W m k) := hP.2
  have hCR : compiled.2≤GeneralPaperSourceCompilerPairStorageRates.price model W m k Qv := hPair.2
  have hRun := run_data model W k Qv hQv weights hp hs b hm hb
  change result=(compiled.1,values.2+rich.2+poor.2+compiled.2+128*W) at hRun
  have hResult : result.2=values.2+rich.2+poor.2+compiled.2+128*W := congrArg Prod.snd hRun
  have hWork : result.2≤price model C d W m k Qv := by unfold price;omega
  have hReturned : GeneralPaperRetainedCompilerPairStorage.optionFoot W result.1≤
      GeneralPaperSourceCompilerPairStorageRates.sourceProfile model W m k Qv := by
    have hInside : GeneralPaperRetainedCompilerPairStorage.optionFoot W compiled.1≤
        GeneralPaperSourceCompilerPairStorage.window model W k Qv hQv weights hp hs (b:ℝ) outer ho inner hi := by
      dsimp only [compiled,GeneralPaperSourceCompilerPairStorage.run,GeneralPaperSourceCompilerPairStorage.window,GeneralPaperRetainedCompilerPairStorage.window]
      omega
    have hEq := congrArg Prod.fst hRun
    change result.1=compiled.1 at hEq
    rw [hEq]
    exact hInside.trans (hPair.1 outer ho inner hi)
  have hRowsRich := GeneralPaperSourceRowsCallerStorage.source_rows hg W k Qv weights hs (b:ℝ) hbReal false
  have hRowsPoor := GeneralPaperSourceRowsCallerStorage.source_rows hg W k Qv weights hs (b:ℝ) hbReal true
  have hGrid := grid_bound C d W k Qv weights hs b hb
  have hFront := GeneralPaperClassifierResultStorage.front_native W m k (b:ℝ) hbReal
  change front W m k b≤GeneralPaperClassifierResultStorage.frontProfile W m k at hFront
  have hWeights := GeneralPaperEncodedNatArray.bounded W (natBits Qv) weights
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono (GeneralPaperSourceScoreHeights.weight_le Qv weights hs j)) 1)
  have hRatio := rationalWordWidth_of_height hB
  have hRichBit := GeneralPaperFinalStaticLoopStorage.bit_bound rich.1.2
  have hPoorBit := GeneralPaperFinalStaticLoopStorage.bit_bound poor.1.2
  have hCheckBit := GeneralPaperFinalStaticLoopStorage.bit_bound (rich.1.2 && poor.1.2)
  have hSomeBit := GeneralPaperFinalStaticLoopStorage.bit_bound result.1.isSome
  have hf := fields_bound W (natBits (metadataCap model C d W m k Qv))
    [m,k,Qv,(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows,(prepare m k).K,cursor,
      values.2,rich.2,poor.2,compiled.2,result.2,values.2+rich.2,values.2+rich.2+poor.2,values.2+rich.2+poor.2+compiled.2,128*W,64*W,
      GeneralPaperFinalStaticLoopStorage.bit rich.1.2,GeneralPaperFinalStaticLoopStorage.bit poor.1.2,
      GeneralPaperFinalStaticLoopStorage.bit (rich.1.2 && poor.1.2),GeneralPaperFinalStaticLoopStorage.bit result.1.isSome] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap price at *;omega)
  change fields W _≤20*(natBits (metadataCap model C d W m k Qv)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  have hPairWindow := hPair.1 outer ho inner hi
  simp only [window,profile]
  change rationalWordWidth b+GeneralPaperEncodedNatArray.footprint W weights+front W m k b+
    GeneralPaperMaterializedCacheStorage.gridFootprint W (GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv)+
    GeneralPaperSourceRowsCallerStorage.window model W k Qv weights (b:ℝ) false+
    GeneralPaperSourceRowsCallerStorage.window model W k Qv weights (b:ℝ) true+
    GeneralPaperRetainedFieldValuesStorage.window model W Qv hQv weights hp hs cursor hc+
    GeneralPaperSourceColumnCallerStorage.window model W k Qv weights (b:ℝ) false+
    GeneralPaperSourceColumnCallerStorage.window model W k Qv weights (b:ℝ) true+
    GeneralPaperSourceCompilerPairStorage.window model W k Qv hQv weights hp hs (b:ℝ) outer ho inner hi+
    GeneralPaperRetainedCompilerPairStorage.optionFoot W result.1+
    fields W [m,k,Qv,(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows,(prepare m k).K,cursor,
      values.2,rich.2,poor.2,compiled.2,result.2,values.2+rich.2,values.2+rich.2+poor.2,values.2+rich.2+poor.2+compiled.2,128*W,64*W,
      GeneralPaperFinalStaticLoopStorage.bit rich.1.2,GeneralPaperFinalStaticLoopStorage.bit poor.1.2,
      GeneralPaperFinalStaticLoopStorage.bit (rich.1.2 && poor.1.2),GeneralPaperFinalStaticLoopStorage.bit result.1.isSome]+192*W≤_
  omega

theorem actual_return {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℚ) (hm : 0<m) (hb : 0<b ∧ b<1) :
    ∃ physical pair,(run model W k Qv hQv weights hp hs b).1=some physical ∧
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hs (b:ℝ)=some pair ∧
      GeneralPaperOriginalDrawEquilibrium.Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs (b:ℝ) pair := by
  obtain ⟨physical,pair,hNative,hSource,hMatch,hContract⟩ := GeneralPaperSourceCompilerPairStorage.actual_return
    model W k Qv hQv weights hp hs (b:ℝ) hm (by exact_mod_cast hb)
  have hd := congrArg Prod.fst (run_data model W k Qv hQv weights hp hs b hm hb)
  exact ⟨physical,pair,hd.trans hNative,hSource,hMatch,hContract⟩

end Blotto.GeneralPaperSourcePreparedPairOwners
