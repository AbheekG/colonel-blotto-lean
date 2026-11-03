import Blotto.GeneralPaperSourceCompilerPairStorageRates

/-! Actual physical compiler pair from both retained original-unit source
columns and the stored normalized value array. No matching or acceptance
postcondition is assumed: actual native returns establish the checked pair.
The selected child owns the opposite player's full array simultaneously. -/
namespace Blotto.GeneralPaperSourceCompilerPairStorage
open GeneralPaperProxyParameters GeneralPaperOriginalDrawEquilibrium GeneralPaperEncodedScalarStorage
open GeneralPaperInitializerPreparedPoint
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

noncomputable def columns {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ)
    (weights : FixedArrayTable m ℕ) (b : ℝ) :
    Columns (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K :=
  ⟨GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b false,
    GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b true⟩

noncomputable def run {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) :=
  GeneralPaperRetainedCompilerPairBits.run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H (prepare m k).Qg
    (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperProxyClassifier.classify m k b)
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1 (columns model W k Qv weights b)

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K) : ℕ :=
  GeneralPaperRetainedCompilerPairStorage.window model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H (prepare m k).Qg
    (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperProxyClassifier.classify m k b)
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1 (columns model W k Qv weights b) outer ho inner hi

theorem actual_return {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hm : 0<m) (hb : 0<b ∧ b<1) :
    ∃ physical pair,(run model W k Qv hQv weights hp hs b).1=some physical ∧
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hs b=some pair ∧ Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs b pair := by
  let c := columns model W k Qv weights b
  let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
  obtain ⟨physical,pair,hRun,hPair,hMatches,hContract⟩ := GeneralPaperRetainedPairSource.actual_return model k Qv hm hQv weights hp hs b hb c values
    (GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b false)
    (GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b true)
    (GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs)
  refine ⟨physical,pair,?_,hPair,hMatches,hContract⟩
  exact (GeneralPaperRetainedCompilerPairBits.data model W k hm b hb values c).trans hRun

theorem source_pair {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hm : 0<m) (hb : 0<b ∧ b<1)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    (∀ outer ho inner hi,window model W k Qv hQv weights hp hs b outer ho inner hi≤
      GeneralPaperSourceCompilerPairStorageRates.sourceProfile model W m k Qv) ∧
      (run model W k Qv hQv weights hp hs b).2≤GeneralPaperSourceCompilerPairStorageRates.price model W m k Qv := by
  let c := columns model W k Qv weights b
  let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
  let classified := GeneralPaperProxyClassifier.classify m k b
  let proxyValue := classified.choice.proxy.value
  let R := GeneralPaperSourceUnitCallerStorageRates.operandWidth m k
  have hAnchor (reciprocal : Bool) (j l) :
      rationalWordWidth (((GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal).read j).anchors.read l)≤R := by
    have hh : RationalHeight (((GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal).read j).anchors.read l)
        (GeneralPaperSourceScoreHeights.anchorHeight m k) := by
      change RationalHeight ((GeneralPaperRowQuantizer.dictionary (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)).anchor j l) _
      rw [GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b reciprocal,
        GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b reciprocal]
      exact GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal j l
    exact (rationalWordWidth_of_height hh).trans (by unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth;omega)
  have hValue (j) : RationalHeight (values.values.read j) (binaryWordWidth Qv) := by
    change RationalHeight ((GeneralPaperRetainedFieldValues.selector values).weight j) _
    rw [GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs]
    exact GeneralPaperSourceScoreHeights.value_height Qv hQv weights hp hs j
  have hProxy : rationalWordWidth proxyValue≤GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth m k := by
    have h := rationalWordWidth_of_height (GeneralPaperSourceScoreHeights.proxy_height m k b hb)
    unfold GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth GeneralPaperRetainedEndpointBitBounds.priceWidth
    exact h.trans (by omega)
  have hEndpoint := GeneralPaperSourceEndpointFractionConstructionStorage.source_constructor model W m k b hb
  have hE : GeneralPaperRetainedCompilerPairStorage.endpointWindow model W (prepare m k).Qg (grid_positive m k) classified≤
      GeneralPaperSourceEndpointFractionConstructionStorageRates.sourceProfile model W m k := by
    cases hc : classified.choice.modify with
    | none => simp only [GeneralPaperRetainedCompilerPairStorage.endpointWindow,hc];exact Nat.zero_le _
    | some side =>
      simpa only [GeneralPaperRetainedCompilerPairStorage.endpointWindow,hc,GeneralPaperSourceEndpointFractionConstructionStorage.window] using hEndpoint.1
  have hEP : GeneralPaperRetainedCompilerPairStorage.endpointWork model W (prepare m k).Qg (grid_positive m k) classified≤
      GeneralPaperSourceCompilerPairStorageRates.endpointPrice model W m k := by
    cases hc : classified.choice.modify with
    | none => simp only [GeneralPaperRetainedCompilerPairStorage.endpointWork,hc];exact Nat.zero_le _
    | some side =>
      simpa only [GeneralPaperRetainedCompilerPairStorage.endpointWork,hc,GeneralPaperSourceCompilerPairStorageRates.endpointPrice] using hEndpoint.2
  have hChild : ∀ outer ho inner hi,GeneralPaperRetainedCompilerPairStorage.activeWindow model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H (prepare m k).Qg
    (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperProxyClassifier.classify m k b)
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1 (columns model W k Qv weights b) outer ho inner hi≤
      GeneralPaperSourceModifiedColumnStorageRates.sourceProfile model W m k Qv := by
    intro outer ho inner hi
    cases hc : (GeneralPaperProxyClassifier.classify m k b).choice.modify with
    | none => simp only [GeneralPaperRetainedCompilerPairStorage.activeWindow,hc];exact Nat.zero_le _
    | some side =>
      have hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by rw [hc];simp
      cases side with
        | rich =>
          have h := (GeneralPaperSourceModifiedColumnStorage.source_construction model W k Qv hm hQv weights hp hs b hb false hModify hW hK hM hIndex hDim hBatch hFinal).1 outer ho inner hi
          simpa only [GeneralPaperRetainedCompilerPairStorage.activeWindow,hc,GeneralPaperSourceModifiedColumnStorage.window,
            columns,GeneralPaperSourceFinalCheckStorage.endpointFraction,ownBudget,opposingBudget,Bool.false_eq_true,ite_false] using h
        | poor =>
          have h := (GeneralPaperSourceModifiedColumnStorage.source_construction model W k Qv hm hQv weights hp hs b hb true hModify hW hK hM hIndex hDim hBatch hFinal).1 outer ho inner hi
          simpa only [GeneralPaperRetainedCompilerPairStorage.activeWindow,hc,GeneralPaperSourceModifiedColumnStorage.window,
            columns,GeneralPaperSourceFinalCheckStorage.endpointFraction,ownBudget,opposingBudget,ite_true] using h
  have hP : (GeneralPaperRetainedCompilerPairStorage.child model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H (prepare m k).Qg
    (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperProxyClassifier.classify m k b)
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1 (columns model W k Qv weights b)).2≤
      GeneralPaperSourceModifiedColumnStorageRates.price model W m k Qv := by
    cases hc : (GeneralPaperProxyClassifier.classify m k b).choice.modify with
    | none => simp only [GeneralPaperRetainedCompilerPairStorage.child,hc];exact Nat.zero_le _
    | some side =>
      have hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by rw [hc];simp
      cases side with
        | rich =>
          have h := (GeneralPaperSourceModifiedColumnStorage.source_construction model W k Qv hm hQv weights hp hs b hb false hModify hW hK hM hIndex hDim hBatch hFinal).2
          simpa only [GeneralPaperRetainedCompilerPairStorage.child,hc,GeneralPaperSourceModifiedColumnStorage.run,
            columns,GeneralPaperSourceFinalCheckStorage.endpointFraction,ownBudget,opposingBudget,Bool.false_eq_true,ite_false] using h
        | poor =>
          have h := (GeneralPaperSourceModifiedColumnStorage.source_construction model W k Qv hm hQv weights hp hs b hb true hModify hW hK hM hIndex hDim hBatch hFinal).2
          simpa only [GeneralPaperRetainedCompilerPairStorage.child,hc,GeneralPaperSourceModifiedColumnStorage.run,
            columns,GeneralPaperSourceFinalCheckStorage.endpointFraction,ownBudget,opposingBudget,ite_true] using h
  have hGeneric outer ho inner hi := GeneralPaperRetainedCompilerPairStorage.bounded model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H (prepare m k).Qg
    (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperProxyClassifier.classify m k b)
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
    (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1 (columns model W k Qv weights b) R (binaryWordWidth Qv)
    (GeneralPaperClassifierResultStorage.profile W m k) (GeneralPaperSourceEndpointFractionConstructionStorageRates.operandWidth m k)
    (GeneralPaperSourceModifiedColumnStorageRates.sourceProfile model W m k Qv)
    (GeneralPaperSourceEndpointFractionConstructionStorageRates.sourceProfile model W m k)
    (GeneralPaperSourceModifiedColumnStorageRates.price model W m k Qv) (GeneralPaperSourceCompilerPairStorageRates.endpointPrice model W m k)
    (hAnchor false) (hAnchor true) hValue (GeneralPaperClassifierResultStorage.native W m k b hb) hProxy hChild hE hP hEP outer ho inner hi
  exact ⟨fun outer ho inner hi => (hGeneric outer ho inner hi).1,(hGeneric 0 (Nat.zero_le _) 0 (Nat.zero_le _)).2⟩

theorem construction_common_word {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ z : GeneralPaperSourceWordGrowth.Input,
      let W := GeneralPaperCompilerReference.width C d z
      ∀ (_hm : 0<z.m) (hQv : 0<z.Qv) (hp : ∀ j,0<z.weights.read j)
        (b : ℝ) (_hb : 0<b ∧ b<1)
        (_hW : 1≤W) (_hK : binaryWordWidth ((prepare z.m z.k).K+1)≤W) (_hM : binaryWordWidth (z.m+1)≤W)
        (_hIndex : binaryWordWidth ((prepare z.m z.k).S+2)≤W) (_hDim : binaryWordWidth (z.m*((prepare z.m z.k).K-1)+3)≤W)
        (_hBatch : binaryWordWidth (((prepare z.m z.k).S+1)*((prepare z.m z.k).K*(prepare z.m z.k).K)+3)≤W)
        (_hFinal : binaryWordWidth ((prepare z.m z.k).S+4)≤W),
        ∀ outer ho inner hi,window model W z.k z.Qv hQv z.weights hp z.weight_sum b outer ho inner hi≤
          A*(z.m+1)^3*2^(4*z.k)*(GeneralPaperSourceWordGrowth.logSize z)^e := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceCompilerPairStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro hm hQv hp b hb hW hK hM hIndex hDim hBatch hFinal outer ho inner hi
  exact ((source_pair model (GeneralPaperCompilerReference.width C d z) z.k z.Qv hQv z.weights hp z.weight_sum b hm hb
    hW hK hM hIndex hDim hBatch hFinal).1 outer ho inner hi).trans ((Nat.le_add_left _ _).trans (hRate z))

theorem retained_construction {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hm : 0<m) (hb : 0<b ∧ b<1)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) (C d oldOwner : ℕ)
    (hOld : oldOwner≤GeneralPaperSourceModifiedColumnStorageRates.reservation model C d W m k Qv) :
    ∀ outer ho inner hi,oldOwner+window model W k Qv hQv weights hp hs b outer ho inner hi≤
      GeneralPaperSourceCompilerPairStorageRates.reservation model C d W m k Qv := by
  intro outer ho inner hi
  exact Nat.add_le_add hOld ((source_pair model W k Qv hQv weights hp hs b hm hb
    hW hK hM hIndex hDim hBatch hFinal).1 outer ho inner hi)

end Blotto.GeneralPaperSourceCompilerPairStorage
