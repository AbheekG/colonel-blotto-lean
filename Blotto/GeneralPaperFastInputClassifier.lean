import Blotto.GeneralPaperFastInputQuotient

/-! Once-only bit front with one original-input quotient. The returned
root, classifier and parameter cache agree exactly with the checked front.
CF search uses constructed operands; original b enters only the quotient
and the fixed number of selection comparisons. No source is replayed. -/
namespace Blotto.GeneralPaperFastInputClassifier
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def query (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) :
    (GeneralPaperBoundedQuotient.Result×GeneralPaperMidpointQuery.Result)×ℕ :=
  let location := GeneralPaperFastInputQuotient.run model W c b
  let root := GeneralPaperStreamingMidpointQuery.run model W true c.proxy.H c.proxy.Qg location.1.quotient (c.proxy.gridBits+3)
  ((location.1,root.1),location.2+root.2+64*W)

theorem query_data (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1) :
    (query model W c b).1=(GeneralPaperStreamingCachedRoot.run model W c b).1 := by
  dsimp only [query,GeneralPaperStreamingCachedRoot.run]
  rw [GeneralPaperFastInputQuotient.data model W m k c hc b hb]

def queryProfile (model : RationalCostModel) (W m k B : ℕ) : ℕ :=
  let c := GeneralPaperPrecallCachePrice.specification m k
  GeneralPaperFastInputQuotient.profile model W m k B+
    2097152*(c.proxy.gridBits+6)*(W+model.rat (GeneralPaperCFOperandPrice.width (c.proxy.gridBits+3) c.proxy.H))+64*W

theorem query_work (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    (query model W c b).2≤queryProfile model W m k B := by
  have hl := GeneralPaperFastInputQuotient.work model W m k c hc b B hB
  have ht := (GeneralPaperProxyQuotientPrice.quotient_cell model W m k c hc b hb).1
  rw [←GeneralPaperFastInputQuotient.data model W m k c hc b hb] at ht
  have hD : 0<c.proxy.H := by rw [hc];exact GeneralPaperProxyParameters.H_positive m k
  have hQ : 0<c.proxy.Qg := by rw [hc];exact GeneralPaperProxyParameters.grid_positive m k
  have hPower : 8*c.proxy.Qg=2^(c.proxy.gridBits+3) := by rw [hc];exact GeneralPaperProxyClassifier.grid_dyadic m k
  have hr := GeneralPaperStreamingMidpointQuery.work model W c.proxy.H c.proxy.Qg
    (GeneralPaperFastInputQuotient.run model W c b).1.quotient (c.proxy.gridBits+3) true hD hQ ht hPower
  have hProfile : queryProfile model W m k B=GeneralPaperFastInputQuotient.profile model W m k B+
      2097152*(c.proxy.gridBits+6)*(W+model.rat (GeneralPaperCFOperandPrice.width (c.proxy.gridBits+3) c.proxy.H))+64*W := by
    unfold queryProfile
    rw [hc]
  rw [hProfile]
  change _≤2097152*(c.proxy.gridBits+6)*(W+model.rat (GeneralPaperCFOperandPrice.width (c.proxy.gridBits+3) c.proxy.H)) at hr
  exact Nat.add_le_add_right (Nat.add_le_add hl hr) _

def run (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (hQ : 0<c.proxy.Qg) (b : ℚ) :
    GeneralPaperProxyClassifier.Result×ℕ :=
  let queried := query model W c b
  let selected := GeneralPaperSelectionBits.run model W c.proxy.Qg queried.1.1.quotient hQ b queried.1.2.fraction
  (⟨queried.1.1.quotient,queried.1.2.fraction,selected.1,
      c.proxy.work+queried.1.1.work+queried.1.2.work+selected.1.work+24⟩,
    queried.2+selected.2+64*W)

theorem classifier_data (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (hQ : 0<c.proxy.Qg) (b : ℚ) (hb : 0<b ∧ b<1) :
    (run model W c hQ b).1=GeneralPaperProxyClassifier.classify m k (b:ℝ) := by
  have h : (run model W c hQ b).1=(GeneralPaperStreamingClassifier.run model W c hQ b).1 := by
    dsimp only [run,GeneralPaperStreamingClassifier.run]
    rw [query_data model W m k c hc b hb]
  exact h.trans (GeneralPaperStreamingClassifier.data model W m k c hc hQ b)

def profile (model : RationalCostModel) (W m k B : ℕ) : ℕ :=
  queryProfile model W m k B+512*(W+model.rat (GeneralPaperSelectionPoints.width (GeneralPaperProxyParameters.prepare m k).Qg B))+64*W

theorem work (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (hQ : 0<c.proxy.Qg) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) : (run model W c hQ b).2≤profile model W m k B := by
  have hQuery := query_work model W m k c hc b hb B hB
  have hRoot : ∀ f,(query model W c b).1.2.fraction=some f → f.num≤2*c.proxy.Qg ∧ f.den≤2*c.proxy.Qg := by
    rw [query_data model W m k c hc b hb,GeneralPaperStreamingCachedRoot.data_agrees]
    exact GeneralPaperClassifierRootBounds.root_bounds model W m k c hc b hb
  have hCell : (query model W c b).1.1.quotient<c.proxy.Qg := by
    change (GeneralPaperFastInputQuotient.run model W c b).1.quotient<c.proxy.Qg
    rw [GeneralPaperFastInputQuotient.data model W m k c hc b hb]
    exact (GeneralPaperProxyQuotientPrice.quotient_cell model W m k c hc b hb).1
  have hSelection := GeneralPaperSelectionBits.work model W c.proxy.Qg (query model W c b).1.1.quotient B hQ b
    (query model W c b).1.2.fraction hCell hB hRoot
  have hWidth : GeneralPaperSelectionPoints.width c.proxy.Qg B=GeneralPaperSelectionPoints.width
      (GeneralPaperProxyParameters.prepare m k).Qg B := by rw [hc];rfl
  rw [hWidth] at hSelection
  exact Nat.add_le_add_right (Nat.add_le_add hQuery hSelection) _

def prepare (model : RationalCostModel) (W m k : ℕ) (b : ℚ) :=
  let cache := GeneralPaperPrecallCachePrice.prepare model.rat W m k
  let classified := run model W cache.1.1 (GeneralPaperStreamingPreparedClassifier.cache_positive model W m k) b
  ((cache.1,classified.1),cache.2+classified.2+32*W)

theorem prepare_data (model : RationalCostModel) (W m k : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    (prepare model W m k b).1=((GeneralPaperPrecallCachePrice.specification m k,GeneralPaperProxyParameters.alphabet m k),
      GeneralPaperProxyClassifier.classify m k (b:ℝ)) := by
  dsimp only [prepare]
  rw [classifier_data model W m k (GeneralPaperPrecallCachePrice.prepare model.rat W m k).1.1 (GeneralPaperPrecallCachePrice.data model.rat W m k)
    (GeneralPaperStreamingPreparedClassifier.cache_positive model W m k) b hb,GeneralPaperPrecallCachePrice.prepare_data]

def prepareProfile (model : RationalCostModel) (W m k B : ℕ) : ℕ :=
  GeneralPaperPrecallCachePrice.profile model.rat W m k+profile model W m k B+56*W

theorem prepare_work (model : RationalCostModel) (W m k : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    (prepare model W m k b).2≤prepareProfile model W m k B := by
  have hCache := GeneralPaperPrecallCachePrice.prepare_work model.rat model.monotone W m k
  have hClass := work model W m k (GeneralPaperPrecallCachePrice.prepare model.rat W m k).1.1 (GeneralPaperPrecallCachePrice.data model.rat W m k)
    (GeneralPaperStreamingPreparedClassifier.cache_positive model W m k) b hb B hB
  unfold prepare prepareProfile
  dsimp only
  omega

def source (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) :=
  let front := prepare model W m k b
  let controls := GeneralPaperSourcePreparationCache.prepare model.rat W m front.1.1.2.lambda k Qv
  ((front.1,controls.1),front.2+controls.2+64*W)

theorem source_data (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    (source model W m k Qv b).1=(GeneralPaperSourcePrecallPreparation.prepare model W m k Qv b).1 := by
  rw [GeneralPaperSourcePrecallPreparation.data]
  simp only [source,prepare_data model W m k b hb,GeneralPaperSourcePreparationCache.data]

def sourceProfile (model : RationalCostModel) (W m k Qv B : ℕ) : ℕ :=
  prepareProfile model W m k B+GeneralPaperSourcePreparationCache.profile model.rat W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv+64*W

theorem source_work (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    (source model W m k Qv b).2≤sourceProfile model W m k Qv B := by
  have hFront := prepare_work model W m k b hb B hB
  have hControls := GeneralPaperSourcePreparationCache.work model.rat model.monotone W m
    (prepare model W m k b).1.1.2.lambda k Qv
  rw [prepare_data model W m k b hb] at hControls
  dsimp only at hControls
  dsimp only [source]
  rw [prepare_data model W m k b hb]
  exact Nat.add_le_add_right (Nat.add_le_add hFront hControls) _

end Blotto.GeneralPaperFastInputClassifier
