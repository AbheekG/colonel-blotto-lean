import Blotto.GeneralPaperSourcePreparationControls

/-! The returned classifier alphabet feeds the shared source parameter
cache once. Both are retained together. The combined local word covers the
constructor/classifier and parameter controls, without any capacity oracle.
This boundary precedes source grid/power-table/forest materialization.
-/
namespace Blotto.GeneralPaperSourcePrecallPreparation
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def prepare (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) :=
  let front := GeneralPaperStreamingPreparedClassifier.prepare model W m k b
  let source := GeneralPaperSourcePreparationCache.prepare model.rat W m front.1.1.2.lambda k Qv
  ((front.1,source.1),front.2+source.2+64*W)

theorem data (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) :
    (prepare model W m k Qv b).1=
      (((GeneralPaperPrecallCachePrice.specification m k,GeneralPaperProxyParameters.alphabet m k),
        GeneralPaperProxyClassifier.classify m k (b:ℝ)),
        GeneralPaperSourcePreparationCache.specification m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv) := by
  simp only [prepare,GeneralPaperStreamingPreparedClassifier.data,GeneralPaperSourcePreparationCache.data]

def profile (model : RationalCostModel) (W m k Qv B : ℕ) : ℕ :=
  GeneralPaperStreamingPreparedClassifier.profile model W m k B+
    GeneralPaperSourcePreparationCache.profile model.rat W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv+64*W

theorem work (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    (prepare model W m k Qv b).2≤profile model W m k Qv B := by
  have hf := GeneralPaperStreamingPreparedClassifier.work model W m k b hb B hB
  have hs := GeneralPaperSourcePreparationCache.work model.rat model.monotone W m
    (GeneralPaperStreamingPreparedClassifier.prepare model W m k b).1.1.2.lambda k Qv
  rw [GeneralPaperStreamingPreparedClassifier.data] at hs
  dsimp only at hs
  change (GeneralPaperStreamingPreparedClassifier.prepare model W m k b).2+
    (GeneralPaperSourcePreparationCache.prepare model.rat W m
      (GeneralPaperStreamingPreparedClassifier.prepare model W m k b).1.1.2.lambda k Qv).2+64*W≤_
  rw [GeneralPaperStreamingPreparedClassifier.data]
  dsimp only
  unfold profile
  omega

def word (m k Qv : ℕ) : ℕ :=
  GeneralPaperPrecallControlWord.word m k+
    GeneralPaperSourcePreparationControls.word m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv

theorem front_word (m k Qv : ℕ) : GeneralPaperPrecallControlWord.word m k≤word m k Qv := by unfold word; omega

theorem source_word (m k Qv : ℕ) :
    GeneralPaperSourcePreparationControls.word m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv≤word m k Qv := by unfold word; omega

def calibrated (model : RationalCostModel) (m k Qv : ℕ) (b : ℚ) := prepare model (word m k Qv) m k Qv b

theorem calibrated_work (model : RationalCostModel) (m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    (calibrated model m k Qv b).2≤profile model (word m k Qv) m k Qv B := work model _ m k Qv b hb B hB

theorem both_data (model model' : RationalCostModel) (W W' m k Qv : ℕ) (b : ℚ) :
    (prepare model W m k Qv b).1=(prepare model' W' m k Qv b).1 := by rw [data,data]

theorem native_front (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) :
    (prepare model W m k Qv b).1.1=(GeneralPaperCachedClassifier.prepare m k (b:ℝ)).1 := by
  rw [data,GeneralPaperCachedClassifier.prepare_data]

theorem proxy_caps (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    let r := (prepare model W m k Qv b).1
    0<r.1.2.choice.proxy.num ∧ r.1.2.choice.proxy.num<r.1.2.choice.proxy.den ∧
      r.1.2.choice.proxy.den≤r.1.1.1.proxy.qbar ∧
      0<r.1.2.choice.proxy.value ∧ r.1.2.choice.proxy.value<1 ∧
      r.1.2.choice.proxy.value.den≤r.1.1.1.proxy.qbar := by
  exact GeneralPaperStreamingPreparedClassifier.returned_proxy model W m k b hb

theorem parameter_dyadic_controls (primitive : ℕ → ℕ) (m k Qv e : ℕ) (he : e≤74+2*k) :
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive (word m k Qv) e).1.doublings+1)≤word m k Qv ∧
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive (word m k Qv) e).1.work+8)≤word m k Qv := by
  rw [GeneralPaperDyadicPowerBits.data]
  have h := GeneralPaperSourcePreparationControls.dyadic_controls primitive m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv e he
  rw [GeneralPaperDyadicPowerBits.data] at h
  exact ⟨h.1.trans (source_word m k Qv),h.2.trans (source_word m k Qv)⟩

theorem parameter_ceiling_controls (primitive : ℕ → ℕ) (m k Qv target p : ℕ) (hp : 0<p)
    (ht : GeneralPaperSourcePreparationControls.IsTarget m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv target) :
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m k Qv) target p hp).1.doublings+1)≤word m k Qv ∧
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m k Qv) target p hp).1.work+192)≤word m k Qv := by
  rw [GeneralPaperPowerCeilingBits.loop_data]
  have h := GeneralPaperSourcePreparationControls.ceiling_controls primitive m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv target p hp ht
  rw [GeneralPaperPowerCeilingBits.loop_data] at h
  exact ⟨h.1.trans (source_word m k Qv),h.2.trans (source_word m k Qv)⟩

end Blotto.GeneralPaperSourcePrecallPreparation
