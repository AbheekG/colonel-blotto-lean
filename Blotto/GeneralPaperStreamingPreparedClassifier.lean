import Blotto.GeneralPaperStreamingClassifier

/-! Parameter/alphabet construction and the whole streaming classifier
compose once, at the derived shared word. The native proxy, cap, unit data
and complete pre-existing constructor/classifier operation price survive.
Only the CF phase space is closed here; global simultaneous space remains.
-/
namespace Blotto.GeneralPaperStreamingPreparedClassifier
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem cache_positive (model : RationalCostModel) (W m k : ℕ) :
    0<(GeneralPaperPrecallCachePrice.prepare model.rat W m k).1.1.proxy.Qg := by
  rw [GeneralPaperPrecallCachePrice.prepare_data]
  exact GeneralPaperProxyParameters.grid_positive m k

def prepare (model : RationalCostModel) (W m k : ℕ) (b : ℚ) :
    ((GeneralPaperPrecallCachePrice.Cache × GeneralPaperCodeAlphabet.Alphabet) × GeneralPaperProxyClassifier.Result) × ℕ :=
  let cache := GeneralPaperPrecallCachePrice.prepare model.rat W m k
  let classified := GeneralPaperStreamingClassifier.run model W cache.1.1 (cache_positive model W m k) b
  ((cache.1,classified.1),cache.2+classified.2+32*W)

theorem data (model : RationalCostModel) (W m k : ℕ) (b : ℚ) :
    (prepare model W m k b).1=((GeneralPaperPrecallCachePrice.specification m k,GeneralPaperProxyParameters.alphabet m k),
      GeneralPaperProxyClassifier.classify m k (b:ℝ)) := by
  unfold prepare
  dsimp only
  rw [GeneralPaperStreamingClassifier.data model W m k (GeneralPaperPrecallCachePrice.prepare model.rat W m k).1.1
    (GeneralPaperPrecallCachePrice.data model.rat W m k),
    GeneralPaperPrecallCachePrice.prepare_data]

def profile (model : RationalCostModel) (W m k B : ℕ) : ℕ :=
  GeneralPaperPrecallCachePrice.profile model.rat W m k+
    GeneralPaperStreamingClassifier.profile model W (GeneralPaperPrecallCachePrice.specification m k) B+56*W

theorem work (model : RationalCostModel) (W m k : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    (prepare model W m k b).2≤profile model W m k B := by
  have hp := GeneralPaperPrecallCachePrice.prepare_work model.rat model.monotone W m k
  have hc := GeneralPaperStreamingClassifier.work model W m k
    (GeneralPaperPrecallCachePrice.prepare model.rat W m k).1.1
    (GeneralPaperPrecallCachePrice.data model.rat W m k) (cache_positive model W m k) b hb B hB
  have hProfile : GeneralPaperStreamingClassifier.profile model W
      (GeneralPaperPrecallCachePrice.prepare model.rat W m k).1.1 B=
      GeneralPaperStreamingClassifier.profile model W (GeneralPaperPrecallCachePrice.specification m k) B := by
    rw [GeneralPaperPrecallCachePrice.prepare_data]
  rw [hProfile] at hc
  change (GeneralPaperPrecallCachePrice.prepare model.rat W m k).2+
    (GeneralPaperStreamingClassifier.run model W (GeneralPaperPrecallCachePrice.prepare model.rat W m k).1.1
      (cache_positive model W m k) b).2+32*W≤_
  unfold profile
  omega

theorem unit_data (model : RationalCostModel) (W m k : ℕ) (b : ℚ) :
    (prepare model W m k b).1=(GeneralPaperCachedClassifier.prepare m k (b:ℝ)).1 := by
  rw [data,GeneralPaperCachedClassifier.prepare_data]

theorem returned_proxy (model : RationalCostModel) (W m k : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    let c := (prepare model W m k b).1
    0<c.2.choice.proxy.num ∧ c.2.choice.proxy.num<c.2.choice.proxy.den ∧
      c.2.choice.proxy.den≤c.1.1.proxy.qbar ∧
      0<c.2.choice.proxy.value ∧ c.2.choice.proxy.value<1 ∧
      c.2.choice.proxy.value.den≤c.1.1.proxy.qbar := by
  rw [data]
  have hReal : (0:ℝ)<b ∧ (b:ℝ)<1 := by exact_mod_cast hb
  have hInt := GeneralPaperProxyClassifier.proxy_integer_representation m k (b:ℝ) hReal
  have hUnit := GeneralPaperProxyClassifier.proxy_unit m k (b:ℝ) hReal
  exact ⟨hInt.1,hInt.2.1,hInt.2.2,hUnit.1,hUnit.2,GeneralPaperProxyClassifier.proxy_reduced_denominator m k (b:ℝ)⟩

theorem profile_agrees (model : RationalCostModel) (W m k B : ℕ) :
    profile model W m k B=GeneralPaperPreparedClassifierBits.profile model W m k B := rfl

def calibrated (model : RationalCostModel) (m k : ℕ) (b : ℚ) :=
  prepare model (GeneralPaperPrecallControlWord.word m k) m k b

theorem calibrated_work (model : RationalCostModel) (m k : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    (calibrated model m k b).2≤GeneralPaperCalibratedClassifier.profile model m k B := by
  have h := work model (GeneralPaperPrecallControlWord.word m k) m k b hb B hB
  rw [profile_agrees] at h
  have hc := GeneralPaperClassifierEnvelope.profile_bound model (GeneralPaperPrecallControlWord.word m k)
    (GeneralPaperPrecallCachePrice.specification m k) B
  have hp := model.monotone (GeneralPaperClassifierEnvelope.actual_width m k B)
  have hProfile := hc.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hp (GeneralPaperPrecallControlWord.word m k)))
  change _≤GeneralPaperPrecallCachePrice.profile model.rat (GeneralPaperPrecallControlWord.word m k) m k+
    GeneralPaperClassifierBits.profile model (GeneralPaperPrecallControlWord.word m k) (GeneralPaperPrecallCachePrice.specification m k) B+
    56*GeneralPaperPrecallControlWord.word m k at h
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add_left hProfile _) _)

theorem calibrated_data (model : RationalCostModel) (m k : ℕ) (b : ℚ) :
    (calibrated model m k b).1=(GeneralPaperCachedClassifier.prepare m k (b:ℝ)).1 :=
  unit_data model (GeneralPaperPrecallControlWord.word m k) m k b

end Blotto.GeneralPaperStreamingPreparedClassifier
