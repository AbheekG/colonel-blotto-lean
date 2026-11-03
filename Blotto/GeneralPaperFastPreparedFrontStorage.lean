import Blotto.GeneralPaperFastClassifierStorage

/-! Actual prepared fast classifier. The full native precall constructor
frontier, cache/alphabet return, classifier child, complete returned front,
original ratio and ten parent fields coexist. This wraps existing executed
constructors; parameter construction and classification are not replayed. -/
namespace Blotto.GeneralPaperFastPreparedFrontStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def window (model : RationalCostModel) (W m k : ℕ) (b : ℚ) : ℕ :=
  let cache := GeneralPaperPrecallCachePrice.prepare model.rat W m k
  let classified := GeneralPaperFastInputClassifier.run model W cache.1.1 (GeneralPaperStreamingPreparedClassifier.cache_positive model W m k) b
  let result := GeneralPaperFastInputClassifier.prepare model W m k b
  GeneralPaperPrecallConstructionStorage.window model W m k+
    GeneralPaperFastClassifierStorage.window model W cache.1.1 (GeneralPaperStreamingPreparedClassifier.cache_positive model W m k) b+
    footprint W cache.1.1+alphabetFootprint W cache.1.2+rationalWordWidth b+
    GeneralPaperClassifierResultStorage.frontFootprint W result.1+
    fields W [m,k,W,cache.2,classified.2,result.2,cache.2+classified.2,32*W,24*W,56*W]+192*W

def profile (model : RationalCostModel) (W m k B : ℕ) : ℕ :=
  GeneralPaperPrecallConstructionStorage.profile model W m k+GeneralPaperFastClassifierStorage.profile model W m k B+
    21*(payload m k+W)+(1+2*B)+GeneralPaperClassifierResultStorage.frontProfile W m k+
    10*(payload m k+natBits (GeneralPaperFastInputClassifier.prepareProfile model W m k B)+2*W+8)+480*W

theorem returned (model : RationalCostModel) (W m k : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    GeneralPaperClassifierResultStorage.frontFootprint W (GeneralPaperFastInputClassifier.prepare model W m k b).1≤
      GeneralPaperClassifierResultStorage.frontProfile W m k := by
  rw [GeneralPaperFastInputClassifier.prepare_data model W m k b hb]
  exact GeneralPaperClassifierResultStorage.front_native W m k (b:ℝ) (by exact_mod_cast hb)

theorem bounded (model : RationalCostModel) (W m k B : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) :
    window model W m k b≤profile model W m k B ∧
      (GeneralPaperFastInputClassifier.prepare model W m k b).2≤GeneralPaperFastInputClassifier.prepareProfile model W m k B := by
  let cache := GeneralPaperPrecallCachePrice.prepare model.rat W m k
  let classified := GeneralPaperFastInputClassifier.run model W cache.1.1 (GeneralPaperStreamingPreparedClassifier.cache_positive model W m k) b
  let result := GeneralPaperFastInputClassifier.prepare model W m k b
  have hCache : cache.1.1=GeneralPaperPrecallCachePrice.specification m k := GeneralPaperPrecallCachePrice.data model.rat W m k
  have hConstructor := GeneralPaperPrecallConstructionStorage.bounded model W m k
  have hClass := (GeneralPaperFastClassifierStorage.bounded model W m k B cache.1.1 hCache
    (GeneralPaperStreamingPreparedClassifier.cache_positive model W m k) b hb hB hW).1
  have hCacheFoot := native W m k
  rw [←hCache] at hCacheFoot
  have hAlphabet : alphabetFootprint W cache.1.2≤3*(payload m k+W)+96*W := by
    dsimp only [cache]
    rw [GeneralPaperPrecallCachePrice.prepare_data]
    exact alphabet W m k
  have hReturn := returned model W m k b hb
  have hRatio := rationalWordWidth_of_height hB
  have hWork := GeneralPaperFastInputClassifier.prepare_work model W m k b hb B hB
  change result.2≤GeneralPaperFastInputClassifier.prepareProfile model W m k B at hWork
  have hWorkEq : result.2=cache.2+classified.2+32*W := rfl
  have hCachePrice := GeneralPaperPrecallCachePrice.prepare_work model.rat model.monotone W m k
  have hInput := GeneralPaperPrecallConstructorBounds.input_words m k
  have hm := hInput m (by simp)
  have hk := hInput k (by simp)
  have hWN := GeneralPaperInitializerControlCounters.word_le_self W
  have cost (z : ℕ) (hz : z≤GeneralPaperFastInputClassifier.prepareProfile model W m k B) :
      natBits z≤payload m k+natBits (GeneralPaperFastInputClassifier.prepareProfile model W m k B)+W+8 := by
    have h := Nat.add_le_add_left (binaryWordWidth_mono hz) 1
    change natBits z≤natBits (GeneralPaperFastInputClassifier.prepareProfile model W m k B) at h
    omega
  have hf := fields_bound W (payload m k+natBits (GeneralPaperFastInputClassifier.prepareProfile model W m k B)+W+8)
    [m,k,W,cache.2,classified.2,result.2,cache.2+classified.2,32*W,24*W,56*W] (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · omega
    · omega
    · unfold natBits;omega
    · exact cost _ (by omega)
    · exact cost _ (by omega)
    · exact cost _ (by omega)
    · exact cost _ (by omega)
    · exact cost _ (by omega)
    · exact cost _ (by omega)
    · apply cost
      dsimp only [GeneralPaperFastInputClassifier.prepareProfile]
      omega)
  change fields W _≤10*((payload m k+natBits (GeneralPaperFastInputClassifier.prepareProfile model W m k B)+W+8)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  dsimp only [window,profile]
  dsimp only [cache,classified,result] at *
  omega

theorem retained_inputs (model : RationalCostModel) (W m k : ℕ) (b : ℚ) :
    let cache := GeneralPaperPrecallCachePrice.prepare model.rat W m k
    footprint W cache.1.1+alphabetFootprint W cache.1.2+rationalWordWidth b+
      GeneralPaperClassifierResultStorage.frontFootprint W (GeneralPaperFastInputClassifier.prepare model W m k b).1≤window model W m k b := by
  dsimp only [window]
  omega

end Blotto.GeneralPaperFastPreparedFrontStorage
