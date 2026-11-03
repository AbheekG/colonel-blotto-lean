import Blotto.GeneralPaperFastInputQuotientStorageRates

/-! Actual fast quotient/root-query parent. The original ratio and complete
cache, both complete child/returned records, fast scalar frame, streaming
CF frontier and ten native parent fields coexist. Work is encoded metadata
only. No old quotient is executed or used as primitive scratch. -/
namespace Blotto.GeneralPaperFastQueryStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def rootPrice (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  let p := GeneralPaperProxyParameters.prepare m k
  1024*(W+model.rat (GeneralPaperCFOperandPrice.width (p.gridBits+3) p.H))

def recordPrice (W m k B : ℕ) : ℕ :=
  let p := GeneralPaperProxyParameters.prepare m k
  4*(1+2*GeneralPaperBoundedQuotient.heightBudget (B+binaryWordWidth p.Qg) 1 (p.gridBits+1))+128*W

theorem returned_record (model : RationalCostModel) (W m k B : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    GeneralPaperQuotientConstructionStorage.record W (GeneralPaperFastInputQuotient.run model W c b).1≤recordPrice W m k B := by
  rw [GeneralPaperFastInputQuotient.data model W m k c hc b hb,GeneralPaperProxyQuotientPrice.data]
  have hQ : (0:ℚ)<c.proxy.Qg := by rw [hc];exact_mod_cast GeneralPaperProxyParameters.grid_positive m k
  have hPow : (c.proxy.Qg:ℚ)=(2:ℚ)^c.proxy.gridBits := by rw [hc];exact_mod_cast GeneralPaperProxyParameters.grid_power m k
  have hCap : b*(c.proxy.Qg:ℚ)<(1:ℚ)*(2:ℚ)^(c.proxy.gridBits+1) := by rw [pow_succ,←hPow];nlinarith only [hb.2,hQ]
  have h := GeneralPaperQuotientConstructionStorage.record_bound W (b*(c.proxy.Qg:ℚ)) 1 (by norm_num)
    (c.proxy.gridBits+1) (B+binaryWordWidth c.proxy.Qg) 1 (mul_nonneg hb.1.le hQ.le) hCap
    (hB.mul (GeneralPaperBasisDivideBits.nat_height c.proxy.Qg)) (by norm_num [RationalHeight])
  rw [hc] at h
  rw [hc]
  exact h

def window (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) : ℕ :=
  let location := GeneralPaperFastInputQuotient.run model W c b
  let root := GeneralPaperStreamingMidpointQuery.run model W true c.proxy.H c.proxy.Qg location.1.quotient (c.proxy.gridBits+3)
  let result := GeneralPaperFastInputClassifier.query model W c b
  rationalWordWidth b+footprint W c+GeneralPaperFastInputQuotientStorageRates.window model W c b+
    GeneralPaperStreamingQuerySpace.peak model W true c.proxy.H c.proxy.Qg location.1.quotient (c.proxy.gridBits+3)+
    2*GeneralPaperQuotientConstructionStorage.record W location.1+2*GeneralPaperStreamingQuerySpace.resultFootprint W root.1+
    fields W [W,c.proxy.H,c.proxy.Qg,c.proxy.gridBits,c.proxy.gridBits+3,location.2,root.2,result.2,location.2+root.2,64*W]+192*W

def profile (model : RationalCostModel) (W m k B : ℕ) : ℕ :=
  (1+2*B)+18*(payload m k+W)+160*W+GeneralPaperFastInputQuotientStorageRates.storageProfile model W m k B+
    3*rootPrice model W m k+2*recordPrice W m k B+
    10*(payload m k+natBits (GeneralPaperFastInputClassifier.queryProfile model W m k B)+2*W+8)+224*W

theorem root_children (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) :
    let location := GeneralPaperFastInputQuotient.run model W c b
    let root := GeneralPaperStreamingMidpointQuery.run model W true c.proxy.H c.proxy.Qg location.1.quotient (c.proxy.gridBits+3)
    GeneralPaperStreamingQuerySpace.peak model W true c.proxy.H c.proxy.Qg location.1.quotient (c.proxy.gridBits+3)≤rootPrice model W m k ∧
      GeneralPaperStreamingQuerySpace.resultFootprint W root.1≤rootPrice model W m k := by
  have ht := (GeneralPaperProxyQuotientPrice.quotient_cell model W m k c hc b hb).1
  rw [←GeneralPaperFastInputQuotient.data model W m k c hc b hb] at ht
  have hD : 0<c.proxy.H := by rw [hc];exact GeneralPaperProxyParameters.H_positive m k
  have hQ : 0<c.proxy.Qg := by rw [hc];exact GeneralPaperProxyParameters.grid_positive m k
  have hPower : 8*c.proxy.Qg=2^(c.proxy.gridBits+3) := by rw [hc];exact GeneralPaperProxyClassifier.grid_dyadic m k
  have hControl : GeneralPaperCFControlWords.width (c.proxy.gridBits+3)≤W := by
    rw [hc]
    exact (GeneralPaperPrecallLoopWords.root_CF m k).trans hW
  have hp := GeneralPaperStreamingQuerySpace.peak_bound model W c.proxy.H c.proxy.Qg
    (GeneralPaperFastInputQuotient.run model W c b).1.quotient (c.proxy.gridBits+3) true hD hQ ht hPower hControl
  have hRet := GeneralPaperClassifierConstructionStorage.query_return model W c.proxy.H c.proxy.Qg
    (GeneralPaperFastInputQuotient.run model W c b).1.quotient (c.proxy.gridBits+3) true
  have hPrice : 1024*(W+model.rat (GeneralPaperCFOperandPrice.width (c.proxy.gridBits+3) c.proxy.H))=rootPrice model W m k := by rw [hc];rfl
  rw [hPrice] at hp
  exact ⟨hp,hRet.trans hp⟩

theorem bounded (model : RationalCostModel) (W m k B : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) :
    window model W c b≤profile model W m k B ∧
      (GeneralPaperFastInputClassifier.query model W c b).2≤GeneralPaperFastInputClassifier.queryProfile model W m k B := by
  let location := GeneralPaperFastInputQuotient.run model W c b
  let root := GeneralPaperStreamingMidpointQuery.run model W true c.proxy.H c.proxy.Qg location.1.quotient (c.proxy.gridBits+3)
  let result := GeneralPaperFastInputClassifier.query model W c b
  have hRoot := root_children model W m k c hc b hb hW
  have hRecord := returned_record model W m k B c hc b hb hB
  have hScalar := GeneralPaperFastInputQuotientStorageRates.bounded model W m k B c hc b hB
  have hCache := native W m k
  rw [←hc] at hCache
  have hRatio := rationalWordWidth_of_height hB
  have hWork := GeneralPaperFastInputClassifier.query_work model W m k c hc b hb B hB
  change result.2≤GeneralPaperFastInputClassifier.queryProfile model W m k B at hWork
  have hWorkEq : result.2=location.2+root.2+64*W := rfl
  have hCacheWords := (words m k).2.1
  rw [←hc] at hCacheWords
  have hH := hCacheWords c.proxy.H (by simp)
  have hQ := hCacheWords c.proxy.Qg (by simp)
  have hG := hCacheWords c.proxy.gridBits (by simp)
  have hD : natBits (c.proxy.gridBits+3)≤payload m k := by
    have h := (GeneralPaperPrecallControlWord.root_controls m k).1
    change (GeneralPaperPrecallCachePrice.specification m k).proxy.gridBits+4≤GeneralPaperPrecallControlWord.measure m k at h
    rw [←hc] at h
    exact small m k _ (by omega)
  have hWN := GeneralPaperInitializerControlCounters.word_le_self W
  have cost (z : ℕ) (hz : z≤GeneralPaperFastInputClassifier.queryProfile model W m k B) :
      natBits z≤payload m k+natBits (GeneralPaperFastInputClassifier.queryProfile model W m k B)+W+8 := by
    have h := Nat.add_le_add_left (binaryWordWidth_mono hz) 1
    change natBits z≤natBits (GeneralPaperFastInputClassifier.queryProfile model W m k B) at h
    omega
  have hf := fields_bound W (payload m k+natBits (GeneralPaperFastInputClassifier.queryProfile model W m k B)+W+8)
    [W,c.proxy.H,c.proxy.Qg,c.proxy.gridBits,c.proxy.gridBits+3,location.2,root.2,result.2,location.2+root.2,64*W] (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · unfold natBits;omega
    · omega
    · omega
    · omega
    · omega
    all_goals apply cost;omega)
  change fields W _≤10*((payload m k+natBits (GeneralPaperFastInputClassifier.queryProfile model W m k B)+W+8)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  dsimp only [window,profile]
  change rationalWordWidth b+footprint W c+GeneralPaperFastInputQuotientStorageRates.window model W c b+
    GeneralPaperStreamingQuerySpace.peak model W true c.proxy.H c.proxy.Qg location.1.quotient (c.proxy.gridBits+3)+
    2*GeneralPaperQuotientConstructionStorage.record W location.1+2*GeneralPaperStreamingQuerySpace.resultFootprint W root.1+
    fields W [W,c.proxy.H,c.proxy.Qg,c.proxy.gridBits,c.proxy.gridBits+3,location.2,root.2,result.2,location.2+root.2,64*W]+192*W≤_
  dsimp only [location,root,result] at *
  omega

theorem retained_inputs (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (b : ℚ) :
    footprint W c+rationalWordWidth b+
      GeneralPaperQuotientConstructionStorage.record W (GeneralPaperFastInputClassifier.query model W c b).1.1+
      GeneralPaperStreamingQuerySpace.resultFootprint W (GeneralPaperFastInputClassifier.query model W c b).1.2≤window model W c b := by
  dsimp only [window,GeneralPaperFastInputClassifier.query]
  omega

end Blotto.GeneralPaperFastQueryStorage
