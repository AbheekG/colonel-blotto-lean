import Blotto.GeneralPaperProxyLocationStorage
import Blotto.GeneralPaperClassifierResultStorage

/-! One native classifier phase with simultaneous cache/alphabet, location
return, streaming CF result, selection temporaries, caller annotations and
full returned classifier. The cache constructor is a separate earlier phase.
W is explicit, with its actual precall calibration discharged below. -/
namespace Blotto.GeneralPaperClassifierConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem query_return (model : RationalCostModel) (W D C j lambda : ℕ) (closed : Bool) :
    GeneralPaperStreamingQuerySpace.resultFootprint W
      (GeneralPaperStreamingMidpointQuery.run model W closed D C j lambda).1≤
        GeneralPaperStreamingQuerySpace.peak model W closed D C j lambda := by
  simp only [GeneralPaperStreamingMidpointQuery.run,GeneralPaperStreamingMidpointRaw.data,
    GeneralPaperMidpointFilterBits.run]
  unfold GeneralPaperStreamingQuerySpace.peak GeneralPaperStreamingQuerySpace.filterWindow
  omega

def annotations (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (q : GeneralPaperBoundedQuotient.Result × GeneralPaperMidpointQuery.Result)
    (s : GeneralPaperProxySelection.Selected) : ℕ :=
  fields W [c.proxy.work+q.1.work,c.proxy.work+q.1.work+q.2.work,
    c.proxy.work+q.1.work+q.2.work+s.work]

def window (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hQ : 0<c.proxy.Qg) (b : ℚ) : ℕ :=
  let q := (GeneralPaperStreamingCachedRoot.run model W c b).1
  let s := (GeneralPaperSelectionBits.run model W c.proxy.Qg q.1.quotient hQ b q.2.fraction).1
  footprint W c+alphabetFootprint W (GeneralPaperProxyParameters.alphabet m k)+
    GeneralPaperProxyLocationStorage.window model W c b+
    GeneralPaperStreamingQuerySpace.peak model W true c.proxy.H c.proxy.Qg q.1.quotient (c.proxy.gridBits+3)+
    GeneralPaperStreamingQuerySpace.resultFootprint W q.2+
    GeneralPaperSelectionConstructionStorage.window model W c.proxy.Qg q.1.quotient hQ b q.2.fraction+
    GeneralPaperClassifierResultStorage.footprint W (GeneralPaperStreamingClassifier.run model W c hQ b).1+
      annotations W c q s+512*W

def profile (model : RationalCostModel) (W m k B : ℕ) : ℕ :=
  let c := GeneralPaperPrecallCachePrice.specification m k
  24*payload m k+824*W+GeneralPaperProxyLocationStorage.profile model W c B+
    2048*(W+model.rat (GeneralPaperCFOperandPrice.width (c.proxy.gridBits+3) c.proxy.H))+
    GeneralPaperSelectionConstructionStorage.profile model W c.proxy.Qg B+
    GeneralPaperClassifierResultStorage.profile W m k

theorem bounded (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (hQ : 0<c.proxy.Qg)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) : window model W m k c hQ b≤profile model W m k B := by
  let q := (GeneralPaperStreamingCachedRoot.run model W c b).1
  let s := (GeneralPaperSelectionBits.run model W c.proxy.Qg q.1.quotient hQ b q.2.fraction).1
  have hj := (GeneralPaperProxyQuotientPrice.quotient_cell model W m k c hc b hb).1
  change q.1.quotient<c.proxy.Qg at hj
  have hroot : ∀ f,q.2.fraction=some f → f.num≤2*c.proxy.Qg ∧ f.den≤2*c.proxy.Qg := by
    dsimp only [q]
    rw [GeneralPaperStreamingCachedRoot.data_agrees]
    exact GeneralPaperClassifierRootBounds.root_bounds model W m k c hc b hb
  have hloc := GeneralPaperProxyLocationStorage.bounded model W m k c hc b hb B hB
  have hControl : GeneralPaperCFControlWords.width (c.proxy.gridBits+3)≤W := by
    have h : GeneralPaperCFControlWords.width (c.proxy.gridBits+3)≤GeneralPaperPrecallControlWord.word m k := by
      rw [hc]
      exact GeneralPaperPrecallLoopWords.root_CF m k
    exact h.trans hW
  have hcf := GeneralPaperStreamingQuerySpace.peak_bound model W c.proxy.H c.proxy.Qg q.1.quotient
    (c.proxy.gridBits+3) true (by rw [hc]; exact GeneralPaperProxyParameters.H_positive m k) hQ hj
    (by rw [hc]; exact GeneralPaperProxyClassifier.grid_dyadic m k)
    hControl
  have hret := query_return model W c.proxy.H c.proxy.Qg q.1.quotient (c.proxy.gridBits+3) true
  change GeneralPaperStreamingQuerySpace.resultFootprint W q.2≤_ at hret
  have hsel := GeneralPaperSelectionConstructionStorage.bounded model W c.proxy.Qg q.1.quotient B hQ b q.2.fraction hj hB hroot
  have hfinal := GeneralPaperClassifierResultStorage.returned model W m k c hc hQ b hb
  have hcache := native W m k
  rw [←hc] at hcache
  have halphabet := alphabet W m k
  have hreal : (0:ℝ)<b ∧ (b:ℝ)<1 := by exact_mod_cast hb
  have hn := GeneralPaperProxyClassifier.classify_work m k (b:ℝ) hreal
  have hp := GeneralPaperPrecallControlWord.root_controls m k
  have hdata := congrArg GeneralPaperProxyClassifier.Result.work
    (GeneralPaperStreamingClassifier.data model W m k c hc hQ b)
  change c.proxy.work+q.1.work+q.2.work+s.work+24=(GeneralPaperProxyClassifier.classify m k (b:ℝ)).work at hdata
  change (GeneralPaperProxyClassifier.classify m k (b:ℝ)).work≤
    (GeneralPaperPrecallCachePrice.specification m k).proxy.work+
      182*(GeneralPaperPrecallCachePrice.specification m k).proxy.gridBits+966 at hn
  rw [←hc] at hn
  change (GeneralPaperPrecallCachePrice.specification m k).proxy.gridBits+4≤GeneralPaperPrecallControlWord.measure m k ∧
    (GeneralPaperPrecallCachePrice.specification m k).proxy.work≤44*GeneralPaperPrecallControlWord.measure m k+56 at hp
  rw [←hc] at hp
  change c.proxy.gridBits+4≤GeneralPaperPrecallControlWord.measure m k ∧
    c.proxy.work≤44*GeneralPaperPrecallControlWord.measure m k+56 at hp
  have hsmall (n : ℕ) (hn' : n≤(GeneralPaperProxyClassifier.classify m k (b:ℝ)).work) :
      natBits n≤payload m k := small m k n (by omega)
  have hann := fields_bound W (payload m k)
    [c.proxy.work+q.1.work,c.proxy.work+q.1.work+q.2.work,c.proxy.work+q.1.work+q.2.work+s.work] (by
      intro n hn'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn'
      rcases hn' with rfl|rfl|rfl <;> apply hsmall <;> omega)
  change annotations W c q s≤3*(payload m k+W)+32*W at hann
  unfold window profile
  dsimp only
  change footprint W c+alphabetFootprint W (GeneralPaperProxyParameters.alphabet m k)+
    GeneralPaperProxyLocationStorage.window model W c b+
    GeneralPaperStreamingQuerySpace.peak model W true c.proxy.H c.proxy.Qg q.1.quotient (c.proxy.gridBits+3)+
    GeneralPaperStreamingQuerySpace.resultFootprint W q.2+
    GeneralPaperSelectionConstructionStorage.window model W c.proxy.Qg q.1.quotient hQ b q.2.fraction+
    GeneralPaperClassifierResultStorage.footprint W (GeneralPaperStreamingClassifier.run model W c hQ b).1+
    annotations W c q s+512*W≤_
  rw [←hc]
  omega

theorem source_word (model : RationalCostModel) (m k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) :
    window model (GeneralPaperSourcePrecallPreparation.word m k Qv) m k
      (GeneralPaperPrecallCachePrice.specification m k) (GeneralPaperProxyParameters.grid_positive m k) b≤
        profile model (GeneralPaperSourcePrecallPreparation.word m k Qv) m k B :=
  bounded model _ m k _ rfl _ (GeneralPaperSourcePrecallPreparation.front_word m k Qv) b hb B hB

end Blotto.GeneralPaperClassifierConstructionStorage
