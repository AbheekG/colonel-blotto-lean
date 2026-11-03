import Blotto.GeneralPaperFastQueryStorage

/-! Actual fast classifier parent, retaining the full queried records,
cache and original ratio during selection and return. All eighteen native
price/counter fields are counted. The unchanged selection child supplies
its actual scalar primitive bound; no legacy bit quotient is executed. -/
namespace Blotto.GeneralPaperFastClassifierStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def window (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (hQ : 0<c.proxy.Qg) (b : ℚ) : ℕ :=
  let queried := GeneralPaperFastInputClassifier.query model W c b
  let selected := GeneralPaperSelectionBits.run model W c.proxy.Qg queried.1.1.quotient hQ b queried.1.2.fraction
  let result := GeneralPaperFastInputClassifier.run model W c hQ b
  GeneralPaperFastQueryStorage.window model W c b+footprint W c+rationalWordWidth b+
    GeneralPaperQuotientConstructionStorage.record W queried.1.1+GeneralPaperStreamingQuerySpace.resultFootprint W queried.1.2+
    GeneralPaperSelectionConstructionStorage.window model W c.proxy.Qg queried.1.1.quotient hQ b queried.1.2.fraction+
    GeneralPaperClassifierResultStorage.footprint W result.1+
    fields W [W,c.proxy.Qg,c.proxy.work,queried.2,selected.2,result.2,queried.2+selected.2,64*W,
      queried.1.1.work,queried.1.2.work,selected.1.work,c.proxy.work+queried.1.1.work,
      c.proxy.work+queried.1.1.work+queried.1.2.work,c.proxy.work+queried.1.1.work+queried.1.2.work+selected.1.work,
      result.1.work,24,queried.1.1.quotient,c.proxy.gridBits+3]+192*W

def profile (model : RationalCostModel) (W m k B : ℕ) : ℕ :=
  2*GeneralPaperFastQueryStorage.profile model W m k B+
    GeneralPaperSelectionConstructionStorage.profile model W (GeneralPaperProxyParameters.prepare m k).Qg B+
    GeneralPaperClassifierResultStorage.profile W m k+
    18*(payload m k+natBits (GeneralPaperFastInputClassifier.profile model W m k B)+2*W+8)+224*W

theorem native_work_cap (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (hQ : 0<c.proxy.Qg) (b : ℚ) (hb : 0<b ∧ b<1) :
    (GeneralPaperFastInputClassifier.run model W c hQ b).1.work≤256*GeneralPaperPrecallControlWord.measure m k+1024 := by
  have h := GeneralPaperProxyClassifier.classify_work m k (b:ℝ) (by exact_mod_cast hb)
  have hs := GeneralPaperPrecallControlWord.root_controls m k
  rw [GeneralPaperFastInputClassifier.classifier_data model W m k c hc hQ b hb]
  change (GeneralPaperProxyClassifier.classify m k (b:ℝ)).work≤
    (GeneralPaperProxyParameters.prepare m k).work+182*(GeneralPaperProxyParameters.prepare m k).gridBits+966 at h
  change (GeneralPaperProxyParameters.prepare m k).gridBits+4≤GeneralPaperPrecallControlWord.measure m k ∧
    (GeneralPaperProxyParameters.prepare m k).work≤44*GeneralPaperPrecallControlWord.measure m k+56 at hs
  omega

theorem selected_bound (model : RationalCostModel) (W m k B : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (hQ : 0<c.proxy.Qg) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    let queried := GeneralPaperFastInputClassifier.query model W c b
    GeneralPaperSelectionConstructionStorage.window model W c.proxy.Qg queried.1.1.quotient hQ b queried.1.2.fraction≤
      GeneralPaperSelectionConstructionStorage.profile model W (GeneralPaperProxyParameters.prepare m k).Qg B := by
  have hRoot : ∀ f,(GeneralPaperFastInputClassifier.query model W c b).1.2.fraction=some f → f.num≤2*c.proxy.Qg ∧ f.den≤2*c.proxy.Qg := by
    rw [GeneralPaperFastInputClassifier.query_data model W m k c hc b hb,GeneralPaperStreamingCachedRoot.data_agrees]
    exact GeneralPaperClassifierRootBounds.root_bounds model W m k c hc b hb
  have hCell : (GeneralPaperFastInputClassifier.query model W c b).1.1.quotient<c.proxy.Qg := by
    change (GeneralPaperFastInputQuotient.run model W c b).1.quotient<c.proxy.Qg
    rw [GeneralPaperFastInputQuotient.data model W m k c hc b hb]
    exact (GeneralPaperProxyQuotientPrice.quotient_cell model W m k c hc b hb).1
  have h := GeneralPaperSelectionConstructionStorage.bounded model W c.proxy.Qg
    (GeneralPaperFastInputClassifier.query model W c b).1.1.quotient B hQ b
    (GeneralPaperFastInputClassifier.query model W c b).1.2.fraction hCell hB hRoot
  have he : GeneralPaperSelectionConstructionStorage.profile model W c.proxy.Qg B=
      GeneralPaperSelectionConstructionStorage.profile model W (GeneralPaperProxyParameters.prepare m k).Qg B := by rw [hc];rfl
  exact h.trans_eq he

theorem bounded (model : RationalCostModel) (W m k B : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (hQ : 0<c.proxy.Qg) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) :
    window model W c hQ b≤profile model W m k B ∧
      (GeneralPaperFastInputClassifier.run model W c hQ b).2≤GeneralPaperFastInputClassifier.profile model W m k B := by
  let queried := GeneralPaperFastInputClassifier.query model W c b
  let selected := GeneralPaperSelectionBits.run model W c.proxy.Qg queried.1.1.quotient hQ b queried.1.2.fraction
  let result := GeneralPaperFastInputClassifier.run model W c hQ b
  have hQuery := (GeneralPaperFastQueryStorage.bounded model W m k B c hc b hb hB hW).1
  have hInputs := (GeneralPaperFastQueryStorage.retained_inputs model W c b).trans hQuery
  have hSelected := selected_bound model W m k B c hc hQ b hb hB
  have hResult : GeneralPaperClassifierResultStorage.footprint W result.1≤GeneralPaperClassifierResultStorage.profile W m k := by
    rw [GeneralPaperFastInputClassifier.classifier_data model W m k c hc hQ b hb]
    exact GeneralPaperClassifierResultStorage.native W m k (b:ℝ) (by exact_mod_cast hb)
  have hWork := GeneralPaperFastInputClassifier.work model W m k c hc hQ b hb B hB
  change result.2≤GeneralPaperFastInputClassifier.profile model W m k B at hWork
  have hWorkEq : result.2=queried.2+selected.2+64*W := rfl
  have hNative := native_work_cap model W m k c hc hQ b hb
  change result.1.work≤256*GeneralPaperPrecallControlWord.measure m k+1024 at hNative
  have hNativeEq : result.1.work=c.proxy.work+queried.1.1.work+queried.1.2.work+selected.1.work+24 := rfl
  have hn (z : ℕ) (hz : z≤result.1.work) : natBits z≤payload m k+natBits (GeneralPaperFastInputClassifier.profile model W m k B)+W+8 := by
    have h := small m k z (hz.trans hNative)
    omega
  have cost (z : ℕ) (hz : z≤GeneralPaperFastInputClassifier.profile model W m k B) :
      natBits z≤payload m k+natBits (GeneralPaperFastInputClassifier.profile model W m k B)+W+8 := by
    have h := Nat.add_le_add_left (binaryWordWidth_mono hz) 1
    change natBits z≤natBits (GeneralPaperFastInputClassifier.profile model W m k B) at h
    omega
  have hWords := (words m k).2.1
  rw [←hc] at hWords
  have hQword := hWords c.proxy.Qg (by simp)
  have hCell : queried.1.1.quotient<c.proxy.Qg := by
    change (GeneralPaperFastInputQuotient.run model W c b).1.quotient<c.proxy.Qg
    rw [GeneralPaperFastInputQuotient.data model W m k c hc b hb]
    exact (GeneralPaperProxyQuotientPrice.quotient_cell model W m k c hc b hb).1
  have hCellWord : natBits queried.1.1.quotient≤payload m k :=
    (Nat.add_le_add_left (binaryWordWidth_mono hCell.le) 1).trans hQword
  have hD : natBits (c.proxy.gridBits+3)≤payload m k := by
    have h := (GeneralPaperPrecallControlWord.root_controls m k).1
    change (GeneralPaperPrecallCachePrice.specification m k).proxy.gridBits+4≤GeneralPaperPrecallControlWord.measure m k at h
    rw [←hc] at h
    exact small m k _ (by omega)
  have hWN := GeneralPaperInitializerControlCounters.word_le_self W
  have hf := fields_bound W (payload m k+natBits (GeneralPaperFastInputClassifier.profile model W m k B)+W+8)
    [W,c.proxy.Qg,c.proxy.work,queried.2,selected.2,result.2,queried.2+selected.2,64*W,
      queried.1.1.work,queried.1.2.work,selected.1.work,c.proxy.work+queried.1.1.work,
      c.proxy.work+queried.1.1.work+queried.1.2.work,c.proxy.work+queried.1.1.work+queried.1.2.work+selected.1.work,
      result.1.work,24,queried.1.1.quotient,c.proxy.gridBits+3] (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · unfold natBits;omega
    · omega
    · exact hn _ (by omega)
    · exact cost _ (by omega)
    · exact cost _ (by omega)
    · exact cost _ (by omega)
    · exact cost _ (by omega)
    · exact cost _ (by omega)
    · exact hn _ (by omega)
    · exact hn _ (by omega)
    · exact hn _ (by omega)
    · exact hn _ (by omega)
    · exact hn _ (by omega)
    · exact hn _ (by omega)
    · exact hn _ (by omega)
    · exact hn _ (by omega)
    · omega
    · omega)
  change fields W _≤18*((payload m k+natBits (GeneralPaperFastInputClassifier.profile model W m k B)+W+8)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  dsimp only [window,profile]
  dsimp only [queried,selected,result] at *
  omega

theorem retained_inputs (model : RationalCostModel) (W : ℕ) (c : GeneralPaperPrecallCachePrice.Cache) (hQ : 0<c.proxy.Qg) (b : ℚ) :
    footprint W c+rationalWordWidth b+GeneralPaperClassifierResultStorage.footprint W (GeneralPaperFastInputClassifier.run model W c hQ b).1≤
      window model W c hQ b := by
  dsimp only [window]
  omega

end Blotto.GeneralPaperFastClassifierStorage
