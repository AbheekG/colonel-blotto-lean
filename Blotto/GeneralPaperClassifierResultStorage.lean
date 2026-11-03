import Blotto.GeneralPaperSelectionStorage
import Blotto.GeneralPaperStreamingPreparedClassifier

/-! Complete native classifier return, including optional root, modification
tag, endpoint and native work annotations. Its stored size is independent of
the rational height of the original budget. -/
namespace Blotto.GeneralPaperClassifierResultStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint (W : ℕ) (r : GeneralPaperProxyClassifier.Result) : ℕ :=
  fields W [r.cell,r.work]+GeneralPaperSelectionStorage.root W r.root+
    GeneralPaperSelectionStorage.selected W r.choice+64*W

def profile (W m k : ℕ) : ℕ :=
  2*payload m k+6*GeneralPaperSelectionPoints.width (GeneralPaperProxyParameters.prepare m k).Qg 0+328*W

theorem root_caps (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    ∀ f,(GeneralPaperProxyClassifier.classify m k b).root=some f →
      f.num≤2*(GeneralPaperProxyParameters.prepare m k).Qg ∧
        f.den≤2*(GeneralPaperProxyParameters.prepare m k).Qg := by
  intro f hf
  have hs := GeneralPaperProxyClassifier.root_sound m k b f hf
  have hc := (GeneralPaperProxyQuotient.locate_spec m k b hb).1
  change (GeneralPaperProxyClassifier.classify m k b).cell<(GeneralPaperProxyParameters.prepare m k).Qg at hc
  have hn := GeneralPaperClassifierRootBounds.cell_numerator _ _ f
    (GeneralPaperProxyParameters.grid_positive m k) hc hs.2
  have hH := GeneralPaperProxyParameters.H_positive m k
  have hGrid := GeneralPaperProxyParameters.grid_lower m k
  have hCap : (GeneralPaperProxyParameters.prepare m k).H≤2*(GeneralPaperProxyParameters.prepare m k).Qg := by
    nlinarith only [hH,hGrid]
  exact ⟨hn.trans (hs.1.trans hCap),hs.1.trans hCap⟩

theorem native (W m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    footprint W (GeneralPaperProxyClassifier.classify m k b)≤profile W m k := by
  let r := GeneralPaperProxyClassifier.classify m k b
  let p := GeneralPaperProxyParameters.prepare m k
  have hc := (GeneralPaperProxyQuotient.locate_spec m k b hb).1
  change r.cell<p.Qg at hc
  have hQ : natBits p.Qg≤payload m k := (words m k).2.1 _ (by simp [p,GeneralPaperPrecallCachePrice.specification])
  have hCell : natBits r.cell≤payload m k := by
    have hw := binaryWordWidth_mono hc.le
    unfold natBits at hQ ⊢
    omega
  have hw := GeneralPaperProxyClassifier.classify_work m k b hb
  have hp := GeneralPaperPrecallControlWord.root_controls m k
  change p.gridBits+4≤GeneralPaperPrecallControlWord.measure m k ∧
    p.work≤44*GeneralPaperPrecallControlWord.measure m k+56 at hp
  have hWork : natBits r.work≤payload m k := small m k r.work (by
    change r.work≤p.work+182*p.gridBits+966 at hw
    omega)
  have hFields := fields_bound W (payload m k) [r.cell,r.work] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl <;> assumption)
  change _≤2*(payload m k+W)+32*W at hFields
  have hRoot := GeneralPaperSelectionStorage.root_bound W p.Qg r.root (root_caps m k b hb)
  have hSelected := GeneralPaperSelectionStorage.selected_bound W p.Qg r.cell
    (GeneralPaperProxyParameters.grid_positive m k) hc b r.root (root_caps m k b hb)
  change GeneralPaperSelectionStorage.selected W r.choice≤_ at hSelected
  change fields W [r.cell,r.work]+GeneralPaperSelectionStorage.root W r.root+
    GeneralPaperSelectionStorage.selected W r.choice+64*W≤profile W m k
  unfold profile
  dsimp only [p] at *
  omega

theorem returned (model : RationalCostModel) (W m k : ℕ)
    (c : GeneralPaperPrecallCachePrice.Cache) (hc : c=GeneralPaperPrecallCachePrice.specification m k)
    (hQ : 0<c.proxy.Qg) (b : ℚ) (hb : 0<b ∧ b<1) :
    footprint W (GeneralPaperStreamingClassifier.run model W c hQ b).1≤profile W m k := by
  rw [GeneralPaperStreamingClassifier.data model W m k c hc hQ b]
  apply native W m k (b:ℝ)
  exact_mod_cast hb

def frontFootprint (W : ℕ)
    (r : (GeneralPaperPrecallCachePrice.Cache × GeneralPaperCodeAlphabet.Alphabet) × GeneralPaperProxyClassifier.Result) : ℕ :=
  GeneralPaperPrecallCacheStorage.footprint W r.1.1+alphabetFootprint W r.1.2+footprint W r.2+64*W

def frontProfile (W m k : ℕ) : ℕ := 21*(payload m k+W)+profile W m k+320*W

theorem front_native (W m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    frontFootprint W ((GeneralPaperPrecallCachePrice.specification m k,GeneralPaperProxyParameters.alphabet m k),
      GeneralPaperProxyClassifier.classify m k b)≤frontProfile W m k := by
  have hC := GeneralPaperPrecallCacheStorage.native W m k
  have hA := GeneralPaperPrecallCacheStorage.alphabet W m k
  have hR := native W m k b hb
  unfold frontFootprint frontProfile
  dsimp only
  omega

theorem front_returned (model : RationalCostModel) (W m k : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    frontFootprint W (GeneralPaperStreamingPreparedClassifier.prepare model W m k b).1≤frontProfile W m k := by
  rw [GeneralPaperStreamingPreparedClassifier.data]
  apply front_native W m k (b:ℝ)
  exact_mod_cast hb

theorem payload_profile (W m k : ℕ) : profile W m k≤128*payload m k+192+328*W := by
  have hQ : natBits (GeneralPaperProxyParameters.prepare m k).Qg≤payload m k :=
    (words m k).2.1 _ (by simp [GeneralPaperPrecallCachePrice.specification])
  unfold profile GeneralPaperSelectionPoints.width natBits at *
  omega

end Blotto.GeneralPaperClassifierResultStorage
