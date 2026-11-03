import Blotto.GeneralPaperPrecallIndexWords

/-! Apply the shared word to actual source/root CF prefixes and full
classifier metadata. Every capacity follows from constructed parameters
and the actual budget/cell conditions, without a supplied width oracle.
-/
namespace Blotto.GeneralPaperClassifierControlWords
open GeneralPaperPrecallControlWord
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem root_prefix (m k j fuel : ℕ) (hj : j<(GeneralPaperProxyParameters.prepare m k).Qg)
    (hFuel : fuel≤2*((GeneralPaperProxyParameters.prepare m k).gridBits+3)+4) :
    let r := GeneralPaperProxyParameters.prepare m k
    let s := GeneralPaperRegularCFLoop.run r.H (r.gridBits+3+2) fuel (GeneralPaperRegularCFLoop.initial r.Qg j)
    binaryWordWidth (s.steps+1)≤word m k ∧ binaryWordWidth (s.quotientDepth+(r.gridBits+3)+2)≤word m k ∧
    binaryWordWidth (s.zeroChecks+1)≤word m k ∧ binaryWordWidth (s.work+512)≤word m k := by
  have hc := GeneralPaperCFControlWords.prefix_words (GeneralPaperProxyParameters.prepare m k).H
    (GeneralPaperProxyParameters.prepare m k).Qg j ((GeneralPaperProxyParameters.prepare m k).gridBits+3) fuel
    (GeneralPaperProxyParameters.H_positive m k) (GeneralPaperProxyParameters.grid_positive m k) hj
    (GeneralPaperProxyClassifier.grid_dyadic m k) hFuel
  have hw := GeneralPaperPrecallLoopWords.root_CF m k
  dsimp only at hc ⊢
  exact ⟨hc.1.trans hw,hc.2.1.trans hw,hc.2.2.1.trans hw,hc.2.2.2.trans hw⟩

theorem source_prefix (m k j fuel : ℕ) (hj : j<(GeneralPaperProxyParameters.alphabet m k).C)
    (hFuel : fuel≤2*(GeneralPaperProxyParameters.alphabet m k).lambda+4) :
    let a := GeneralPaperProxyParameters.alphabet m k
    let s := GeneralPaperRegularCFLoop.run a.D (a.lambda+2) fuel (GeneralPaperRegularCFLoop.initial a.C j)
    binaryWordWidth (s.steps+1)≤word m k ∧ binaryWordWidth (s.quotientDepth+a.lambda+2)≤word m k ∧
    binaryWordWidth (s.zeroChecks+1)≤word m k ∧ binaryWordWidth (s.work+512)≤word m k := by
  let a := GeneralPaperProxyParameters.alphabet m k
  have hc := GeneralPaperCFControlWords.prefix_words a.D a.C j a.lambda fuel
    a.orderPositive a.scalePositive hj a.dyadic hFuel
  have hw := GeneralPaperPrecallLoopWords.source_CF m k
  dsimp only at hc ⊢
  exact ⟨hc.1.trans hw,hc.2.1.trans hw,hc.2.2.1.trans hw,hc.2.2.2.trans hw⟩

theorem selection (m k Q j : ℕ) (hQ : 0<Q) (b : ℝ) (root : Option Farey.Fraction) :
    binaryWordWidth ((GeneralPaperProxySelection.select Q j hQ b root).work+64)≤word m k := by
  have hs := GeneralPaperProxySelection.selected_work Q j hQ b root
  have hw := bounded m k ((GeneralPaperProxySelection.select Q j hQ b root).work+64) (by unfold cap; omega)
  omega

theorem classifier_metadata (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    binaryWordWidth ((GeneralPaperProxyClassifier.classify m k b).work+128)≤word m k := by
  have hc := GeneralPaperProxyClassifier.classify_work m k b hb
  have hr := root_controls m k
  dsimp only at hr
  have hw := bounded m k ((GeneralPaperProxyClassifier.classify m k b).work+128) (by unfold cap; omega)
  omega

theorem returned_metadata (model : RationalCostModel) (m k : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) :
    binaryWordWidth ((GeneralPaperPreparedClassifierBits.prepare model (word m k) m k b).1.2.work+128)≤word m k := by
  rw [GeneralPaperPreparedClassifierBits.data]
  have hReal : (0:ℝ)<b ∧ (b:ℝ)<1 := by exact_mod_cast hb
  exact classifier_metadata m k (b:ℝ) hReal

end Blotto.GeneralPaperClassifierControlWords
