import Blotto.GeneralPaperProxySelectionPaths

/-! Root-free path and endpoint-direction guarantees of the ACTUAL
pre-call classifier. The root query's own soundness/absence certificates
discharge the branch analysis; no root/path oracle is supplied.
-/
namespace Blotto.GeneralPaperProxyClassifierPaths
open GeneralPaperProxyParameters GeneralPaperProxySelection GeneralPaperProxySelectionPaths
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem safe (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    Safe (prepare m k).H b (GeneralPaperProxyClassifier.classify m k b).choice := by
  have hc := GeneralPaperProxyQuotient.locate_spec m k b hb
  have hCell : (GeneralPaperBucketGeometry.lower (prepare m k).Qg (GeneralPaperProxyClassifier.classify m k b).cell:ℝ)≤b ∧
      b<(GeneralPaperBucketGeometry.upper (prepare m k).Qg (GeneralPaperProxyClassifier.classify m k b).cell:ℝ) := by
    have he : (GeneralPaperProxyClassifier.classify m k b).cell=(GeneralPaperProxyQuotient.locate m k b).quotient := rfl
    rw [he]
    simpa only [GeneralPaperBucketGeometry.lower,GeneralPaperBucketGeometry.upper,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_one]
      using hc.2
  exact select_safe _ _ _ (H_positive m k) (grid_positive m k) (grid_lower m k) b hCell _
    (GeneralPaperProxyClassifier.root_sound m k b)
    ((GeneralPaperProxyClassifier.root_none m k b hb).mp)

theorem unchanged (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify=none) :
    ((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)=b :=
  unchanged_eq _ b _ (safe m k b hb) hm

theorem denominator_large (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) :
    (prepare m k).H<(GeneralPaperProxyClassifier.classify m k b).choice.proxy.value.den :=
  modified_denominator _ b _ (safe m k b hb) hm

theorem open_path (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) (x : ℚ) (hx : x.den≤(prepare m k).H) :
    ¬GeneralPaperProxyCellPaths.Between (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint x :=
  modified_path _ b _ (safe m k b hb) hm x hx

theorem rich_direction (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    ((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)<b ∧
      b<((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ) := by
  rcases safe m k b hb with hu|⟨hd,hp,hr|hb'⟩
  · have hn := hu.1; rw [hm] at hn; cases hn
  · exact hr.2
  · have he := Option.some.inj (hm.symm.trans hb'.1)
    cases he

theorem poor_direction (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor) :
    ((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ)<b ∧
      b<((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ) := by
  rcases safe m k b hb with hu|⟨hd,hp,hr|hb'⟩
  · have hn := hu.1; rw [hm] at hn; cases hn
  · have he := Option.some.inj (hm.symm.trans hr.1)
    cases he
  · exact hb'.2

theorem poor_reciprocal_direction (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (ht : (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.endpoint) :
    1/((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)<1/b ∧
      1/b<1/((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ) := by
  have hd := poor_direction m k b hb hm
  exact ⟨one_div_lt_one_div_of_lt hb.1 hd.2,one_div_lt_one_div_of_lt ht hd.1⟩

end Blotto.GeneralPaperProxyClassifierPaths
