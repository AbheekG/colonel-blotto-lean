import Blotto.GeneralPaperSelectionBits

/-! The actual root record supplies selection's integer-size premises.
Inclusive cell membership gives value at most one, hence numerator at most
denominator. The constructed H/grid relation then gives the original cap.
-/
namespace Blotto.GeneralPaperClassifierRootBounds
set_option autoImplicit false

theorem cell_numerator (Q j : ℕ) (f : Farey.Fraction) (hQ : 0<Q) (hj : j<Q)
    (hCell : GeneralPaperProxyCell.Closed Q j f.value) : f.num≤f.den := by
  have hQrat : (0:ℚ)<Q := by exact_mod_cast hQ
  have hUpper : GeneralPaperBucketGeometry.upper Q j≤1 := by
    unfold GeneralPaperBucketGeometry.upper
    apply (div_le_one hQrat).mpr
    exact_mod_cast (show j+1≤Q by omega)
  have hValue : f.value≤1 := hCell.2.trans hUpper
  have hD : (0:ℚ)<f.den := by exact_mod_cast f.den_pos
  have hN : (f.num:ℚ)≤f.den := (div_le_one hD).mp hValue
  exact_mod_cast hN

theorem root_bounds (model : RationalCostModel) (W m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℚ) (hb : 0<b ∧ b<1) :
    ∀ f,(GeneralPaperCachedRootQueryBits.run model W c b).1.2.fraction=some f →
      f.num≤2*c.proxy.Qg ∧ f.den≤2*c.proxy.Qg := by
  subst c
  intro f hf
  rw [GeneralPaperCachedRootQueryBits.classifier_root model W m k _ rfl b] at hf
  have hs := GeneralPaperProxyClassifier.root_sound m k (b:ℝ) f hf
  have hReal : (0:ℝ)<b ∧ (b:ℝ)<1 := by exact_mod_cast hb
  have hCell := (GeneralPaperProxyQuotient.locate_spec m k (b:ℝ) hReal).1
  change (GeneralPaperProxyClassifier.classify m k (b:ℝ)).cell<(GeneralPaperProxyParameters.prepare m k).Qg at hCell
  have hn := cell_numerator (GeneralPaperProxyParameters.prepare m k).Qg
    (GeneralPaperProxyClassifier.classify m k (b:ℝ)).cell f (GeneralPaperProxyParameters.grid_positive m k) hCell hs.2
  have hH := GeneralPaperProxyParameters.H_positive m k
  have hGrid := GeneralPaperProxyParameters.grid_lower m k
  have hSquare : (GeneralPaperProxyParameters.prepare m k).H≤
      (GeneralPaperProxyParameters.prepare m k).H*(GeneralPaperProxyParameters.prepare m k).H := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (GeneralPaperProxyParameters.prepare m k).H
      (show 1≤(GeneralPaperProxyParameters.prepare m k).H by omega)
  have hCap : (GeneralPaperProxyParameters.prepare m k).H≤2*(GeneralPaperProxyParameters.prepare m k).Qg := by
    nlinarith only [hGrid,hSquare]
  exact ⟨hn.trans (hs.1.trans hCap),hs.1.trans hCap⟩

end Blotto.GeneralPaperClassifierRootBounds
