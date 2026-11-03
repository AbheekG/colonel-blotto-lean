import Blotto.GeneralPaperPrecallTemporaryStorage

/-! Whole precall parameter construction: simultaneous returned cache/view,
all native temporaries, every selected constructor stack and conservative
primitive scratch from the one complete executed constructor price. -/
namespace Blotto.GeneralPaperPrecallConstructionStorage
open GeneralPaperPrecallCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def constructorStack (W m k : ℕ) : ℕ :=
  let c := GeneralPaperPrecallCachePrice.specification m k
  GeneralPaperDyadicConstructionStorage.peak W (7+k)+GeneralPaperDyadicConstructionStorage.peak W (17+k)+
    GeneralPaperNatPowerConstructionStorage.peak W (m+3) (c.proxy.d+2)+
    GeneralPaperNatPowerConstructionStorage.peak W (m+2) c.comparator.J+
    GeneralPaperCeilingConstructionStorage.peak W (m*c.score.K) 1 (by decide)+
    GeneralPaperCeilingConstructionStorage.peak W (4*c.proxy.H*c.proxy.H) 1 (by decide)+
    GeneralPaperCeilingConstructionStorage.peak W (4*c.comparator.D*c.comparator.D) 1 (by decide)

def stackProfile (W m k : ℕ) : ℕ :=
  let M := GeneralPaperPrecallControlWord.measure m k
  let P := payload m k
  2*(M+1)*(4*P+192*W)+2*(M+2)*(12*P+384*W)+3*(M+1)*(5*P+192*W)

theorem stack_bound (W m k : ℕ) : constructorStack W m k≤stackProfile W m k := by
  let M := GeneralPaperPrecallControlWord.measure m k
  let c := GeneralPaperPrecallCachePrice.specification m k
  have hM := (GeneralPaperPrecallControlWord.terms m k).1
  have h0 := (GeneralPaperPrecallConstructorBounds.dyadic_peak W m k (7+k) (by omega)).trans
    (Nat.mul_le_mul_right _ (show 7+k+1≤M+1 by dsimp only [M]; omega))
  have h1 := (GeneralPaperPrecallConstructorBounds.dyadic_peak W m k (17+k) (Nat.le_refl _)).trans
    (Nat.mul_le_mul_right _ (show 17+k+1≤M+1 by dsimp only [M]; omega))
  have h2 := GeneralPaperPrecallConstructorBounds.root_peak W m k
  have h3 := GeneralPaperPrecallConstructorBounds.alphabet_peak W m k
  have h4 := GeneralPaperPrecallConstructorBounds.ceiling_peak W m k (m*c.score.K) (Or.inl rfl)
  have h5 := GeneralPaperPrecallConstructorBounds.ceiling_peak W m k (4*c.proxy.H*c.proxy.H) (Or.inr (Or.inl rfl))
  have h6 := GeneralPaperPrecallConstructorBounds.ceiling_peak W m k (4*c.comparator.D*c.comparator.D) (Or.inr (Or.inr rfl))
  unfold constructorStack stackProfile
  dsimp only
  dsimp only [M,c,GeneralPaperPrecallCachePrice.specification] at *
  nlinarith only [h0,h1,h2,h3,h4,h5,h6]

def window (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  let returned := GeneralPaperPrecallCachePrice.prepare model.rat W m k
  footprint W returned.1.1+alphabetFootprint W returned.1.2+
    GeneralPaperPrecallTemporaryStorage.footprint W m k+constructorStack W m k+returned.2+256*W

def profile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  81*payload m k+1882*W+stackProfile W m k+GeneralPaperPrecallCachePrice.profile model.rat W m k

theorem bounded (model : RationalCostModel) (W m k : ℕ) : window model W m k≤profile model W m k := by
  have hr := returned model.rat W m k
  have ht := GeneralPaperPrecallTemporaryStorage.bounded W m k
  have hs := stack_bound W m k
  have hp := GeneralPaperPrecallCachePrice.prepare_work model.rat model.monotone W m k
  unfold window profile GeneralPaperPrecallTemporaryStorage.profile at *
  dsimp only
  omega

theorem stack_quadratic (W m k : ℕ) : stackProfile W m k≤
    64*(GeneralPaperPrecallControlWord.measure m k+2)*(payload m k+32*W) := by
  unfold stackProfile
  nlinarith only [Nat.zero_le (GeneralPaperPrecallControlWord.measure m k*payload m k),
    Nat.zero_le (GeneralPaperPrecallControlWord.measure m k*W)]

theorem source_stack (W m k : ℕ) : constructorStack W m k≤
    64*(k+8*(GeneralPaperProxyParameters.alphabet m k).lambda+66)*
      (65536*(k+8*(GeneralPaperProxyParameters.alphabet m k).lambda+65)+32*W) := by
  have hm := GeneralPaperPrecallWordEnvelope.measure_bound m k
  have hp := source_payload m k
  exact (stack_bound W m k).trans ((stack_quadratic W m k).trans
    (Nat.mul_le_mul (by omega) (by omega)))

theorem structural_quadratic (W m k : ℕ) :
    81*payload m k+1882*W+stackProfile W m k≤
      16777216*(GeneralPaperPrecallControlWord.measure m k+2)*
        (GeneralPaperPrecallControlWord.measure m k+2+W) := by
  have h := stack_quadratic W m k
  unfold payload at *
  nlinarith only [h,Nat.zero_le (GeneralPaperPrecallControlWord.measure m k*W),
    Nat.zero_le (GeneralPaperPrecallControlWord.measure m k*GeneralPaperPrecallControlWord.measure m k)]

theorem whole_structural (model : RationalCostModel) (W m k : ℕ) :
    window model W m k≤16777216*(GeneralPaperPrecallControlWord.measure m k+2)*
      (GeneralPaperPrecallControlWord.measure m k+2+W)+GeneralPaperPrecallCachePrice.profile model.rat W m k :=
  (bounded model W m k).trans (Nat.add_le_add_right (structural_quadratic W m k) _)

theorem source_lambda (model : RationalCostModel) (W m k : ℕ) (hm : 0<m) :
    window model W m k≤16777216*66*66*((GeneralPaperProxyParameters.alphabet m k).lambda+1)*
      ((GeneralPaperProxyParameters.alphabet m k).lambda+1+W)+GeneralPaperPrecallCachePrice.profile model.rat W m k := by
  let L := (GeneralPaperProxyParameters.alphabet m k).lambda
  have hk := GeneralPaperStreamingQueryEnvelope.accuracy_index m k hm
  have hM := GeneralPaperPrecallWordEnvelope.measure_bound m k
  have h0 : GeneralPaperPrecallControlWord.measure m k+2≤66*(L+1) := by dsimp only [L]; omega
  have h1 : GeneralPaperPrecallControlWord.measure m k+2+W≤66*(L+1+W) := by omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 16777216 h0) h1
  have h : 16777216*(GeneralPaperPrecallControlWord.measure m k+2)*
      (GeneralPaperPrecallControlWord.measure m k+2+W)≤16777216*66*66*(L+1)*(L+1+W) :=
    hmul.trans_eq (by ring)
  exact (whole_structural model W m k).trans (Nat.add_le_add_right h _)

end Blotto.GeneralPaperPrecallConstructionStorage
