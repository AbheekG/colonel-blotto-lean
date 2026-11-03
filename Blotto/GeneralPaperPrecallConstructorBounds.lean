import Blotto.GeneralPaperNatPowerConstructionStorage

/-! Derived payload and frame bounds for the actual precall constructors.
The two halving powers and three ceilings use full constructed words, while
all bounds include m=0 and exponent/target zero. No size oracle is supplied. -/
namespace Blotto.GeneralPaperPrecallConstructorBounds
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def IsTarget (m k target : ℕ) : Prop :=
  let c := GeneralPaperPrecallCachePrice.specification m k
  target=m*c.score.K ∨ target=4*c.proxy.H*c.proxy.H ∨ target=4*c.comparator.D*c.comparator.D

theorem target_word (m k target : ℕ) (ht : IsTarget m k target) :
    binaryWordWidth target≤GeneralPaperPrecallControlWord.measure m k := by
  have h := GeneralPaperPrecallControlWord.terms m k
  rcases ht with rfl|rfl|rfl <;> dsimp only [GeneralPaperPrecallCachePrice.specification] <;> omega

theorem input_words (m k : ℕ) :
    ∀ x∈[m,k,m+2,m+3,7+k,17+k],natBits x≤payload m k := by
  have ht := GeneralPaperPrecallControlWord.terms m k
  dsimp only at ht
  have hK := GeneralPaperScoreScaleParameters.labels_positive m k
  have hm : m≤m*(GeneralPaperScoreScaleParameters.prepare m k).K := by nlinarith only [hK]
  have hmw := binaryWordWidth_mono hm
  have h2 := GeneralPaperRayOperandWidthEnvelope.word_add m 2
  have h3 := GeneralPaperRayOperandWidthEnvelope.word_add m 3
  have htwo : binaryWordWidth 2=2 := by decide
  have hthree : binaryWordWidth 3=2 := by decide
  have hk := GeneralPaperInitializerControlCounters.word_le_self k
  have h7 := GeneralPaperInitializerControlCounters.word_le_self (7+k)
  have h17 := GeneralPaperInitializerControlCounters.word_le_self (17+k)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold natBits payload <;> omega

theorem root_payload (m k : ℕ) :
    GeneralPaperNatPowerConstructionStorage.payload (m+3) ((GeneralPaperProxyParameters.prepare m k).d+2)≤payload m k := by
  let r := GeneralPaperProxyParameters.prepare m k
  have ht := GeneralPaperPrecallControlWord.terms m k
  have he := GeneralPaperPrecallIndexWords.root_exponent m k
  have hew := GeneralPaperInitializerControlCounters.word_le_self (r.d+2)
  have hK := GeneralPaperScoreScaleParameters.labels_positive m k
  have hm : m≤m*(GeneralPaperScoreScaleParameters.prepare m k).K := by nlinarith only [hK]
  have hmw := binaryWordWidth_mono hm
  have hbase := GeneralPaperRayOperandWidthEnvelope.word_add m 3
  have h3 : binaryWordWidth 3=2 := by decide
  have hH := GeneralPaperProxyParameters.H_positive m k
  have hh := binaryWordWidth_mono (show r.H≤4*r.H*r.H by change 0<r.H at hH; nlinarith only [hH])
  unfold GeneralPaperNatPowerConstructionStorage.payload
  rw [←(GeneralPaperProxyParameters.data m k).2.2.2.1]
  dsimp only at ht
  unfold payload
  dsimp only [r] at *
  omega

theorem alphabet_payload (m k : ℕ) :
    GeneralPaperNatPowerConstructionStorage.payload (m+2)
      (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J≤payload m k := by
  let c := GeneralPaperPrecallCachePrice.specification m k
  have ht := GeneralPaperPrecallControlWord.terms m k
  have he := GeneralPaperPrecallIndexWords.alphabet_exponent m k
  have hew := GeneralPaperInitializerControlCounters.word_le_self c.comparator.J
  have hK := GeneralPaperScoreScaleParameters.labels_positive m k
  have hm : m≤m*c.score.K := by change 0<c.score.K at hK; nlinarith only [hK]
  have hmw := binaryWordWidth_mono hm
  have hbase := GeneralPaperRayOperandWidthEnvelope.word_add m 2
  have h2 : binaryWordWidth 2=2 := by decide
  have hD : 0<c.comparator.D := GeneralPaperComparatorParameters.denominator_positive m k c.proxy.qbar
    (GeneralPaperProxyParameters.cap_positive m k)
  have hq : 1≤c.proxy.qbar := GeneralPaperProxyParameters.cap_positive m k
  have hd : c.comparator.D=c.proxy.qbar*(m+2)^c.comparator.J := (GeneralPaperComparatorParameters.data m k c.proxy.qbar).2.2.1
  have hp : (m+2)^c.comparator.J≤c.comparator.D := by
    rw [hd]
    simpa only [one_mul] using Nat.mul_le_mul_right ((m+2)^c.comparator.J) hq
  have hpw := binaryWordWidth_mono hp
  have hds := binaryWordWidth_mono (show c.comparator.D≤4*c.comparator.D*c.comparator.D by nlinarith only [hD])
  unfold GeneralPaperNatPowerConstructionStorage.payload payload
  dsimp only at ht
  dsimp only [c,GeneralPaperPrecallCachePrice.specification] at *
  omega

theorem dyadic_record (W m k e : ℕ) (he : e≤17+k) :
    GeneralPaperPreparationCacheStorage.powerFootprint W (GeneralPaperScoreScaleParameters.powerRun e)≤
      3*(payload m k+W)+32*W := by
  have hd := GeneralPaperScoreScaleParameters.power_data e
  have hp := GeneralPaperParameterOperandBounds.dyadic_word e
  have hew := GeneralPaperInitializerControlCounters.word_le_self e
  have hw := GeneralPaperInitializerControlCounters.word_le_self (8*e+2)
  have ht := (GeneralPaperPrecallControlWord.terms m k).1
  apply fields_bound W (payload m k)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl <;> unfold natBits payload
  · omega
  · rw [hd.2.1]; omega
  · rw [hd.2.2]; omega

theorem dyadic_peak (W m k e : ℕ) (he : e≤17+k) :
    GeneralPaperDyadicConstructionStorage.peak W e≤(e+1)*(4*payload m k+192*W) := by
  have index (n : ℕ) (hn : n≤17+k) : natBits n≤payload m k :=
    small m k n (by have h := (GeneralPaperPrecallControlWord.terms m k).1; omega)
  induction e with
  | zero =>
    have hr := dyadic_record W m k 0 he
    have hi := index 0 he
    unfold GeneralPaperDyadicConstructionStorage.peak
    omega
  | succ e ih =>
    have hr := dyadic_record W m k (e+1) he
    have hi := index (e+1) he
    have hs := ih (by omega)
    rw [GeneralPaperDyadicConstructionStorage.peak]
    nlinarith only [hr,hi,hs]

theorem ceiling_word (m k target : ℕ) (ht : IsTarget m k target) :
    GeneralPaperCeilingConstructionStorage.word target≤payload m k := by
  have h := target_word m k target ht
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add target 1
  have h1 : binaryWordWidth 1=1 := by decide
  unfold GeneralPaperCeilingConstructionStorage.word payload
  omega

theorem ceiling_record (W m k target : ℕ) (ht : IsTarget m k target) :
    GeneralPaperPreparationCacheStorage.powerFootprint W (GeneralPaperPowerCeiling.ceiling target)≤5*payload m k+192*W := by
  have h := GeneralPaperCeilingConstructionStorage.record W target
  have hw := ceiling_word m k target ht
  omega

theorem ceiling_peak (W m k target : ℕ) (ht : IsTarget m k target) :
    GeneralPaperCeilingConstructionStorage.peak W target 1 (by decide)≤
      (GeneralPaperPrecallControlWord.measure m k+1)*(5*payload m k+192*W) := by
  have h := GeneralPaperCeilingConstructionStorage.bounded W target 1 (by decide) (by omega)
  have hw := ceiling_word m k target ht
  have hd := GeneralPaperPowerCeiling.loop_depth target 1 (by decide)
  have htW := target_word m k target ht
  exact h.trans (Nat.mul_le_mul (by omega) (by omega))

theorem root_peak (W m k : ℕ) :
    GeneralPaperNatPowerConstructionStorage.peak W (m+3) ((GeneralPaperProxyParameters.prepare m k).d+2)≤
      (GeneralPaperPrecallControlWord.measure m k+2)*(12*payload m k+384*W) := by
  have h := GeneralPaperNatPowerConstructionStorage.depth_bound W (m+3)
    ((GeneralPaperProxyParameters.prepare m k).d+2) ((GeneralPaperProxyParameters.prepare m k).d+2) (by omega) (Nat.le_refl _)
  have he := GeneralPaperPrecallIndexWords.root_exponent m k
  have hw := GeneralPaperInitializerControlCounters.word_le_self ((GeneralPaperProxyParameters.prepare m k).d+2)
  have hp := root_payload m k
  exact h.trans (Nat.mul_le_mul (by omega) (by omega))

theorem alphabet_peak (W m k : ℕ) :
    GeneralPaperNatPowerConstructionStorage.peak W (m+2)
      (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J≤
        (GeneralPaperPrecallControlWord.measure m k+2)*(12*payload m k+384*W) := by
  have h := GeneralPaperNatPowerConstructionStorage.depth_bound W (m+2)
    (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J
    (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J (by omega) (Nat.le_refl _)
  have he := GeneralPaperPrecallIndexWords.alphabet_exponent m k
  have hw := GeneralPaperInitializerControlCounters.word_le_self
    (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J
  have hp := alphabet_payload m k
  exact h.trans (Nat.mul_le_mul (by omega) (by omega))

end Blotto.GeneralPaperPrecallConstructorBounds
