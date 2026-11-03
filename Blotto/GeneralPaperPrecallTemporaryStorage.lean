import Blotto.GeneralPaperPrecallConstructorBounds

/-! All fixed-size temporaries of the selected score/proxy/comparator
preparation: two dyadic returns, two determinant-power returns, three ceiling
returns, literal intermediate arithmetic and native annotation sums. -/
namespace Blotto.GeneralPaperPrecallTemporaryStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def rawValues (m k : ℕ) : List ℕ :=
  let c := GeneralPaperPrecallCachePrice.specification m k
  [m,k,7+k,17+k,m+2,m+3,c.score.K-1,m*c.score.K,c.proxy.d,c.proxy.d+2,
    c.comparator.Kc-1,m*(c.comparator.Kc-1),c.comparator.J,(m+2)^c.comparator.J,
    c.proxy.qbar,c.comparator.D,4*c.proxy.H,4*c.proxy.H*c.proxy.H,
    4*c.comparator.D,4*c.comparator.D*c.comparator.D,2*c.proxy.Qg,1,2,3,4,7,17]

theorem raw_words (m k : ℕ) : ∀ x∈rawValues m k,natBits x≤payload m k := by
  let c := GeneralPaperPrecallCachePrice.specification m k
  have hi := GeneralPaperPrecallConstructorBounds.input_words m k
  have hw := words m k
  change (∀ x∈[c.score.K,c.score.S,c.score.depth,c.score.work],natBits x≤payload m k) ∧
    (∀ x∈[c.proxy.K,c.proxy.S,c.proxy.d,c.proxy.H,c.proxy.Qg,c.proxy.gridBits,c.proxy.qbar,c.proxy.work],natBits x≤payload m k) ∧
    (∀ x∈[c.comparator.Kc,c.comparator.J,c.comparator.D,c.comparator.C,c.comparator.lambda,c.comparator.work],natBits x≤payload m k) at hw
  have ht := GeneralPaperPrecallControlWord.terms m k
  change k+18≤GeneralPaperPrecallControlWord.measure m k ∧
    binaryWordWidth (m*c.score.K)+1≤GeneralPaperPrecallControlWord.measure m k ∧
    binaryWordWidth (c.proxy.d+2)+1≤GeneralPaperPrecallControlWord.measure m k ∧
    binaryWordWidth (4*c.proxy.H*c.proxy.H)+1≤GeneralPaperPrecallControlWord.measure m k ∧
    binaryWordWidth c.comparator.J+1≤GeneralPaperPrecallControlWord.measure m k ∧
    binaryWordWidth (4*c.comparator.D*c.comparator.D)+1≤GeneralPaperPrecallControlWord.measure m k ∧
    c.proxy.gridBits+4≤GeneralPaperPrecallControlWord.measure m k at ht
  have hK := hw.1 c.score.K (by simp)
  have hKc := hw.2.2 c.comparator.Kc (by simp)
  have hd := hw.2.1 c.proxy.d (by simp)
  have hq := hw.2.1 c.proxy.qbar (by simp)
  have hD := hw.2.2 c.comparator.D (by simp)
  have hHpos : 0<c.proxy.H := GeneralPaperProxyParameters.H_positive m k
  have hDpos : 0<c.comparator.D := GeneralPaperComparatorParameters.denominator_positive m k c.proxy.qbar
    (GeneralPaperProxyParameters.cap_positive m k)
  have hqpos : 1≤c.proxy.qbar := GeneralPaperProxyParameters.cap_positive m k
  have hden : c.comparator.D=c.proxy.qbar*(m+2)^c.comparator.J :=
    (GeneralPaperComparatorParameters.data m k c.proxy.qbar).2.2.1
  have hJ : c.comparator.J=m*(c.comparator.Kc-1)+1 :=
    (GeneralPaperComparatorParameters.data m k c.proxy.qbar).2.1
  have hcap : c.proxy.qbar=2*c.proxy.Qg := (GeneralPaperProxyParameters.data m k).2.2.2.2.2.2
  have monotone (x y : ℕ) (hxy : x≤y) (hy : natBits y≤payload m k) : natBits x≤payload m k := by
    have h := binaryWordWidth_mono hxy
    unfold natBits at *
    omega
  have measured (x : ℕ) (hx : binaryWordWidth x≤GeneralPaperPrecallControlWord.measure m k) :
      natBits x≤payload m k := by unfold natBits payload; omega
  have hpower : (m+2)^c.comparator.J≤c.comparator.D := by
    rw [hden]
    simpa only [one_mul] using Nat.mul_le_mul_right ((m+2)^c.comparator.J) hqpos
  intro x hx
  change x∈[m,k,7+k,17+k,m+2,m+3,c.score.K-1,m*c.score.K,c.proxy.d,c.proxy.d+2,
    c.comparator.Kc-1,m*(c.comparator.Kc-1),c.comparator.J,(m+2)^c.comparator.J,
    c.proxy.qbar,c.comparator.D,4*c.proxy.H,4*c.proxy.H*c.proxy.H,
    4*c.comparator.D,4*c.comparator.D*c.comparator.D,2*c.proxy.Qg,1,2,3,4,7,17] at hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hi _ (by simp)
  · exact hi _ (by simp)
  · exact hi _ (by simp)
  · exact hi _ (by simp)
  · exact hi _ (by simp)
  · exact hi _ (by simp)
  · exact monotone _ _ (by omega) hK
  · exact measured _ (by omega)
  · exact hd
  · exact measured _ (by omega)
  · exact monotone _ _ (by omega) hKc
  · exact measured _ ((binaryWordWidth_mono (by omega : m*(c.comparator.Kc-1)≤c.comparator.J)).trans (by omega))
  · exact measured _ (by omega)
  · exact monotone _ _ hpower hD
  · exact hq
  · exact hD
  · exact measured _ ((binaryWordWidth_mono (show 4*c.proxy.H≤4*c.proxy.H*c.proxy.H by nlinarith only [hHpos])).trans (by omega))
  · exact measured _ (by omega)
  · exact measured _ ((binaryWordWidth_mono (show 4*c.comparator.D≤4*c.comparator.D*c.comparator.D by nlinarith only [hDpos])).trans (by omega))
  · exact measured _ (by omega)
  · rw [←hcap]; exact hq
  · exact small m k 1 (by omega)
  · exact small m k 2 (by omega)
  · exact small m k 3 (by omega)
  · exact small m k 4 (by omega)
  · exact small m k 7 (by omega)
  · exact small m k 17 (by omega)

def annotations (m k : ℕ) : List ℕ :=
  let c := GeneralPaperPrecallCachePrice.specification m k
  let sl := GeneralPaperScoreScaleParameters.powerRun (7+k)
  let sc := GeneralPaperPowerCeiling.ceiling (m*c.score.K)
  let rd := GeneralPaperNatPower.run (m+3) (c.proxy.d+2)
  let rg := GeneralPaperPowerCeiling.ceiling (4*c.proxy.H*c.proxy.H)
  let al := GeneralPaperScoreScaleParameters.powerRun (17+k)
  let ad := GeneralPaperNatPower.run (m+2) c.comparator.J
  let ag := GeneralPaperPowerCeiling.ceiling (4*c.comparator.D*c.comparator.D)
  [sl.work+sc.work,sl.work+sc.work+16,c.score.work+rd.work,c.score.work+rd.work+rg.work,
    al.work+ad.work,al.work+ad.work+ag.work]

theorem annotation_words (m k : ℕ) : ∀ x∈annotations m k,natBits x≤payload m k := by
  let c := GeneralPaperPrecallCachePrice.specification m k
  have hs : c.score.work=(GeneralPaperScoreScaleParameters.powerRun (7+k)).work+
      (GeneralPaperPowerCeiling.ceiling (m*c.score.K)).work+16 := rfl
  have hr : c.proxy.work=c.score.work+(GeneralPaperNatPower.run (m+3) (c.proxy.d+2)).work+
      (GeneralPaperPowerCeiling.ceiling (4*c.proxy.H*c.proxy.H)).work+32 := rfl
  have ha : c.comparator.work=(GeneralPaperScoreScaleParameters.powerRun (17+k)).work+
      (GeneralPaperNatPower.run (m+2) c.comparator.J).work+
        (GeneralPaperPowerCeiling.ceiling (4*c.comparator.D*c.comparator.D)).work+32 := rfl
  have hsC := GeneralPaperPrecallControlWord.score_controls m k
  have hrC := GeneralPaperPrecallControlWord.root_controls m k
  have haC := GeneralPaperPrecallControlWord.alphabet_controls m k
  change c.score.depth≤GeneralPaperPrecallControlWord.measure m k ∧
    c.score.work≤20*GeneralPaperPrecallControlWord.measure m k+20 at hsC
  change c.proxy.gridBits+4≤GeneralPaperPrecallControlWord.measure m k ∧
    c.proxy.work≤44*GeneralPaperPrecallControlWord.measure m k+56 at hrC
  change c.comparator.lambda≤GeneralPaperPrecallControlWord.measure m k+2 ∧
    c.comparator.work≤32*GeneralPaperPrecallControlWord.measure m k+38 at haC
  intro x hx
  apply small m k x
  dsimp only [annotations] at hx
  dsimp only [c,GeneralPaperPrecallCachePrice.specification] at hs hr ha hsC hrC haC hx ⊢
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def records (W m k : ℕ) : ℕ :=
  let c := GeneralPaperPrecallCachePrice.specification m k
  GeneralPaperPreparationCacheStorage.powerFootprint W (GeneralPaperScoreScaleParameters.powerRun (7+k))+
    GeneralPaperPreparationCacheStorage.powerFootprint W (GeneralPaperScoreScaleParameters.powerRun (17+k))+
    GeneralPaperNatPowerConstructionStorage.record W (GeneralPaperNatPower.run (m+3) (c.proxy.d+2))+
    GeneralPaperNatPowerConstructionStorage.record W (GeneralPaperNatPower.run (m+2) c.comparator.J)+
    GeneralPaperPreparationCacheStorage.powerFootprint W (GeneralPaperPowerCeiling.ceiling (m*c.score.K))+
    GeneralPaperPreparationCacheStorage.powerFootprint W (GeneralPaperPowerCeiling.ceiling (4*c.proxy.H*c.proxy.H))+
    GeneralPaperPreparationCacheStorage.powerFootprint W (GeneralPaperPowerCeiling.ceiling (4*c.comparator.D*c.comparator.D))

theorem records_bound (W m k : ℕ) : records W m k≤27*payload m k+716*W := by
  let c := GeneralPaperPrecallCachePrice.specification m k
  have h0 := GeneralPaperPrecallConstructorBounds.dyadic_record W m k (7+k) (by omega)
  have h1 := GeneralPaperPrecallConstructorBounds.dyadic_record W m k (17+k) (Nat.le_refl _)
  have h2 := GeneralPaperNatPowerConstructionStorage.record_bound W (m+3) (c.proxy.d+2) (c.proxy.d+2) (by omega) (Nat.le_refl _)
  have h3 := GeneralPaperNatPowerConstructionStorage.record_bound W (m+2) c.comparator.J c.comparator.J (by omega) (Nat.le_refl _)
  have hp0 := GeneralPaperPrecallConstructorBounds.root_payload m k
  have hp1 := GeneralPaperPrecallConstructorBounds.alphabet_payload m k
  have h4 := GeneralPaperPrecallConstructorBounds.ceiling_record W m k (m*c.score.K) (Or.inl rfl)
  have h5 := GeneralPaperPrecallConstructorBounds.ceiling_record W m k (4*c.proxy.H*c.proxy.H) (Or.inr (Or.inl rfl))
  have h6 := GeneralPaperPrecallConstructorBounds.ceiling_record W m k (4*c.comparator.D*c.comparator.D) (Or.inr (Or.inr rfl))
  change GeneralPaperNatPowerConstructionStorage.payload (m+3) (c.proxy.d+2)≤payload m k at hp0
  change GeneralPaperNatPowerConstructionStorage.payload (m+2) c.comparator.J≤payload m k at hp1
  unfold records
  dsimp only
  dsimp only [c] at *
  omega

def footprint (W m k : ℕ) : ℕ :=
  records W m k+fields W (rawValues m k)+fields W (annotations m k)+512*W

def profile (W m k : ℕ) : ℕ := 60*payload m k+1325*W

theorem bounded (W m k : ℕ) : footprint W m k≤profile W m k := by
  have hr := records_bound W m k
  have hf := fields_bound W (payload m k) (rawValues m k) (raw_words m k)
  have ha := fields_bound W (payload m k) (annotations m k) (annotation_words m k)
  change _≤27*(payload m k+W)+32*W at hf
  change _≤6*(payload m k+W)+32*W at ha
  unfold footprint profile
  omega

end Blotto.GeneralPaperPrecallTemporaryStorage
