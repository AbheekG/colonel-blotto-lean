import Blotto.GeneralPaperOriginalValueBitGrowth

/-! Original-length fast bit time for the actual value/source driver.
The value word is uniformly any logarithmic word; source addresses retain
their already derived global reference. Final caller space and accuracy/
circle/output construction remain separate resource joins. -/
namespace Blotto.GeneralPaperOriginalValueBitDriverRate
open GeneralPaperOriginalValueBitOperands GeneralPaperOriginalValueBitGrowth
open GeneralPaperFastRationalModel GeneralPaperOriginalSourceValuePreparation GeneralPaperOriginalSourceValueDriver
open GeneralPaperSourceRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def originalLog (n k B S : ℕ) : ℕ :=
  GeneralPaperOriginalSourceValueContract.inputLog n k B+binaryWordWidth (S+1)

theorem log_positive (n k B S : ℕ) : 1≤originalLog n k B S := by
  unfold originalLog GeneralPaperOriginalSourceValueContract.inputLog
  omega

theorem value_log (K n k B S W : ℕ) (hW : W≤K*originalLog n k B S) :
    logarithm n k W≤(K+1)*originalLog n k B S := by
  have hBase : 128+k+binaryWordWidth (n+4)≤originalLog n k B S := by
    unfold originalLog GeneralPaperOriginalSourceValueContract.inputLog
    omega
  unfold logarithm
  nlinarith only [hW,hBase]

theorem charge_bound (C d K n k B S W : ℕ) (hW : W≤K*originalLog n k B S) :
    GeneralPaperFastRationalModel.charge C d (2^28*size n k W S)≤
      (C*2^28*(2*binaryWordWidth (K+1)+40)^d*(1+(K+1)^2))*(S+n+1)*(originalLog n k B S)^(d+2) := by
  let L := originalLog n k B S
  let D := 2*binaryWordWidth (K+1)+40
  let T := S+(n+1)*(K+1)^2*L^2
  have hL : 1≤L := log_positive n k B S
  have hLV := value_log K n k B S W hW
  have hSize : size n k W S≤T := by
    unfold size
    calc
      _≤S+(n+1)*((K+1)*L)^2 := Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLV 2)) _
      _= _ := by dsimp only [T];ring
  have hWordN : binaryWordWidth (n+1)≤L := by
    have hh := binaryWordWidth_mono (show n+1≤n+4 by omega)
    dsimp only [L,originalLog,GeneralPaperOriginalSourceValueContract.inputLog]
    omega
  have hWordS : binaryWordWidth S≤L := by
    have hh := binaryWordWidth_mono (show S≤S+1 by omega)
    dsimp only [L,originalLog,GeneralPaperOriginalSourceValueContract.inputLog]
    omega
  have hWordL : binaryWordWidth L≤L+1 := by
    have hh := Nat.log2_le_self L
    unfold binaryWordWidth
    omega
  have hWord : binaryWordWidth (2^28*T+1)+1≤D*L := by
    have h0 := binaryWordWidth_mul (K+1) (K+1)
    have h1 := binaryWordWidth_mul L L
    have h2 := binaryWordWidth_mul (n+1) ((K+1)^2)
    have h3 := binaryWordWidth_mul ((n+1)*(K+1)^2) (L^2)
    have h4 := GeneralPaperReferenceScaling.word_add S ((n+1)*(K+1)^2*L^2)
    have h5 := binaryWordWidth_mul (2^28) T
    have h6 := GeneralPaperReferenceScaling.word_add (2^28*T) 1
    rw [show binaryWordWidth (2^28)=29 by decide] at h5
    rw [show binaryWordWidth 1=1 by decide] at h6
    dsimp only [T,D] at h5 h6 ⊢
    simp only [pow_two] at h2 h3 h4 h5 h6 ⊢
    nlinarith only [h0,h1,h2,h3,h4,h5,h6,hWordN,hWordS,hWordL,hL,
      Nat.mul_le_mul_left (2*binaryWordWidth (K+1)) hL]
  have hFactor : logFactor d (2^28*T)≤D^d*L^d := by
    unfold logFactor
    exact (Nat.pow_le_pow_left hWord d).trans_eq (by rw [mul_pow])
  have hAmp : T≤(1+(K+1)^2)*(S+n+1)*L^2 := by
    have hOne : 1≤L^2 := Nat.one_le_pow _ _ hL
    have h0 : S≤(S+n+1)*L^2 := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul (show S≤S+n+1 by omega) hOne
    have h1 := Nat.mul_le_mul_right ((K+1)^2*L^2) (show n+1≤S+n+1 by omega)
    dsimp only [T]
    nlinarith only [h0,h1]
  apply (charge_monotone C d (Nat.mul_le_mul_left (2^28) hSize)).trans
  unfold GeneralPaperFastRationalModel.charge
  calc
    C*(2^28*T)*logFactor d (2^28*T)≤C*(2^28*T)*(D^d*L^d) := Nat.mul_le_mul_left _ hFactor
    _≤C*(2^28*((1+(K+1)^2)*(S+n+1)*L^2))*(D^d*L^d) := by gcongr
    _= _ := by rw [pow_add];ring

theorem value_price {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (K W k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (hW : W≤K*originalLog n k B (GeneralPaperValueRoundingInputPrice.inputSize values)) :
    GeneralPaperOriginalSourceValuePrice.bitPrice model W k values≤
      (C*2^28*(2*binaryWordWidth (K+1)+40)^d*(1+(K+1)^2))*(GeneralPaperValueRoundingInputPrice.inputSize values+n+1)*
        (originalLog n k B (GeneralPaperValueRoundingInputPrice.inputSize values))^(d+2) :=
  (fast_price hg W k values v hv).trans (charge_bound C d K n k B _ W hW)

theorem input_fields {n : ℕ} (values : FixedArrayTable n ℚ) : n≤GeneralPaperValueRoundingInputPrice.inputSize values := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ : Fin n => 1)
    (g:=fun j => rationalWordWidth (values.read j)) (fun _ _ => by unfold rationalWordWidth;omega)
  simpa only [GeneralPaperValueRoundingInputPrice.inputSize,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] using h

theorem native_time {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d) (K : ℕ) :
    ∃ A e : ℕ,∀ {n : ℕ} (Wv k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B),
      let S := GeneralPaperValueRoundingInputPrice.inputSize values
      Wv≤K*originalLog n k B S →
      let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
      let x := input o k B b hb hB
      let Ws := GeneralPaperFastDriverReference.width C d x
      (bit model Wv Ws k values v hv b hb).2≤A*(S+B+1+monomial 3 0 6 x)*(originalLog n k B S)^e := by
  obtain ⟨A,e,h⟩ := GeneralPaperOriginalSourceValueContract.bit_input_time hg
  let V := C*2^28*(2*binaryWordWidth (K+1)+40)^d*(1+(K+1)^2)
  refine ⟨2*V+A,e+d+2,?_⟩
  intro n Wv k B values v hv b hb hB
  dsimp only
  intro hW
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let L := originalLog n k B S
  let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
  let x := input o k B b hb hB
  let R := S+B+1+monomial 3 0 6 x
  have hN : n≤S := input_fields values
  have hL : 1≤L := log_positive n k B S
  have hAmp : S+n+1≤2*R := by dsimp only [R];omega
  have hValue := value_price hg K Wv k B values v hv hW
  have hValue' : GeneralPaperOriginalSourceValuePrice.bitPrice model Wv k values≤V*(2*R)*L^(e+d+2) :=
    hValue.trans (Nat.mul_le_mul (Nat.mul_le_mul_left V hAmp) (Nat.pow_le_pow_right hL (by omega)))
  have hSourceAmp : B+1+monomial 3 0 6 x≤R := by dsimp only [R];omega
  have hSourceLog : GeneralPaperOriginalSourceValueContract.inputLog n k B≤L := Nat.le_add_right _ _
  have hPower : (GeneralPaperOriginalSourceValueContract.inputLog n k B)^e≤L^(e+d+2) :=
    (Nat.pow_le_pow_left hSourceLog e).trans (Nat.pow_le_pow_right hL (by omega))
  have hSource := Nat.mul_le_mul (Nat.mul_le_mul_left A hSourceAmp) hPower
  exact (h Wv k B values v hv b hb hB).trans ((Nat.add_le_add hValue' hSource).trans_eq (by ring))

theorem time_and_return {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d) (K : ℕ) :
    ∃ A e : ℕ,∀ {n : ℕ} (Wv k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B),
      let S := GeneralPaperValueRoundingInputPrice.inputSize values
      Wv≤K*originalLog n k B S →
      let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
      let x := input o k B b hb hB
      let Ws := GeneralPaperFastDriverReference.width C d x
      let redValues := GeneralPaperOriginalValueReduction.selector true model Wv k values v hv
      ∃ physical pair,(bit model Wv Ws k values v hv b hb).1.physical=some physical ∧
        GeneralPaperRoundedValueCanonical.run true model Wv k o.reduced.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧
        GeneralPaperOriginalDrawEquilibrium.Matches physical pair ∧
        GeneralPaperSourcePairContract.Contract k o.Qv o.Qv_positive o.weights o.weights_positive o.weight_sum (b:ℝ) pair ∧
        (bit model Wv Ws k values v hv b hb).2≤A*(S+B+1+monomial 3 0 6 x)*(originalLog n k B S)^e := by
  obtain ⟨A,e,h⟩ := native_time hg K
  refine ⟨A,e,?_⟩
  intro n Wv k B values v hv b hb hB
  dsimp only
  intro hW
  obtain ⟨physical,pair,hRun,hSource,hMatches,hContract⟩ := bit_return model Wv _ k values v hv b hb
  exact ⟨physical,pair,hRun,hSource,hMatches,hContract,h Wv k B values v hv b hb hB hW⟩

/- This instantiates only the price word. Full simultaneous caller storage
and address calibration must still supply the final common machine word. -/
theorem at_input_word {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d) :
    ∃ A e : ℕ,∀ {n : ℕ} (k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B),
      let S := GeneralPaperValueRoundingInputPrice.inputSize values
      let Wv := originalLog n k B S
      let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
      let x := input o k B b hb hB
      let Ws := GeneralPaperFastDriverReference.width C d x
      (bit model Wv Ws k values v hv b hb).2≤A*(S+B+1+monomial 3 0 6 x)*(originalLog n k B S)^e := by
  obtain ⟨A,e,h⟩ := native_time hg 1
  refine ⟨A,e,?_⟩
  intro n k B values v hv b hb hB
  exact h (originalLog n k B (GeneralPaperValueRoundingInputPrice.inputSize values)) k B values v hv b hb hB
    (by rw [Nat.one_mul])

end Blotto.GeneralPaperOriginalValueBitDriverRate
