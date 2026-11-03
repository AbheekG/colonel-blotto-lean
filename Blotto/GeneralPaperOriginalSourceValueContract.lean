import Blotto.GeneralPaperOriginalSourceValueDriver

/-! Quantitative reduced-field bit time and canonical original-game law
for the actual retained original-value producer. The replaced branch uses
the existing native finite-circle/fresh-bit sampler, with Matches derived
from this run. No acceptance, reduced-field cap or source premise is input. -/
namespace Blotto.GeneralPaperOriginalSourceValueContract
open GeneralPaperOriginalSourceValuePreparation GeneralPaperOriginalSourceValueDriver
open GeneralPaperOriginalDrawEquilibrium GeneralPaperOriginalCirclePreparation
open GeneralPaperNativeSelectedSecurity
open GeneralPaperSourceWordGrowth GeneralPaperSourceRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

theorem bit_source_time {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ {n : ℕ} (Wv k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B),
      let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
      let x := input o k B b hb hB
      let Ws := GeneralPaperFastDriverReference.width C d x
      (bit model Wv Ws k values v hv b hb).2≤GeneralPaperOriginalSourceValuePrice.bitPrice model Wv k values+
        A*(B+1+monomial 3 0 6 x)*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := GeneralPaperFastDriverSharpWork.native_time hg 18
  obtain ⟨K,hK⟩ := GeneralPaperFastDriverReference.width_tight C d
  refine ⟨A+128*K,e+1,?_⟩
  intro n Wv k B values v hv b hb hB
  let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
  let x := input o k B b hb hB
  let L := logSize x
  let R := B+1+monomial 3 0 6 x
  have hL : 1≤L := size_positive x
  have hR : 1≤R := by dsimp only [R];omega
  have hPower : L^e≤L^(e+1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ hL
  have hLinear : L≤L^(e+1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hL)
  have hPair := h x (count_bounds true model Wv k values v hv).1 o.Qv_positive o.weights_positive
    (field_cap true model Wv k B values v hv b hb hB)
  have hPair' : (GeneralPaperFastRationalPairDriver.run model (GeneralPaperFastDriverReference.width C d x)
      (GeneralPaperFastDriverReference.width C d x) k o.Qv o.Qv_positive o.weights o.weights_positive o.weight_sum b hb).2≤
      A*R*L^(e+1) := hPair.trans (Nat.mul_le_mul_left _ hPower)
  have hParent : 128*GeneralPaperFastDriverReference.width C d x≤128*K*R*L^(e+1) := by
    calc
      _≤128*(K*L) := Nat.mul_le_mul_left 128 (hK x)
      _≤128*(K*L^(e+1)) := Nat.mul_le_mul_left 128 (Nat.mul_le_mul_left K hLinear)
      _≤128*(K*(R*L^(e+1))) := Nat.mul_le_mul_left 128 (Nat.mul_le_mul_left K (Nat.le_mul_of_pos_left _ hR))
      _= _ := by ring
  have hPrep := GeneralPaperOriginalSourceValuePrice.bit_work model Wv k values v hv
  exact (Nat.add_le_add (Nat.add_le_add hPrep hPair') hParent).trans_eq (by
    dsimp only [bit,L,R,o,x,input]
    ring)

theorem bit_time_and_return {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ {n : ℕ} (Wv k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B),
      let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
      let x := input o k B b hb hB
      let Ws := GeneralPaperFastDriverReference.width C d x
      let redValues := GeneralPaperOriginalValueReduction.selector true model Wv k values v hv
      ∃ physical pair,(bit model Wv Ws k values v hv b hb).1.physical=some physical ∧
        GeneralPaperRoundedValueCanonical.run true model Wv k o.reduced.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧
        Matches physical pair ∧
        GeneralPaperSourcePairContract.Contract k o.Qv o.Qv_positive o.weights o.weights_positive o.weight_sum (b:ℝ) pair ∧
        (bit model Wv Ws k values v hv b hb).2≤GeneralPaperOriginalSourceValuePrice.bitPrice model Wv k values+
          A*(B+1+monomial 3 0 6 x)*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := bit_source_time hg
  refine ⟨A,e,?_⟩
  intro n Wv k B values v hv b hb hB
  dsimp only
  obtain ⟨physical,pair,hRun,hSource,hMatches,hContract⟩ := bit_return model Wv _ k values v hv b hb
  exact ⟨physical,pair,hRun,hSource,hMatches,hContract,h Wv k B values v hv b hb hB⟩

theorem original_bit {n : ℕ} (model : RationalCostModel) (Wv Ws k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run true model Wv k values).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector true model Wv k values v hv
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives),∃ (physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (bit model Wv Ws k values v hv b hb).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run true model Wv k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let μ := GeneralPaperOriginalDrawLaw.law hT (count_positive k) model o hR 1 (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.rich).1
      let ν := GeneralPaperOriginalDrawLaw.law hT (count_positive k) model o hR b (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.poor).1
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
      security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
      regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧ regret v.values (b:ℝ) ν μ≤179*(1/(2:ℝ)^k)/320 := by
  obtain ⟨hm,pair,hSource,hLaw⟩ := GeneralPaperOriginalDrawEquilibrium.original true true model Wv Wv k values v hv b hb price index A hReplace
  obtain ⟨physical,actualPair,hRun,hActual,hMatches,_⟩ := bit_return model Wv Ws k values v hv b hb
  have he : actualPair=pair := Option.some.inj (hActual.symm.trans hSource)
  subst actualPair
  exact ⟨hm,physical,pair,hRun,hSource,hMatches,hLaw physical hMatches⟩

theorem sampled_original_bit {n : ℕ} (model : RationalCostModel) (Wv Ws k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run true model Wv k values).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector true model Wv k values v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives),∃ (physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (bit model Wv Ws k values v hv b hb).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run true model Wv k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let μ := GeneralPaperNativeFairSamplerLaw.law primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR 1
        (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.rich).1
      let ν := GeneralPaperNativeFairSamplerLaw.law primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR b
        (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.poor).1
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
      security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
      regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧ regret v.values (b:ℝ) ν μ≤179*(1/(2:ℝ)^k)/320 := by
  obtain ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich,hPoor⟩ :=
    original_bit model Wv Ws k values v hv b hb price index A hReplace
  dsimp only
  refine ⟨hm,physical,pair,hRun,hSource,hMatches,?_⟩
  rw [GeneralPaperNativeFairSamplerLaw.data,GeneralPaperNativeFairSamplerLaw.data]
  exact ⟨hA,hB,hSec,hRich,hPoor⟩

theorem dyadic_loss (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) :
    179*(1/(2:ℝ)^(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)/320≤(epsilon:ℝ) := by
  have h := (GeneralPaperDyadicAccuracy.accuracy_bounds epsilon hE hOne).2
  rw [GeneralPaperDyadicAccuracy.accuracy_power] at h
  have hCast : (((1/(2:ℚ)^(GeneralPaperDyadicAccuracy.prepare epsilon).exponent):ℚ):ℝ)≤(epsilon:ℝ) := by exact_mod_cast h
  have hReal : (1/(2:ℝ)^(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)≤(epsilon:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hCast
  have hPos : 0≤(1/(2:ℝ)^(GeneralPaperDyadicAccuracy.prepare epsilon).exponent) := by positivity
  linarith only [hReal,hPos]

theorem dyadic_field_count {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
    let o := (GeneralPaperOriginalSourceValuePreparation.run bits model W k values v hv).1
    (o.reduced.m:ℚ)≤36*min (n:ℚ) (1/epsilon) := by
  let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
  have hc := count_bounds bits model W k values v hv
  have hN : ((GeneralPaperOriginalSourceValuePreparation.run bits model W k values v hv).1.reduced.m:ℚ)≤n := by exact_mod_cast hc.2.1
  have hCap : ((GeneralPaperOriginalSourceValuePreparation.run bits model W k values v hv).1.reduced.m:ℚ)<18*(2:ℚ)^k := by exact_mod_cast hc.2.2
  have he := (GeneralPaperDyadicAccuracy.accuracy_bounds epsilon hE hOne).1
  rw [GeneralPaperDyadicAccuracy.accuracy_power] at he
  have hp : (0:ℚ)<(2:ℚ)^k := by positivity
  have hMul : epsilon*(2:ℚ)^k<2 := by
    have h := (lt_div_iff₀ hp).mp he
    nlinarith only [h]
  have hRecip : (2:ℚ)^k<2/epsilon := (lt_div_iff₀ hE).mpr (by nlinarith only [hMul])
  have hRecip' : (2:ℚ)^k<2*(1/epsilon) := by simpa only [div_eq_mul_inv,one_mul] using hRecip
  change ((GeneralPaperOriginalSourceValuePreparation.run bits model W k values v hv).1.reduced.m:ℚ)≤36*min (n:ℚ) (1/epsilon)
  by_cases hn : (n:ℚ)≤1/epsilon
  · rw [min_eq_left hn]
    nlinarith only [hN,show (0:ℚ)≤n from Nat.cast_nonneg n]
  · rw [min_eq_right (le_of_not_ge hn)]
    nlinarith only [hCap,hRecip']

theorem alphabet_size (m k : ℕ) :
    (GeneralPaperProxyParameters.alphabet m k).lambda+1≤2^30*(m+4)^2*2^k := by
  have h := GeneralPaperProxyWidths.lambda_bound m k
  have hK : (GeneralPaperProxyParameters.prepare m k).K=128*2^k := by
    rw [(GeneralPaperProxyParameters.data m k).1,GeneralPaperScoreScaleParameters.label_power,pow_add]
    norm_num
  have hC : (GeneralPaperComparatorParameters.countRun k).power=131072*2^k := by
    rw [GeneralPaperComparatorParameters.count_power,pow_add]
    norm_num
  have hD : (GeneralPaperProxyParameters.prepare m k).d≤128*m*2^k := by
    rw [(GeneralPaperProxyParameters.data m k).2.2.1]
    calc
      m*((GeneralPaperProxyParameters.prepare m k).K-1)≤m*(GeneralPaperProxyParameters.prepare m k).K := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _= _ := by rw [hK];ring
  have hT : m*((GeneralPaperComparatorParameters.countRun k).power-1)+1≤131072*m*2^k+1 := by
    have hh := Nat.mul_le_mul_left m (Nat.sub_le (GeneralPaperComparatorParameters.countRun k).power 1)
    rw [hC] at hh
    rw [hC]
    nlinarith only [hh]
  have hW : binaryWordWidth (m+3)≤m+4 := by
    have hh := Nat.log2_le_self (m+3)
    unfold binaryWordWidth
    omega
  have hV : binaryWordWidth (m+2)≤m+4 := (binaryWordWidth_mono (by omega : m+2≤m+3)).trans hW
  have hUpper : (GeneralPaperProxyParameters.alphabet m k).lambda≤
      24+4*(128*m*2^k+2)*(m+4)+2*(131072*m*2^k+1)*(m+4) := by
    apply h.trans
    gcongr
  have ha : 1≤2^k := Nat.one_le_two_pow
  nlinarith only [hUpper,ha,Nat.zero_le (m*m*2^k),Nat.zero_le (m*2^k),Nat.zero_le m]

theorem alphabet_word (m k : ℕ) :
    binaryWordWidth ((GeneralPaperProxyParameters.alphabet m k).lambda+1)≤32+2*binaryWordWidth (m+4)+k := by
  have h := binaryWordWidth_mono (alphabet_size m k)
  have h0 := binaryWordWidth_mul (2^30*(m+4)^2) (2^k)
  have h1 := binaryWordWidth_mul (2^30) ((m+4)^2)
  have h2 := binaryWordWidth_mul (m+4) (m+4)
  have hp : binaryWordWidth (2^k)=k+1 := by simp only [binaryWordWidth,Nat.log2_two_pow]
  have hc : binaryWordWidth (2^30)=31 := by decide
  rw [_root_.pow_two] at h h0 h1
  rw [hp] at h0
  rw [hc] at h1
  omega

def inputLog (n k B : ℕ) : ℕ := 128+k+binaryWordWidth (n+4)+binaryWordWidth (B+1)

theorem short_log_bound (x : Input) (n : ℕ) (hm : x.m≤n)
    (hQ : binaryWordWidth x.Qv≤binaryWordWidth x.m+x.k+11) :
    logSize x≤4*inputLog n x.k x.B ∧
      GeneralPaperSourceCoreLogBound.coreLog x≤4*inputLog n x.k 0 := by
  have hM : binaryWordWidth (x.m+1)≤binaryWordWidth (n+4) := binaryWordWidth_mono (by omega)
  have hM0 : binaryWordWidth x.m≤binaryWordWidth (n+4) := binaryWordWidth_mono (by omega)
  have hM4 : binaryWordWidth (x.m+4)≤binaryWordWidth (n+4) := binaryWordWidth_mono (by omega)
  have hL := alphabet_word x.m x.k
  have hQ1 := GeneralPaperReferenceScaling.word_add x.Qv 1
  have hOne : binaryWordWidth 1=1 := by decide
  rw [hOne] at hQ1
  constructor
  · unfold logSize inputLog
    change 128+x.k+binaryWordWidth (x.m+1)+binaryWordWidth ((GeneralPaperProxyParameters.alphabet x.m x.k).lambda+1)+
      binaryWordWidth (x.Qv+1)+binaryWordWidth (x.B+1)≤_
    omega
  · unfold GeneralPaperSourceCoreLogBound.coreLog GeneralPaperSourcePreparationSizes.measure inputLog
    change 128+x.k+binaryWordWidth ((GeneralPaperProxyParameters.alphabet x.m x.k).lambda+1)+binaryWordWidth (x.m+1)+
      binaryWordWidth (x.Qv+1)≤_
    omega

theorem original_log_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k B : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    let x := input (GeneralPaperOriginalSourceValuePreparation.run bits model W k values v hv).1 k B b hb hB
    logSize x≤4*inputLog n k B ∧ GeneralPaperSourceCoreLogBound.coreLog x≤4*inputLog n k 0 :=
  short_log_bound _ n (count_bounds bits model W k values v hv).2.1 (denominator_word bits model W k values v hv)

theorem input_log_positive (n k B : ℕ) : 1≤ inputLog n k B := by unfold inputLog;omega

theorem arithmetic_price_bound (n k : ℕ) :
    GeneralPaperOriginalSourceValuePrice.arithmeticPrice n k≤8192*(n+1)*(inputLog n k 0)^2 := by
  let L := inputLog n k 0
  have hN : binaryWordWidth n≤binaryWordWidth (n+4) := binaryWordWidth_mono (by omega)
  have hk : binaryWordWidth k+1≤L := by
    have h := Nat.log2_le_self k
    unfold binaryWordWidth L inputLog
    omega
  have hp : binaryWordWidth (2^k)=k+1 := by simp only [binaryWordWidth,Nat.log2_two_pow]
  have hA : binaryWordWidth (GeneralPaperValueRoundingPaperContract.scale 256 n k)≤L := by
    have h0 := binaryWordWidth_mul (256*n) (2^k)
    have h1 := binaryWordWidth_mul 256 n
    rw [show binaryWordWidth 256=9 by decide] at h1
    rw [hp] at h0
    unfold L inputLog GeneralPaperValueRoundingPaperContract.scale
    omega
  have hB : binaryWordWidth (GeneralPaperValueRoundingPaperContract.scale 512 n k)≤L := by
    have h0 := binaryWordWidth_mul (512*n) (2^k)
    have h1 := binaryWordWidth_mul 512 n
    rw [show binaryWordWidth 512=10 by decide] at h1
    rw [hp] at h0
    unfold L inputLog GeneralPaperValueRoundingPaperContract.scale
    omega
  have hL : 1≤L := input_log_positive n k 0
  have hSquare : L≤L^2 := by simpa only [_root_.pow_two] using Nat.le_mul_of_pos_left L hL
  have hOne : 1≤L^2 := Nat.one_le_pow _ _ hL
  calc
    _≤256*L^2+(n*(14*L+135)+44*(n+1)+108*n+192)+
      (n*(14*L+135)+44*(n+1)+108*n+192)+210*n+1539 := by
        unfold GeneralPaperOriginalSourceValuePrice.arithmeticPrice GeneralPaperValueRoundingDriver.arithmeticProfile
          GeneralPaperValueRoundArray.arithmeticProfile
        gcongr
    _≤8192*(n+1)*L^2 := by
      nlinarith only [Nat.mul_le_mul_left n hSquare,Nat.mul_le_mul_left n hOne,hOne,Nat.zero_le (n*L^2)]

theorem bit_input_time {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ {n : ℕ} (Wv k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B),
      let o := (GeneralPaperOriginalSourceValuePreparation.run true model Wv k values v hv).1
      let x := input o k B b hb hB
      let Ws := GeneralPaperFastDriverReference.width C d x
      (bit model Wv Ws k values v hv b hb).2≤GeneralPaperOriginalSourceValuePrice.bitPrice model Wv k values+
        A*(B+1+monomial 3 0 6 x)*(inputLog n k B)^e := by
  obtain ⟨A,e,h⟩ := bit_source_time hg
  refine ⟨A*4^e,e,?_⟩
  intro n Wv k B values v hv b hb hB
  have hLog := (original_log_bound true model Wv k B values v hv b hb hB).1
  apply (h Wv k B values v hv b hb hB).trans
  apply Nat.add_le_add_left
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e)).trans_eq (by rw [mul_pow];ring)

theorem real_input_time (model : RationalCostModel) :
    ∃ A e : ℕ,∀ {n : ℕ} (k : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j=v.weight j) (b : ℝ),0<b ∧ b<1 →
      let o := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
      let x := input o k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])
      (arithmetic model k values v hv b).2≤A*(n+1+monomial 2 0 5 x)*(inputLog n k 0)^e := by
  obtain ⟨A,e,h⟩ := real_source_time model
  refine ⟨8192+A*4^e+128,e+2,?_⟩
  intro n k values v hv b hb
  let o := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
  let x := input o k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])
  let L := inputLog n k 0
  let R := n+1+monomial 2 0 5 x
  have hL : 1≤L := input_log_positive n k 0
  have hR : 1≤R := by dsimp only [R];omega
  have hN : n+1≤R := by dsimp only [R];omega
  have hM : monomial 2 0 5 x≤R := by dsimp only [R];omega
  have he : L^e≤L^(e+2) := Nat.pow_le_pow_right hL (by omega)
  have hTwo : L^2≤L^(e+2) := Nat.pow_le_pow_right hL (by omega)
  have hLog : GeneralPaperSourceCoreLogBound.coreLog x≤4*L :=
    (original_log_bound false model 1 k 2 values v hv (1/2) (by norm_num) (by norm_num [RationalHeight])).2
  have hFirst : GeneralPaperOriginalSourceValuePrice.arithmeticPrice n k≤8192*R*L^(e+2) :=
    (arithmetic_price_bound n k).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 8192 hN) hTwo)
  have hSource : A*monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e≤A*4^e*R*L^(e+2) := by
    calc
      _≤A*monomial 2 0 5 x*(4*L)^e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e)
      _=A*4^e*monomial 2 0 5 x*L^e := by rw [mul_pow];ring
      _≤A*4^e*R*L^(e+2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) he
  have hParent : 128≤128*R*L^(e+2) := by
    have hp := Nat.mul_le_mul hR (Nat.one_le_pow (e+2) L hL)
    simpa only [Nat.one_mul,Nat.mul_one,Nat.mul_assoc] using Nat.mul_le_mul_left 128 hp
  exact (h k values v hv b hb).trans ((Nat.add_le_add (Nat.add_le_add hFirst hSource) hParent).trans_eq (by ring))

theorem original_source_word {C d : ℕ} : ∃ K : ℕ,∀ {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k B : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B),
    GeneralPaperFastDriverReference.width C d (input (GeneralPaperOriginalSourceValuePreparation.run bits model W k values v hv).1 k B b hb hB)≤
      K*inputLog n k B := by
  obtain ⟨K,h⟩ := GeneralPaperFastDriverReference.width_tight C d
  refine ⟨K*4,?_⟩
  intro n bits model W k B values v hv b hb hB
  exact (h _).trans ((Nat.mul_le_mul_left K (original_log_bound bits model W k B values v hv b hb hB).1).trans_eq (by ring))

theorem original_arithmetic {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run false model 1 k values).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector false model 1 k values v hv
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives),∃ (physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (GeneralPaperOriginalSourceValueDriver.arithmetic model k values v hv (b:ℝ)).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run false model 1 k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let μ := GeneralPaperOriginalDrawLaw.law hT (count_positive k) model o hR 1 (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.rich).1
      let ν := GeneralPaperOriginalDrawLaw.law hT (count_positive k) model o hR b (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.poor).1
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
      security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
      regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧ regret v.values (b:ℝ) ν μ≤179*(1/(2:ℝ)^k)/320 := by
  obtain ⟨hm,pair,hSource,hLaw⟩ := GeneralPaperOriginalDrawEquilibrium.original false false model 1 1 k values v hv b hb price index A hReplace
  obtain ⟨physical,actualPair,hRun,hActual,hMatches,_⟩ := arithmetic_return model k values v hv (b:ℝ) (by exact_mod_cast hb)
  have he : actualPair=pair := Option.some.inj (hActual.symm.trans hSource)
  subst actualPair
  exact ⟨hm,physical,pair,hRun,hSource,hMatches,hLaw physical hMatches⟩

theorem sampled_original_arithmetic {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run false model 1 k values).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector false model 1 k values v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives),∃ (physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (GeneralPaperOriginalSourceValueDriver.arithmetic model k values v hv (b:ℝ)).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run false model 1 k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let μ := GeneralPaperNativeFairSamplerLaw.law primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR 1
        (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.rich).1
      let ν := GeneralPaperNativeFairSamplerLaw.law primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR b
        (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.poor).1
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
      security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
      regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧ regret v.values (b:ℝ) ν μ≤179*(1/(2:ℝ)^k)/320 := by
  obtain ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich,hPoor⟩ :=
    original_arithmetic model k values v hv b hb price index A hReplace
  dsimp only
  refine ⟨hm,physical,pair,hRun,hSource,hMatches,?_⟩
  rw [GeneralPaperNativeFairSamplerLaw.data,GeneralPaperNativeFairSamplerLaw.data]
  exact ⟨hA,hB,hSec,hRich,hPoor⟩

theorem sampled_original_bit_epsilon {n : ℕ} (model : RationalCostModel) (Wv Ws k : ℕ) (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run true model Wv k values).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector true model Wv k values v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives),∃ (physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (bit model Wv Ws k values v hv b hb).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run true model Wv k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let μ := GeneralPaperNativeFairSamplerLaw.law primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR 1
        (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.rich).1
      let ν := GeneralPaperNativeFairSamplerLaw.law primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR b
        (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.poor).1
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
      security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
      regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) := by
  have hLoss : 179*(1/(2:ℝ)^k)/320≤(epsilon:ℝ) := by rw [hk];exact dyadic_loss epsilon hE hOne
  obtain ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich,hPoor⟩ :=
    sampled_original_bit model Wv Ws k values v hv b hb price index primitive A hReplace
  dsimp only
  exact ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich.trans hLoss,hPoor.trans hLoss⟩

theorem sampled_original_arithmetic_epsilon {n : ℕ} (model : RationalCostModel) (k : ℕ) (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run false model 1 k values).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector false model 1 k values v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives),∃ (physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (GeneralPaperOriginalSourceValueDriver.arithmetic model k values v hv (b:ℝ)).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run false model 1 k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let μ := GeneralPaperNativeFairSamplerLaw.law primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR 1
        (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.rich).1
      let ν := GeneralPaperNativeFairSamplerLaw.law primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR b
        (GeneralPaperOriginalCirclePreparation.run price index A o hm physical.poor).1
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
      security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
      regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) := by
  have hLoss : 179*(1/(2:ℝ)^k)/320≤(epsilon:ℝ) := by rw [hk];exact dyadic_loss epsilon hE hOne
  obtain ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich,hPoor⟩ :=
    sampled_original_arithmetic model k values v hv b hb price index primitive A hReplace
  dsimp only
  exact ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich.trans hLoss,hPoor.trans hLoss⟩

end Blotto.GeneralPaperOriginalSourceValueContract
