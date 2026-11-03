import Blotto.GeneralPaperNativeSamplingParameters

/-! Fast-rational prices preserve the linear original-budget/output height.
Short control arithmetic and final rational output products are bounded
separately before the complete native draw profile is combined. -/
namespace Blotto.GeneralPaperSamplingFastBitBound
open GeneralPaperNativeSamplingParameters GeneralPaperSamplingOperandEnvelope
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

theorem word_self (a : ℕ) : binaryWordWidth a≤a+1 := by
  unfold binaryWordWidth
  have h := Nat.log2_le_self a
  omega

theorem operand_widths (n m k B H L : ℕ) (hm : m≤n)
    (hH : H≤16777216*scale m k*binaryWordWidth (m+3)) (hL : L≤16*logarithm n k B) :
    let ell := logarithm n k B
    let R := B+scale m k+1
    64*L≤1024*ell ∧ binaryWordWidth (64*L+1)+1≤16*ell ∧
      8*(B+H+L)≤268435456*R*ell ∧ binaryWordWidth (8*(B+H+L)+1)+1≤128*ell := by
  let ell := logarithm n k B
  let M := scale m k
  let R := B+M+1
  have he : 1≤ell := log_positive n k B
  change L≤16*ell at hL
  change H≤16777216*M*binaryWordWidth (m+3) at hH
  have hw : binaryWordWidth (m+3)≤ell := by
    have h := binaryWordWidth_mono (show m+3≤n+4 by omega)
    unfold ell logarithm
    omega
  have hMW : binaryWordWidth M≤ell := by
    have h := binaryWordWidth_mul (m+1) (2^k)
    rw [show binaryWordWidth (2^k)=k+1 by simp only [binaryWordWidth,Nat.log2_two_pow]] at h
    have hn := binaryWordWidth_mono (show m+1≤n+4 by omega)
    unfold M scale ell logarithm
    omega
  have hBW : binaryWordWidth B≤ell := by
    have h := binaryWordWidth_mono (show B≤B+1 by omega)
    unfold ell logarithm
    omega
  have hRW : binaryWordWidth R≤2*ell+1 := by
    have h1 := word_add (B+M) 1
    have h2 := word_add B M
    rw [show binaryWordWidth 1=1 by decide] at h1
    dsimp only [R]
    omega
  have hEllW := word_self ell
  have hShort : 64*L≤1024*ell := by omega
  have hShortW : binaryWordWidth (64*L+1)+1≤16*ell := by
    have h1 := word_add (64*L) 1
    have h2 := (binaryWordWidth_mono hShort).trans (binaryWordWidth_mul 1024 ell)
    rw [show binaryWordWidth 1=1 by decide] at h1
    rw [show binaryWordWidth 1024=11 by decide] at h2
    omega
  have hHeight : H≤16777216*M*ell := hH.trans (Nat.mul_le_mul_left _ hw)
  have hB := Nat.mul_le_mul_left B he
  have hLong : 8*(B+H+L)≤268435456*R*ell := by
    dsimp only [R]
    nlinarith only [hHeight,hB,hL,Nat.zero_le (M*ell)]
  have hLongW : binaryWordWidth (8*(B+H+L)+1)+1≤128*ell := by
    have h1 := word_add (8*(B+H+L)) 1
    have h2 := (binaryWordWidth_mono hLong).trans (binaryWordWidth_mul (268435456*R) ell)
    have h3 := binaryWordWidth_mul 268435456 R
    rw [show binaryWordWidth 1=1 by decide] at h1
    rw [show binaryWordWidth 268435456=29 by decide] at h3
    omega
  exact ⟨hShort,hShortW,hLong,hLongW⟩

theorem fast_price {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (w K J rate ell : ℕ) (hWidth : w≤K*rate*ell) (hWord : binaryWordWidth (w+1)+1≤J*ell) :
    model.rat w≤(C*K*J^d)*rate*ell^(d+1) := by
  have hp := Nat.pow_le_pow_left hWord d
  calc
    _≤C*w*(binaryWordWidth (w+1)+1)^d := hg w
    _≤C*(K*rate*ell)*(J*ell)^d := Nat.mul_le_mul (Nat.mul_le_mul_left C hWidth) hp
    _=(C*K*J^d)*rate*ell^(d+1) := by rw [mul_pow,pow_succ];ring

theorem two_prices {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (n m k B H L : ℕ) (hm : m≤n)
    (hH : H≤16777216*scale m k*binaryWordWidth (m+3)) (hL : L≤16*logarithm n k B) :
    model.rat (64*L)≤(C*1024*16^d)*(logarithm n k B)^(d+1) ∧
      model.rat (8*(B+H+L))≤(C*268435456*128^d)*(B+scale m k+1)*(logarithm n k B)^(d+1) := by
  have h := operand_widths n m k B H L hm hH hL
  exact ⟨by simpa only [Nat.mul_one] using fast_price hg (64*L) 1024 16 1 _ (by simpa only [Nat.mul_one] using h.1) h.2.1,
    fast_price hg (8*(B+H+L)) 268435456 128 _ _ h.2.2.1 h.2.2.2⟩

def coefficient (C d : ℕ) : ℕ := 10485760*(C*1024*16^d)+6*(C*268435456*128^d)

theorem envelope_bound {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (n m k B H L : ℕ) (hn : 0<n) (hm : m≤n)
    (hH : H≤16777216*scale m k*binaryWordWidth (m+3)) (hL : L≤16*logarithm n k B) :
    65536*(n+GeneralPaperLightFieldReduction.representatives k+1)*L*model.rat (64*L)+6*n*model.rat (8*(B+H+L))≤
      coefficient C d*n*(B+scale m k+1)*(logarithm n k B)^(d+2) := by
  let ell := logarithm n k B
  let M := scale m k
  let R := B+M+1
  let P := C*1024*16^d
  let Q := C*268435456*128^d
  have hPrice := two_prices hg n m k B H L hm hH hL
  change model.rat (64*L)≤P*ell^(d+1) ∧ model.rat (8*(B+H+L))≤Q*R*ell^(d+1) at hPrice
  change L≤16*ell at hL
  have he : 1≤ell := log_positive n k B
  have hM : 1≤M := Nat.mul_pos (by omega) (Nat.two_pow_pos k)
  have hRep : GeneralPaperLightFieldReduction.representatives k≤8*M := by
    unfold GeneralPaperLightFieldReduction.representatives M scale
    have h := Nat.mul_le_mul_right (2^k) (show 1≤m+1 by omega)
    nlinarith only [h]
  have hCount : n+GeneralPaperLightFieldReduction.representatives k+1≤10*n*R := by
    have hnM := Nat.mul_le_mul_left M (show 1≤n by omega)
    have hmN := Nat.mul_le_mul_left n hM
    dsimp only [R]
    nlinarith only [hRep,hnM,hmN,hn,hM,Nat.zero_le (n*B)]
  have hShort := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 65536 hCount) hL) hPrice.1
  have hShort' : 65536*(n+GeneralPaperLightFieldReduction.representatives k+1)*L*model.rat (64*L)≤
      10485760*P*n*R*ell^(d+2) := hShort.trans_eq (by rw [show d+2=(d+1)+1 by omega,pow_succ];ring)
  have hPow : ell^(d+1)≤ell^(d+2) := Nat.pow_le_pow_right he (by omega)
  have hLong : 6*n*model.rat (8*(B+H+L))≤6*Q*n*R*ell^(d+2) := by
    have hp := Nat.mul_le_mul_left (6*n) hPrice.2
    have hq := Nat.mul_le_mul_left (6*n*(Q*R)) hPow
    nlinarith only [hp,hq]
  have hTotal := Nat.add_le_add hShort' hLong
  exact hTotal.trans_eq (by dsimp only [coefficient,P,Q,ell,R,M];ring)


theorem native_profile {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    {n : ℕ} (Wv k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let A := GeneralPaperClosedBitSampling.reference n o.m k
    let H := GeneralPaperSourcePairAnchorHeights.width o.m k
    GeneralPaperClosedBitSampling.profile model A t.rowBits k B H o≤
      coefficient C d*n*(B+scale o.m k+1)*(logarithm n k B)^(d+2) := by
  let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let A := GeneralPaperClosedBitSampling.reference n o.m k
  let H := GeneralPaperSourcePairAnchorHeights.width o.m k
  let L := controlSize A t.rowBits (k+6) o.representatives o.classified.lightWeight (GeneralPaperNativeSelectedSecurity.count k)
  have hm : o.m≤n := (GeneralPaperOriginalValueReduction.count_bounds true model Wv k values v hv).2.1
  have hW := (binaryWordWidth_mono (GeneralPaperNativeCircleLoss.original_mass_bound true model Wv k values)).trans
    (GeneralPaperOriginalValueReduction.denominator_word true model Wv k values v hv)
  have hRep : o.representatives=GeneralPaperLightFieldReduction.representatives k :=
    GeneralPaperNativeReductionShape.original_representatives true model Wv k values
  have hL : L≤16*logarithm n k B := by
    have h := control_size n o.m k B o.classified.lightWeight hm hW
    rw [←hRep] at h
    exact h
  have hEnvelope := combined_profile model A t.rowBits k B H o
    (GeneralPaperStrategyPreparationWork.light_size true model Wv k values)
    (GeneralPaperClosedArithmeticSampling.heavy_size true model Wv k values)
  have hFast := envelope_bound hg n o.m k B H L v.fields_positive hm (anchor_height o.m k) hL
  rw [←hRep] at hFast
  exact hEnvelope.trans hFast

theorem bit_return_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    {n : ℕ} (Wv Ws Ap : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    let prepared := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := prepared.raw.strategies.original.reduced
    let k := prepared.raw.exponent
    let H := GeneralPaperSourcePairAnchorHeights.width o.m k
    let A := GeneralPaperClosedBitSampling.reference n o.m k
    ∃ sampler : GeneralPaperStoredStrategySampler.Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.sampler=some sampler ∧
      ∀ (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool),
        (GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).work≤
          coefficient C d*n*(B+scale o.m k+1)*(logarithm n k B)^(d+2) ∧
        (∀ j,RationalHeight ((GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).output.read j)
          (GeneralPaperClosedBitSampling.outputHeight o B H)) ∧
        GeneralPaperClosedBitSampling.outputBits (GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).output≤
          n*(1+2*GeneralPaperClosedBitSampling.outputHeight o B H) ∧
        (GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).freshReads=
          Nat.log2 (sampler.controls.rows*sampler.controls.shifts) := by
  obtain ⟨sampler,hSampler,hBounds⟩ := GeneralPaperClosedBitSampling.bit_return_bounds model Wv Ws Ap words values v hv b hb B hB
  dsimp only
  refine ⟨sampler,hSampler,?_⟩
  intro reciprocal fresh
  have h := hBounds reciprocal fresh
  exact ⟨h.1.trans (native_profile hg Wv _ B values v hv),h.2⟩


def epsilonLog (n : ℕ) (epsilon : ℚ) (B : ℕ) : ℕ :=
  128+binaryWordWidth ⌈epsilon⁻¹⌉₊+binaryWordWidth (n+4)+binaryWordWidth (B+1)

theorem epsilon_scale {n : ℕ} (model : RationalCostModel) (Wv k B : ℕ) (epsilon : ℚ)
    (hE : 0<epsilon) (hOne : epsilon<1) (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    ((B+scale (GeneralPaperOriginalValueReduction.run true model Wv k values).1.m k+1:ℕ):ℚ)≤
      76*((B:ℚ)+GeneralPaperRealHeadlineParameters.nStar n epsilon/epsilon) := by
  subst k
  let m := (GeneralPaperOriginalValueReduction.run true model Wv (GeneralPaperDyadicAccuracy.prepare epsilon).exponent values).1.m
  let N := GeneralPaperRealHeadlineParameters.nStar n epsilon
  have hStar : 1≤N := GeneralPaperRealHeadlineParameters.nstar_positive n v.fields_positive epsilon hE hOne
  have hM : (m:ℚ)≤36*N := GeneralPaperOriginalSourceValueContract.dyadic_field_count true model Wv epsilon hE hOne values v hv
  have hPower := GeneralPaperRealHeadlineParameters.power_bound epsilon hE hOne
  have hM' : (m:ℚ)+1≤37*N := by linarith only [hM,hStar]
  have hProduct := mul_le_mul hM' hPower (by positivity) (by positivity)
  have hProduct' : ((m:ℚ)+1)*(2:ℚ)^(GeneralPaperDyadicAccuracy.prepare epsilon).exponent≤74*(N/epsilon) :=
    hProduct.trans_eq (by ring)
  have hUnit : (1:ℚ)≤N/epsilon := (le_div_iff₀ hE).mpr (by linarith only [hOne,hStar])
  change ((B+scale m (GeneralPaperDyadicAccuracy.prepare epsilon).exponent+1:ℕ):ℚ)≤76*((B:ℚ)+N/epsilon)
  unfold scale
  push_cast
  nlinarith only [hProduct',hUnit,show (0:ℚ)≤B by positivity]

theorem epsilon_bit_draw {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    {n : ℕ} (Wv Ws Ap : ℕ) (words : BinaryAccuracyWords) (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (hInput : epsilon=(words.numerator.value:ℚ)/words.denominator.value)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    let prepared := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := prepared.raw.strategies.original.reduced
    let k := prepared.raw.exponent
    let A := GeneralPaperClosedBitSampling.reference n o.m k
    ∃ sampler : GeneralPaperStoredStrategySampler.Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.sampler=some sampler ∧
      ∀ (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool),
        ((GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).work:ℚ)≤
          ((76*coefficient C d:ℕ):ℚ)*(n:ℚ)*((B:ℚ)+GeneralPaperRealHeadlineParameters.nStar n epsilon/epsilon)*
            (epsilonLog n epsilon B:ℚ)^(d+2) ∧
        (GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).freshReads=
          Nat.log2 (sampler.controls.rows*sampler.controls.shifts) := by
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  let m := (GeneralPaperOriginalValueReduction.run true model Wv k values).1.m
  have hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent :=
    GeneralPaperBinaryAccuracy.exact_exponent (fun w => w) Ap words epsilon hInput
  have hScale := epsilon_scale model Wv k B epsilon hE hOne hk values v hv
  have hLog : logarithm n k B≤epsilonLog n epsilon B := by
    have hK : k≤binaryWordWidth ⌈epsilon⁻¹⌉₊ := hk ▸ GeneralPaperRealHeadlineParameters.exponent_bound epsilon
    unfold logarithm epsilonLog
    omega
  have hPow : (logarithm n k B:ℚ)^(d+2)≤(epsilonLog n epsilon B:ℚ)^(d+2) := by
    exact_mod_cast Nat.pow_le_pow_left hLog (d+2)
  have hStar := GeneralPaperRealHeadlineParameters.nstar_positive n v.fields_positive epsilon hE hOne
  have hNonneg : (0:ℚ)≤GeneralPaperRealHeadlineParameters.nStar n epsilon := by linarith only [hStar]
  obtain ⟨sampler,hSampler,hBounds⟩ := bit_return_rate hg Wv Ws Ap words values v hv b hb B hB
  dsimp only
  refine ⟨sampler,hSampler,?_⟩
  intro reciprocal fresh
  have h := hBounds reciprocal fresh
  refine ⟨?_,h.2.2.2⟩
  have hQ : ((GeneralPaperStoredStrategySampler.run true model.rat
      (GeneralPaperClosedBitSampling.reference n m k) model sampler reciprocal fresh).work:ℚ)≤
      (coefficient C d:ℚ)*(n:ℚ)*((B+scale m k+1:ℕ):ℚ)*(logarithm n k B:ℚ)^(d+2) := by exact_mod_cast h.1
  calc
    _≤(coefficient C d:ℚ)*(n:ℚ)*((B+scale m k+1:ℕ):ℚ)*(logarithm n k B:ℚ)^(d+2) := hQ
    _≤(coefficient C d:ℚ)*(n:ℚ)*(76*((B:ℚ)+GeneralPaperRealHeadlineParameters.nStar n epsilon/epsilon))*
        (epsilonLog n epsilon B:ℚ)^(d+2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hScale (by positivity)) hPow (by positivity) (by positivity)
    _=((76*coefficient C d:ℕ):ℚ)*(n:ℚ)*((B:ℚ)+GeneralPaperRealHeadlineParameters.nStar n epsilon/epsilon)*
        (epsilonLog n epsilon B:ℚ)^(d+2) := by push_cast;ring

end Blotto.GeneralPaperSamplingFastBitBound
