import Blotto.GeneralPaperDirectRowSampler

/-! Original-game guarantee in the identity branch. Only first-round
value perturbation is needed; no circle reconstruction error is incurred.
Native source returns feed the direct finite-bit row sampler unchanged. -/
namespace Blotto.GeneralPaperUnreplacedSourceContract
open GeneralPaperOriginalDrawEquilibrium GeneralPaperOriginalSourceValueDriver
open GeneralPaperNativeSelectedSecurity
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

theorem canonical {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℝ) (hb : 0<b ∧ b<1) (hNo : (GeneralPaperOriginalValueReduction.run bits model W k values).1.replaced=false) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector bits model W k values v hv
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∃ (hm:o.m=n),∃ pair,
      GeneralPaperRoundedValueCanonical.run valueBits model Wv k o.values redValues (fun _ => rfl) b=some pair ∧
      let μ := GeneralPaperFieldRelabel.law (finCongr hm.symm) (GeneralPaperSourcePairCanonical.richLaw pair hT)
      let ν := GeneralPaperFieldRelabel.law (finCongr hm.symm) (GeneralPaperSourcePairCanonical.poorLaw pair hT b)
      Supported 1 μ ∧ Supported b ν ∧ security v.values 1 ν+security v.values b μ<1+5*(1/(2:ℝ)^k)/64 ∧
      regret v.values 1 μ ν≤5*(1/(2:ℝ)^k)/64 ∧ regret v.values b ν μ≤5*(1/(2:ℝ)^k)/64 := by
  obtain ⟨hm,hValues⟩ := GeneralPaperUnreplacedShape.selector_values bits model W k values v hv hNo
  obtain ⟨pair,hRun,hRich,hPoor,hSec,_⟩ := GeneralPaperRoundedValueCanonical.run_security valueBits model Wv k
    (GeneralPaperOriginalValueReduction.run bits model W k values).1.values
    (GeneralPaperOriginalValueReduction.selector bits model W k values v hv) (fun _ => rfl) b hb
  dsimp only
  refine ⟨hm,pair,hRun,?_⟩
  let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet (GeneralPaperOriginalValueReduction.run bits model W k values).1.m k).lambda k
  let e := finCongr hm.symm
  let μ := GeneralPaperFieldRelabel.law e (GeneralPaperSourcePairCanonical.richLaw pair hT)
  let ν := GeneralPaperFieldRelabel.law e (GeneralPaperSourcePairCanonical.poorLaw pair hT b)
  have hA : Supported 1 μ := GeneralPaperFieldRelabel.supported e _ 1 hRich
  have hB : Supported b ν := GeneralPaperFieldRelabel.supported e _ b hPoor
  have hSA := GeneralPaperValuePerturbation.security_le_shift v.values
    (GeneralPaperNativeReductionShape.firstSelector bits model W k values v hv).values b hb.1.le μ
  have hSB := GeneralPaperValuePerturbation.security_le_shift v.values
    (GeneralPaperNativeReductionShape.firstSelector bits model W k values v hv).values 1 (by norm_num) ν
  rw [←hValues,GeneralPaperFieldRelabel.security_relabel] at hSA hSB
  have hd := GeneralPaperNativeCircleSourcePair.original_distance bits model W k values v hv
  rw [←hValues] at hd
  have hTotal : security v.values 1 ν+security v.values b μ<1+5*(1/(2:ℝ)^k)/64 := by
    linarith only [hSA,hSB,hSec,hd]
  exact ⟨hA,hB,hTotal,regrets_le_of_security_sum v.values μ ν hA hB hTotal.le⟩

theorem sampled_bit {n : ℕ} (model : RationalCostModel) (Wv Ws k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hNo : (GeneralPaperOriginalValueReduction.run true model Wv k values).1.replaced=false) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector true model Wv k values v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ (hm:o.m=n),∃ (physical : Columns trajectory.rows o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (bit model Wv Ws k values v hv b hb).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run true model Wv k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let μ := GeneralPaperDirectRowSampler.law price index primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift hm 1 physical.rich
      let ν := GeneralPaperDirectRowSampler.law price index primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift hm b physical.poor
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ security v.values 1 ν+security v.values (b:ℝ) μ<1+5*(1/(2:ℝ)^k)/64 ∧
      regret v.values 1 μ ν≤5*(1/(2:ℝ)^k)/64 ∧ regret v.values (b:ℝ) ν μ≤5*(1/(2:ℝ)^k)/64 := by
  obtain ⟨hm,pair,hSource,hLaw⟩ := canonical true true model Wv Wv k values v hv (b:ℝ) (by exact_mod_cast hb) hNo
  obtain ⟨(physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet (GeneralPaperOriginalValueReduction.run true model Wv k values).1.m k).lambda k).rows
      (GeneralPaperOriginalValueReduction.run true model Wv k values).1.m
      (GeneralPaperProxyParameters.prepare (GeneralPaperOriginalValueReduction.run true model Wv k values).1.m k).K),actualPair,hRun,hActual,hMatches,_⟩ :=
    bit_return model Wv Ws k values v hv b hb
  have he : actualPair=pair := Option.some.inj (hActual.symm.trans hSource)
  subst actualPair
  dsimp only
  refine ⟨hm,physical,pair,hRun,hSource,hMatches,?_⟩
  have hRich : GeneralPaperRowQuantizer.dictionary physical.rich=pair.rich := hMatches.1
  have hPoor : GeneralPaperRowQuantizer.dictionary physical.poor=pair.poor := hMatches.2
  rw [GeneralPaperDirectRowSampler.law_data,GeneralPaperDirectRowSampler.law_data,hRich,hPoor]
  simp only [Rat.cast_one,GeneralPaperOriginalDrawScale.one]
  exact hLaw


theorem sampled_arithmetic {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hNo : (GeneralPaperOriginalValueReduction.run false model 1 k values).1.replaced=false) :
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector false model 1 k values v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ (hm:o.m=n),∃ (physical : Columns trajectory.rows o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (arithmetic model k values v hv (b:ℝ)).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run false model 1 k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let μ := GeneralPaperDirectRowSampler.law price index primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift hm 1 physical.rich
      let ν := GeneralPaperDirectRowSampler.law price index primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift hm b physical.poor
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ security v.values 1 ν+security v.values (b:ℝ) μ<1+5*(1/(2:ℝ)^k)/64 ∧
      regret v.values 1 μ ν≤5*(1/(2:ℝ)^k)/64 ∧ regret v.values (b:ℝ) ν μ≤5*(1/(2:ℝ)^k)/64 := by
  obtain ⟨hm,pair,hSource,hLaw⟩ := canonical false false model 1 1 k values v hv (b:ℝ) (by exact_mod_cast hb) hNo
  obtain ⟨(physical : Columns
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m k).lambda k).rows
      (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m
      (GeneralPaperProxyParameters.prepare (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m k).K),actualPair,hRun,hActual,hMatches,_⟩ :=
    arithmetic_return model k values v hv (b:ℝ) (by exact_mod_cast hb)
  have he : actualPair=pair := Option.some.inj (hActual.symm.trans hSource)
  subst actualPair
  dsimp only
  refine ⟨hm,physical,pair,hRun,hSource,hMatches,?_⟩
  have hRich : GeneralPaperRowQuantizer.dictionary physical.rich=pair.rich := hMatches.1
  have hPoor : GeneralPaperRowQuantizer.dictionary physical.poor=pair.poor := hMatches.2
  rw [GeneralPaperDirectRowSampler.law_data,GeneralPaperDirectRowSampler.law_data,hRich,hPoor]
  simp only [Rat.cast_one,GeneralPaperOriginalDrawScale.one]
  exact hLaw

theorem sampled_bit_epsilon {n : ℕ} (model : RationalCostModel) (Wv Ws k : ℕ)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hNo : (GeneralPaperOriginalValueReduction.run true model Wv k values).1.replaced=false) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector true model Wv k values v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ (hm:o.m=n),∃ (physical : Columns trajectory.rows o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (bit model Wv Ws k values v hv b hb).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run true model Wv k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let μ := GeneralPaperDirectRowSampler.law price index primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift hm 1 physical.rich
      let ν := GeneralPaperDirectRowSampler.law price index primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift hm b physical.poor
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ security v.values 1 ν+security v.values (b:ℝ) μ<1+5*(1/(2:ℝ)^k)/64 ∧
      regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) := by
  have hLoss : 179*(1/(2:ℝ)^k)/320≤(epsilon:ℝ) := by
    rw [hk]
    exact GeneralPaperOriginalSourceValueContract.dyadic_loss epsilon hE hOne
  have hSmall : 5*(1/(2:ℝ)^k)/64≤(epsilon:ℝ) := by
    have hp : 0≤1/(2:ℝ)^k := by positivity
    linarith only [hLoss,hp]
  obtain ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich,hPoor⟩ := sampled_bit model Wv Ws k values v hv b hb price index primitive A hNo
  dsimp only
  exact ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich.trans hSmall,hPoor.trans hSmall⟩

theorem sampled_arithmetic_epsilon {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hNo : (GeneralPaperOriginalValueReduction.run false model 1 k values).1.replaced=false) :
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    let redValues := GeneralPaperOriginalValueReduction.selector false model 1 k values v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ (hm:o.m=n),∃ (physical : Columns trajectory.rows o.m (GeneralPaperProxyParameters.prepare o.m k).K),∃ pair,
      (arithmetic model k values v hv (b:ℝ)).1.physical=some physical ∧
      GeneralPaperRoundedValueCanonical.run false model 1 k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧ Matches physical pair ∧
      let μ := GeneralPaperDirectRowSampler.law price index primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift hm 1 physical.rich
      let ν := GeneralPaperDirectRowSampler.law price index primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift hm b physical.poor
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ security v.values 1 ν+security v.values (b:ℝ) μ<1+5*(1/(2:ℝ)^k)/64 ∧
      regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) := by
  have hLoss : 179*(1/(2:ℝ)^k)/320≤(epsilon:ℝ) := by
    rw [hk]
    exact GeneralPaperOriginalSourceValueContract.dyadic_loss epsilon hE hOne
  have hSmall : 5*(1/(2:ℝ)^k)/64≤(epsilon:ℝ) := by
    have hp : 0≤1/(2:ℝ)^k := by positivity
    linarith only [hLoss,hp]
  obtain ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich,hPoor⟩ := sampled_arithmetic model k values v hv b hb price index primitive A hNo
  dsimp only
  exact ⟨hm,physical,pair,hRun,hSource,hMatches,hA,hB,hSec,hRich.trans hSmall,hPoor.trans hSmall⟩

end Blotto.GeneralPaperUnreplacedSourceContract
