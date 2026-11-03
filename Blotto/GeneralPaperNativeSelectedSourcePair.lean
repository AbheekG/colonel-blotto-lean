import Blotto.GeneralPaperNativeSelectedSecurity

/-! Original continuous-game equilibrium for the selected source pair and
the paper's finite midpoint-cell shifts. This is the selected-law semantic
join; native evaluator/cost/description/sampling and boundaries remain open. -/
namespace Blotto.GeneralPaperNativeSelectedSourcePair
open GeneralPaperNativeSelectedSecurity GeneralPaperDictionary
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem original {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives), ∃ pair,
      GeneralPaperRoundedValueCanonical.run valueBits model Wv k o.values redValues (fun _ => rfl) b=some pair ∧
      let μ := lifted bits model W k input v hv hReplace hm (count k) (count_positive k) hT (law pair.rich hT).realRow
      let ν := lifted bits model W k input v hv hReplace hm (count k) (count_positive k) hT
        (fun r => scaleAllocation b ((law pair.poor hT).realRow r))
      Supported 1 μ ∧ Supported b ν ∧
        security v.values 1 ν+security v.values b μ<1+179*(1/(2:ℝ)^k)/320 ∧
        regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧
        regret v.values b ν μ≤179*(1/(2:ℝ)^k)/320 := by
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  obtain ⟨hm,pair,hRun,hFullA,hFullB,hFullSec,_,_⟩ :=
    GeneralPaperNativeCircleSourcePair.original bits valueBits model W Wv k input v hv b hb hReplace
  dsimp only
  refine ⟨hm,pair,hRun,?_⟩
  let μ := lifted bits model W k input v hv hReplace hm (count k) (count_positive k) hT (law pair.rich hT).realRow
  let ν := lifted bits model W k input v hv hReplace hm (count k) (count_positive k) hT
    (fun r => scaleAllocation b ((law pair.poor hT).realRow r))
  have hA : Supported 1 μ := by
    exact supported_of_full bits model W k input v hv hReplace hm (count k) (count_positive k) hT _ 1 hFullA
  have hB : Supported b ν := by
    exact supported_of_full bits model W k input v hv hReplace hm (count k) (count_positive k) hT _ b hFullB
  have hSA := security_bound bits model W k input v hv hReplace hm (count k) (count_positive k) hT
    (law pair.rich hT).realRow v.values b hb.1.le
  have hSB := security_bound bits model W k input v hv hReplace hm (count k) (count_positive k) hT
    (fun r => scaleAllocation b ((law pair.poor hT).realRow r)) v.values 1 (by norm_num)
  have hError := twice_inverse k
  have hTotal : security v.values 1 ν+security v.values b μ<1+179*(1/(2:ℝ)^k)/320 := by
    linarith only [hFullSec,hSA,hSB,hError]
  have hRegret := regrets_le_of_security_sum v.values μ ν hA hB hTotal.le
  exact ⟨hA,hB,hTotal,hRegret⟩

end Blotto.GeneralPaperNativeSelectedSourcePair
