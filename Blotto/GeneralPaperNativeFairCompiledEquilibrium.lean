import Blotto.GeneralPaperFairSamplingControls

/-! Actual compiled original-coordinate strategies sampled by finitely
many fresh fair bits have the canonical continuous Nash guarantee. Row and
shift power identities are erased control postconditions; no sampler or
matching-law premise is supplied. Independent players use disjoint blocks. -/
namespace Blotto.GeneralPaperNativeFairCompiledEquilibrium
open GeneralPaperOriginalCirclePreparation GeneralPaperNativeSelectedSecurity
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem original {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv Wf Wg k R L : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A Ab : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hRows : (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.m k).lambda k).rows=2^R)
    (hShifts : count k=2^L) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
    let T := (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives), ∃ physical,
      (GeneralPaperRoundedNativePair.run valueBits model Wv Wf Wg k o.values redValues (fun _ => rfl) b).1=some physical ∧
      let μ := GeneralPaperNativeFairSamplerLaw.law primitive Ab R L T (count k) hRows hShifts model o hR 1
        (run price index A o hm physical.rich).1
      let ν := GeneralPaperNativeFairSamplerLaw.law primitive Ab R L T (count k) hRows hShifts model o hR b
        (run price index A o hm physical.poor).1
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
        security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
        regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧
        regret v.values (b:ℝ) ν μ≤179*(1/(2:ℝ)^k)/320 := by
  obtain ⟨hm,physical,hRun,hEquilibrium⟩ := GeneralPaperNativeCompiledEquilibrium.original bits valueBits model W Wv Wf Wg k
    input v hv b hb price index A hReplace
  dsimp only
  refine ⟨hm,physical,hRun,?_⟩
  simp only [GeneralPaperNativeFairSamplerLaw.data]
  exact hEquilibrium

end Blotto.GeneralPaperNativeFairCompiledEquilibrium
