import Blotto.GeneralPaperRoundedNativePair

/-! The actual returned physical source/compiler pair supplies the native
original-field evaluator's canonical continuous Nash guarantee. No Matches
premise is supplied. The original value-replacement regime is explicit;
identity/boundary/fair-bit and complete resource joins remain separate. -/
namespace Blotto.GeneralPaperNativeCompiledEquilibrium
open GeneralPaperOriginalCirclePreparation GeneralPaperNativeSelectedSecurity
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem original {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv Wf Wg k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives), ∃ physical,
      (GeneralPaperRoundedNativePair.run valueBits model Wv Wf Wg k o.values redValues (fun _ => rfl) b).1=some physical ∧
      let μ := GeneralPaperOriginalDrawLaw.law hT (count_positive k) model o hR 1 (run price index A o hm physical.rich).1
      let ν := GeneralPaperOriginalDrawLaw.law hT (count_positive k) model o hR b (run price index A o hm physical.poor).1
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
        security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
        regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧
        regret v.values (b:ℝ) ν μ≤179*(1/(2:ℝ)^k)/320 := by
  obtain ⟨hm,pair,hPair,hEquilibrium⟩ := GeneralPaperOriginalDrawEquilibrium.original bits valueBits model W Wv k input v hv b hb price index A hReplace
  dsimp only
  obtain ⟨physical,hRun,hMatch⟩ := GeneralPaperRoundedNativePair.return_of_canonical valueBits model Wv Wf Wg k
    (GeneralPaperOriginalValueReduction.run bits model W k input).1.values
    (GeneralPaperOriginalValueReduction.selector bits model W k input v hv) (fun _ => rfl) b hb pair hPair
  exact ⟨hm,physical,hRun,hEquilibrium physical hMatch⟩

end Blotto.GeneralPaperNativeCompiledEquilibrium
