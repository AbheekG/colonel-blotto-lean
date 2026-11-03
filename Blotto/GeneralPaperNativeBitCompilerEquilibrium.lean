import Blotto.GeneralPaperRoundedBitNativePair
import Blotto.GeneralPaperNativeFairBitEquilibrium

/-! The actual full bit source/compiler entry point feeds the complete
bit-priced fresh sampler. Physical-array equality preserves every finite
output budget and both canonical continuous regrets in the replacement
regime. Paper phase/rate/global-space and remaining branches stay separate. -/
namespace Blotto.GeneralPaperNativeBitCompilerEquilibrium
open GeneralPaperOriginalCirclePreparation GeneralPaperNativeSelectedSecurity
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

theorem original {n : ℕ} (bits : Bool) (model : RationalCostModel) (W Wc Wv Wf Wg k R L : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index : ℕ → ℕ) (Ap A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hRows : (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.m k).lambda k).rows=2^R)
    (hShifts : count k=2^L) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
    let T := (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives), ∃ physical,
      (GeneralPaperRoundedBitNativePair.run model Wc Wv Wf Wg k o.values redValues (fun _ => rfl) b).1=some physical ∧
      let pr := (run price index Ap o hm physical.rich).1
      let pp := (run price index Ap o hm physical.poor).1
      let μ := GeneralPaperNativeFairBitLaw.law A R L T (count k) hRows hShifts model o hR 1 pr
      let ν := GeneralPaperNativeFairBitLaw.law A R L T (count k) hRows hShifts model o hR b pp
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧
        (∀ fresh,Feasible 1 (fun j => ((GeneralPaperNativeFairBitDraw.run A R L T (count k) hRows hShifts model o hR 1 pr fresh).output.read j:ℝ))) ∧
        (∀ fresh,Feasible (b:ℝ) (fun j => ((GeneralPaperNativeFairBitDraw.run A R L T (count k) hRows hShifts model o hR b pp fresh).output.read j:ℝ))) ∧
        security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
        regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧
        regret v.values (b:ℝ) ν μ≤179*(1/(2:ℝ)^k)/320 := by
  obtain ⟨hm,physical,hRun,hEquilibrium⟩ := GeneralPaperNativeFairBitEquilibrium.original bits true model W Wv Wf Wg k R L
    input v hv b hb price index Ap A hReplace hRows hShifts
  dsimp only
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
  refine ⟨hm,physical,?_,hEquilibrium⟩
  exact (GeneralPaperRoundedBitNativePair.data model Wc Wv Wf Wg k o.values redValues (fun _ => rfl) b hb).trans hRun

end Blotto.GeneralPaperNativeBitCompilerEquilibrium
