import Blotto.GeneralPaperNativeFairBitLaw

/-! The actual returned compiler pair, complete operand-priced bit draw
and independent fair inputs preserve canonical continuous Nash security.
Every finite input vector has a hard budget. Full paper-rate/global-space,
accuracy/identity/boundary/final-interface joins remain separate. -/
namespace Blotto.GeneralPaperNativeFairBitEquilibrium
open GeneralPaperOriginalCirclePreparation GeneralPaperNativeSelectedSecurity
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem original {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv Wf Wg k R L : ℕ)
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
      (GeneralPaperRoundedNativePair.run valueBits model Wv Wf Wg k o.values redValues (fun _ => rfl) b).1=some physical ∧
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
  obtain ⟨hm,physical,hRun,hEquilibrium⟩ := GeneralPaperNativeCompiledEquilibrium.original bits valueBits model W Wv Wf Wg k
    input v hv b hb price index Ap hReplace
  dsimp only
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  let hR := GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input
  let pr := (run price index Ap o hm physical.rich).1
  let pp := (run price index Ap o hm physical.poor).1
  let T := (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
  have hRich : Supported 1 (GeneralPaperNativeFairBitLaw.law A R L T (count k) hRows hShifts model o hR 1 pr) := by
    rw [GeneralPaperNativeFairBitLaw.data]
    exact hEquilibrium.1
  have hPoor : Supported (b:ℝ) (GeneralPaperNativeFairBitLaw.law A R L T (count k) hRows hShifts model o hR b pp) := by
    rw [GeneralPaperNativeFairBitLaw.data]
    exact hEquilibrium.2.1
  refine ⟨hm,physical,hRun,hRich,hPoor,?_,?_,?_⟩
  · exact GeneralPaperNativeFairBitLaw.every_output A R L T (count k) hRows hShifts model o hR 1 pr 1 hRich
  · exact GeneralPaperNativeFairBitLaw.every_output A R L T (count k) hRows hShifts model o hR b pp (b:ℝ) hPoor
  · simp only [GeneralPaperNativeFairBitLaw.data]
    exact hEquilibrium.2.2

end Blotto.GeneralPaperNativeFairBitEquilibrium
