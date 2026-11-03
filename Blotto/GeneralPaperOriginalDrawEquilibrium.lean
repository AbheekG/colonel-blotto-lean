import Blotto.GeneralPaperOriginalDrawScale

/-! Native output-law equilibrium for physical columns matching the actual
selected source/compiler pair. Matching is an erased driver postcondition;
the full native pair driver must still establish it from returned arrays.
The conclusion covers canonical continuous deviations and hard budgets. -/
namespace Blotto.GeneralPaperOriginalDrawEquilibrium
open GeneralPaperOriginalCirclePreparation GeneralPaperNativeSelectedSecurity
set_option autoImplicit false
set_option maxHeartbeats 3200000

structure Columns (T m K : ℕ) where
  rich : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)
  poor : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)

def Matches {T m K : ℕ} (physical : Columns T m K) (pair : GeneralPaperSourcePairRun.Pair T m K) : Prop :=
  GeneralPaperRowQuantizer.dictionary physical.rich=pair.rich ∧ GeneralPaperRowQuantizer.dictionary physical.poor=pair.poor

theorem original {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives), ∃ pair,
      GeneralPaperRoundedValueCanonical.run valueBits model Wv k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧
      ∀ physical : Columns (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
          o.m (GeneralPaperProxyParameters.prepare o.m k).K,Matches physical pair →
        let μ := GeneralPaperOriginalDrawLaw.law hT (count_positive k) model o hR 1 (run price index A o hm physical.rich).1
        let ν := GeneralPaperOriginalDrawLaw.law hT (count_positive k) model o hR b (run price index A o hm physical.poor).1
        Supported 1 μ ∧ Supported (b:ℝ) ν ∧
          security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
          regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧
          regret v.values (b:ℝ) ν μ≤179*(1/(2:ℝ)^k)/320 := by
  have hbReal : (0:ℝ)<b ∧ (b:ℝ)<1 := by exact_mod_cast hb
  obtain ⟨hm,pair,hRun,hA,hB,hSecurity,hRich,hPoor⟩ :=
    GeneralPaperNativeSelectedSourcePair.original bits valueBits model W Wv k input v hv (b:ℝ) hbReal hReplace
  dsimp only
  refine ⟨hm,pair,hRun,?_⟩
  intro physical hMatch
  have hRichLaw := GeneralPaperOriginalDrawScale.native_one bits model W k input v hv hReplace hm physical.rich
    (GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.m k).lambda k)
    (count_positive k) price index A
  have hPoorLaw := GeneralPaperOriginalDrawScale.native_scaled bits model W k input v hv hReplace hm physical.poor
    (GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.m k).lambda k)
    (count_positive k) price index A b hb.1
  rw [hMatch.1] at hRichLaw
  rw [hMatch.2] at hPoorLaw
  rw [hRichLaw,hPoorLaw]
  exact ⟨hA,hB,hSecurity,hRich,hPoor⟩

end Blotto.GeneralPaperOriginalDrawEquilibrium
