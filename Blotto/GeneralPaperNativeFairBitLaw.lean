import Blotto.GeneralPaperNativeFairBitPrice

/-! The complete bit-priced draw retains the exact fair-input law and
whole-player independence. Its output/read contracts are the same actual
finite-bit contracts, not a different randomized algorithm. -/
namespace Blotto.GeneralPaperNativeFairBitLaw
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def law {n : ℕ} (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)) : Mixed n :=
  (fairBitLaw (R+L)).map (fun fresh j => ((GeneralPaperNativeFairBitDraw.run A R L T S hT hS model o hR c prepared fresh).output.read j:ℝ))

theorem prior_data {n : ℕ} (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)) :
    law A R L T S hT hS model o hR c prepared=
      GeneralPaperNativeFairSamplerLaw.law model.rat A R L T S hT hS model o hR c prepared := by
  simp only [law,GeneralPaperNativeFairBitDraw.data,GeneralPaperNativeFairSamplerLaw.law]

theorem data {n : ℕ} (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)) :
    law A R L T S hT hS model o hR c prepared=
      GeneralPaperOriginalDrawLaw.law (hT ▸ Nat.two_pow_pos R) (hS ▸ Nat.two_pow_pos L) model o hR c prepared :=
  (prior_data A R L T S hT hS model o hR c prepared).trans
    (GeneralPaperNativeFairSamplerLaw.data model.rat A R L T S hT hS model o hR c prepared)

theorem independent_players {n : ℕ} (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c d : ℚ)
    (rich poor : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)) :
    Measure.map (fun fresh =>
      ((fun j => ((GeneralPaperNativeFairBitDraw.run A R L T S hT hS model o hR c rich
          (firstBitBlock (R+L) (R+L) fresh)).output.read j:ℝ)),
        (fun j => ((GeneralPaperNativeFairBitDraw.run A R L T S hT hS model o hR d poor
          (secondBitBlock (R+L) (R+L) fresh)).output.read j:ℝ))))
      (fairBitLaw ((R+L)+(R+L)) : Measure (Fin ((R+L)+(R+L)) → Bool))=
      (law A R L T S hT hS model o hR c rich : Measure (Allocation n)).prod
        (law A R L T S hT hS model o hR d poor : Measure (Allocation n)) := by
  simp only [GeneralPaperNativeFairBitDraw.data,prior_data]
  exact GeneralPaperNativeFairSamplerLaw.independent_players model.rat A R L T S hT hS model o hR c d rich poor

theorem every_output {n : ℕ} (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n) (hR : 0<o.representatives) (c : ℚ)
    (prepared : FixedArrayTable T (GeneralPaperNamedCircleExecution.Prepared o.classified o.representatives)) (B : ℝ)
    (h : Supported B (law A R L T S hT hS model o hR c prepared)) :
    ∀ fresh,Feasible B (fun j => ((GeneralPaperNativeFairBitDraw.run A R L T S hT hS model o hR c prepared fresh).output.read j:ℝ)) :=
  GeneralPaperNativeFairEveryOutput.all (R+L) _ B h

theorem height {n K : ℕ} (price index : ℕ → ℕ) (Ap A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives)
    (columns : FixedArrayTable o.m (GeneralPaperQuantizedColumn.Column T K)) (hR : 0<o.representatives) (c : ℚ)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping o.classified))
    (C H : ℕ) (hc : RationalHeight c C) (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (fresh : Fin (R+L) → Bool) (j : Fin n) :
    RationalHeight ((GeneralPaperNativeFairBitDraw.run A R L T S hT hS model o hR c
      (GeneralPaperOriginalCirclePreparation.run price index Ap o hm columns).1 fresh).output.read j)
      (C+(binaryWordWidth o.representatives+2*binaryWordWidth o.classified.lightWeight+H)) := by
  rw [GeneralPaperNativeFairBitDraw.data]
  exact GeneralPaperNativeFairEveryOutput.height price index model.rat Ap A R L T S hT hS model o hm columns hR c
    hConserved hBijective C H hc hColumns fresh j

end Blotto.GeneralPaperNativeFairBitLaw
