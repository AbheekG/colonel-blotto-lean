import Blotto.GeneralPaperCheckedSourceEquilibrium
import Blotto.RationalUnitLatticeHeight

/-! The ACTUAL modified ratio endpoint has short reduced numerator and
denominator, whether supplied by a small root or a grid endpoint. Its
reciprocal denominator is bounded by the same cap; no runtime reciprocal
at zero is introduced by these proof observers.
-/
namespace Blotto.GeneralPaperEndpointRatioSize
open GeneralPaperProxyParameters GeneralPaperProxyBranchSpec
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem denominator (m k : ℕ) (b : ℝ)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) :
    (GeneralPaperProxyClassifier.classify m k b).choice.endpoint.den≤(prepare m k).qbar := by
  have hH := H_positive m k
  have hg := grid_lower m k
  have hCap : (prepare m k).H≤(prepare m k).qbar := by
    rw [(data m k).2.2.2.2.2.2]
    nlinarith
  have hGrid : (prepare m k).Qg≤(prepare m k).qbar := by
    rw [(data m k).2.2.2.2.2.2]
    omega
  change (GeneralPaperProxySelection.select (prepare m k).Qg (GeneralPaperProxyClassifier.classify m k b).cell
    (grid_positive m k) b (GeneralPaperProxyClassifier.classify m k b).root).endpoint.den≤(prepare m k).qbar
  rcases select_spec (prepare m k).Qg (GeneralPaperProxyClassifier.classify m k b).cell
      (grid_positive m k) b (GeneralPaperProxyClassifier.classify m k b).root with hu|hr|hp|her|hep
  · exact (hModify hu.1).elim
  · obtain ⟨f,hf,_,_,_,_,he⟩ := hr
    rw [he]
    exact (Farey.value_den_le f).trans ((GeneralPaperProxyClassifier.root_sound m k b f hf).1.trans hCap)
  · obtain ⟨f,hf,_,_,_,he⟩ := hp
    rw [he]
    exact (Farey.value_den_le f).trans ((GeneralPaperProxyClassifier.root_sound m k b f hf).1.trans hCap)
  · rw [her.2.2.2.2]
    simpa only [GeneralPaperBucketGeometry.upper,Int.cast_add,Int.cast_natCast,Int.cast_one] using
      ((reduced_fraction_bounds ((GeneralPaperProxyClassifier.classify m k b).cell+1:ℤ)
        (prepare m k).Qg (grid_positive m k)).2).trans hGrid
  · rw [hep.2.2.2.2]
    exact ((reduced_fraction_bounds ((GeneralPaperProxyClassifier.classify m k b).cell:ℤ)
      (prepare m k).Qg (grid_positive m k)).2).trans hGrid

theorem numerator (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) :
    (GeneralPaperProxyClassifier.classify m k b).choice.endpoint.num.natAbs≤(prepare m k).qbar := by
  let t := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  have hu := GeneralPaperProxyEndpointBounds.endpoint_unit m k b hb hModify
  have ha : |t|≤(1:ℚ) := by rw [abs_of_nonneg hu.1]; exact hu.2
  have hn := rationalLattice_abs_numerator_le (M:=1) t.den_pos (show OnRationalLattice t.den t from dvd_refl _) ha
  simp only [one_mul] at hn
  exact hn.trans (denominator m k b hModify)

theorem height (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) :
    RationalHeight (GeneralPaperProxyClassifier.classify m k b).choice.endpoint (binaryWordWidth (prepare m k).qbar) :=
  ⟨(numerator m k b hb hModify).trans_lt (lt_pow_binaryWordWidth _),
    (denominator m k b hModify).trans_lt (lt_pow_binaryWordWidth _)⟩

theorem threshold_denominator (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) (reciprocal : Bool) :
    (if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
      else (GeneralPaperProxyClassifier.classify m k b).choice.endpoint : ℚ).den≤(prepare m k).qbar := by
  cases reciprocal
  · exact denominator m k b hModify
  · simp only [ite_true,one_div]
    by_cases ht : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0
    · simp only [ht,inv_zero,Rat.den_zero]
      exact cap_positive m k
    · rw [Rat.den_inv_of_ne_zero ht]
      exact numerator m k b hb hModify

end Blotto.GeneralPaperEndpointRatioSize
