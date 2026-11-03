import Blotto.GeneralPaperSelectedCircleLaw

/-! Selected midpoint-cell laws in the actual native reduction's original
named coordinates. Their continuous security differs from the full-cell
lift by at most 1/S. Native shift arithmetic/sort/sweep prices remain open. -/
namespace Blotto.GeneralPaperNativeSelectedSecurity
open GeneralPaperNativeReductionShape GeneralPaperNativeCircleLoss
open GeneralPaperFieldRelabel GeneralPaperLightFieldIndexEquiv
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def count (k : ℕ) : ℕ := 64*2^k

theorem count_positive (k : ℕ) : 0<count k := by unfold count;positivity

theorem count_power (k : ℕ) : count k=2^(k+6) := by
  rw [count,pow_add]
  norm_num only [Nat.reducePow]
  omega

theorem twice_inverse (k : ℕ) : 2*(1/(count k:ℝ))=(1/(2:ℝ)^k)/32 := by
  unfold count
  push_cast
  ring

noncomputable def lifted {n T : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (S : ℕ) (hS : 0<S) (hT : 0<T)
    (rows : Fin T → Allocation (GeneralPaperOriginalValueReduction.run bits model W k input).1.m) : Mixed n :=
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  let hR := original_representatives_positive bits model W k input
  let hG := original_light_positive bits model W k input hReplace
  let hL := GeneralPaperCircleActualWeights.original_total_positive bits model W k input v hv hG
  law (originalEquiv bits model W k input).symm
    (GeneralPaperSelectedCircleLaw.law o.representatives o.classified.lightWeight S hR hL hS hT
      (GeneralPaperCircleActualWeights.weights o) (fun r => allocation (finCongr hm.symm) (rows r)))

theorem security_bound {n T : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (S : ℕ) (hS : 0<S) (hT : 0<T)
    (rows : Fin T → Allocation (GeneralPaperOriginalValueReduction.run bits model W k input).1.m)
    (w : Values n) (B : ℝ) (hB : 0≤B) :
    security w B (lifted bits model W k input v hv hReplace hm S hS hT rows)≤
      security w B (GeneralPaperNativeCircleSecurity.lifted bits model W k input v hv hReplace hm hT rows)+1/(S:ℝ) := by
  unfold lifted GeneralPaperNativeCircleSecurity.lifted
  dsimp only
  rw [restored_security,restored_security]
  exact GeneralPaperSelectedCircleLaw.security_bound _ _ S _ _ hS hT _
    (GeneralPaperCircleActualWeights.original_sum bits model W k input) _ _ B hB

theorem supported {n T : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (S : ℕ) (hS : 0<S) (hT : 0<T)
    (rows : Fin T → Allocation (GeneralPaperOriginalValueReduction.run bits model W k input).1.m)
    (B : ℝ) (h : Supported B (GeneralPaperUniformRowLaw.law hT rows)) :
    Supported B (lifted bits model W k input v hv hReplace hm S hS hT rows) := by
  apply GeneralPaperFieldRelabel.supported
  apply GeneralPaperSelectedCircleLaw.supported
  · exact GeneralPaperCircleActualWeights.original_sum bits model W k input
  · intro r
    exact (feasible_iff (finCongr hm.symm) B (rows r)).mpr
      (GeneralPaperUniformRowSupport.rows_feasible hT rows B h r)

theorem supported_of_full {n T : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (S : ℕ) (hS : 0<S) (hT : 0<T)
    (rows : Fin T → Allocation (GeneralPaperOriginalValueReduction.run bits model W k input).1.m)
    (B : ℝ) (h : Supported B (GeneralPaperNativeCircleSecurity.lifted bits model W k input v hv hReplace hm hT rows)) :
    Supported B (lifted bits model W k input v hv hReplace hm S hS hT rows) := by
  have he := GeneralPaperFieldRelabel.supported (originalEquiv bits model W k input) _ B h
  unfold GeneralPaperNativeCircleSecurity.lifted at he
  dsimp only at he
  rw [law_inverse] at he
  apply GeneralPaperFieldRelabel.supported
  exact GeneralPaperSelectedCircleLaw.supported_of_full _ _ S _ _ hS hT _ _ B he

end Blotto.GeneralPaperNativeSelectedSecurity
