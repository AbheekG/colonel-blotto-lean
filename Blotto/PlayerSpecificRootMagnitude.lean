import Blotto.PlayerSpecificRationalMagnitude
import Mathlib.Analysis.Polynomial.CauchyBound

/-! A dyadic root enclosure computed from the actual rational coefficient
encoding. This supplies the isolator's initial interval without a caller-
provided magnitude bound. Its precision/separation depth remains separate. -/
namespace Blotto.PlayerSpecificRootMagnitude
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificRationalMagnitude
open PlayerSpecificSquarefreeAlgorithm
set_option autoImplicit false
set_option maxHeartbeats 4000000

def rootBound (p : Data) : ℕ := 2^(2*inputHeight p+2)

theorem rootBound_pos (p : Data) : 0<rootBound p := Nat.two_pow_pos _

theorem rootBound_real (p : Data) :
    (rootBound p : ℝ)=4*((2:ℝ)^inputHeight p)^2 := by
  rw [rootBound,Nat.cast_pow,Nat.cast_ofNat]
  rw [show 2*inputHeight p+2=inputHeight p*2+2 by omega,pow_add,pow_mul]
  norm_num
  ring

theorem cauchy_bound (p : Data) (hp : semantics p≠0) :
    ((realPolynomial p).cauchyBound : ℝ)≤((2:ℝ)^inputHeight p)^2+1 := by
  let P := realPolynomial p
  let U : ℝ := (2:ℝ)^inputHeight p
  let T : NNReal := Finset.sup (Finset.range P.natDegree) (fun j => ‖P.coeff j‖₊)
  let D : NNReal := ‖P.leadingCoeff‖₊
  have hU : 0<U := pow_pos (by norm_num) _
  have hcoef (j : ℕ) : ‖P.coeff j‖₊≤(2:NNReal)^inputHeight p := by
    have h := real_upper ((semantics p).coeff j) (inputHeight p) (coefficient_height p j)
    rw [← real_coefficient] at h
    apply NNReal.coe_le_coe.mp
    simpa only [coe_nnnorm,Real.norm_eq_abs,NNReal.coe_pow,NNReal.coe_ofNat] using h.le
  have hT : T≤(2:NNReal)^inputHeight p := Finset.sup_le (fun j _ => hcoef j)
  have hTR : (T : ℝ)≤U := by
    simpa only [NNReal.coe_pow,NNReal.coe_ofNat,U] using (NNReal.coe_le_coe.mpr hT)
  have hn : trim p≠[] := fun h => hp ((trim_nil_iff p).mp h)
  have hlead := real_lower ((trim p).getLast?.getD 0) (inputHeight p) (leading_height p hp)
    ((trim_normalized p).resolve_left hn)
  rw [← real_leading p hp] at hlead
  have hD : (1:ℝ)/U<(D:ℝ) := by
    simpa only [D,P,coe_nnnorm,Real.norm_eq_abs,U] using hlead
  have hDpos : 0<(D:ℝ) := (div_pos (by norm_num) hU).trans hD
  have hprod := (div_lt_iff₀ hU).mp hD
  have hmul := mul_le_mul_of_nonneg_left hprod.le hU.le
  have hfrac : (T:ℝ)/(D:ℝ)≤U^2 := by
    apply (div_le_iff₀ hDpos).mpr
    nlinarith only [hTR,hmul]
  have he : (P.cauchyBound:ℝ)=(T:ℝ)/(D:ℝ)+1 := rfl
  change (P.cauchyBound:ℝ)≤U^2+1
  rw [he]
  linarith

theorem root_lt (p : Data) (hp : semantics p≠0) (x : ℝ) (hx : PlayerSpecificSturmVariations.realEvaluate p x=0) :
    |x|<(rootBound p : ℝ) := by
  have hroot : (realPolynomial p).IsRoot x := by rw [Polynomial.IsRoot,real_evaluate]; exact hx
  have hnorm := Polynomial.IsRoot.norm_lt_cauchyBound (real_nonzero p hp) hroot
  have hreal : (‖x‖₊:ℝ)<((realPolynomial p).cauchyBound:ℝ) := hnorm
  have habs : |x|<((realPolynomial p).cauchyBound:ℝ) := by
    simpa only [coe_nnnorm,Real.norm_eq_abs] using hreal
  have hu : (1:ℝ)≤(2:ℝ)^inputHeight p := one_le_pow₀ (by norm_num)
  have hs : (1:ℝ)≤((2:ℝ)^inputHeight p)^2 := one_le_pow₀ hu
  have hc := cauchy_bound p hp
  rw [rootBound_real]
  nlinarith only [habs,hc,hs]

def initial (p : Data) (prepared : PlayerSpecificIsolationState.Prepared p) : PlayerSpecificIsolationState.Interval :=
  PlayerSpecificIsolationState.initial prepared (-(rootBound p : ℚ)) (rootBound p : ℚ)

theorem initial_valid (p : Data) (prepared : PlayerSpecificIsolationState.Prepared p) :
    PlayerSpecificIsolationState.Valid prepared (initial p prepared) := by
  apply PlayerSpecificIsolationState.initial_valid
  have h : (0:ℚ)<(rootBound p : ℚ) := by exact_mod_cast rootBound_pos p
  linarith

theorem initial_covers (p : Data) (hp : semantics p≠0) (prepared : PlayerSpecificIsolationState.Prepared p)
    (x : ℝ) (hx : PlayerSpecificSturmVariations.realEvaluate p x=0) : (initial p prepared).Contains x := by
  have h := abs_lt.mp (root_lt p hp x hx)
  change ((-(rootBound p : ℚ) : ℚ) : ℝ)<x ∧ x≤((rootBound p : ℚ) : ℝ)
  push_cast
  exact ⟨h.1,h.2.le⟩

end Blotto.PlayerSpecificRootMagnitude
