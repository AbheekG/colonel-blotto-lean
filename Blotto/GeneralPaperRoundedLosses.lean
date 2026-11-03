import Blotto.GeneralPaperFourBlockRegret

/-! Arithmetic construction of the selected integer increments from the
separately rounded component probabilities. Counts represent mesh multiples
in [0,1], with theta=1/N. In particular signed tails are formed after rounding
each sign's interval mass. No battlefield weight enters these formulas.
The compressed CDF implementation must still produce the bounded counts
with the local error hypotheses below.
-/
namespace Blotto.GeneralPaperRoundedLosses
open GeneralPaperGeometricLevels
set_option autoImplicit false

def component (N count : ℕ) : ℚ := (count : ℚ)/N

def primalLoss (N lo hi pos neg : ℕ) : ℚ :=
  1-(component N lo+component N hi)/2+(component N pos-component N neg)

def responseLoss (N lo hi pos neg : ℕ) : ℚ :=
  -(component N lo+component N hi)/2+(component N pos-component N neg)

def signedLoss (N count : ℕ) (positive hit : Bool) : ℚ :=
  if positive then (if hit then 1 else 0)-component N count
  else component N count-(if hit then 1 else 0)

def primalIncrement (N lo hi pos neg : ℕ) : ℕ := 6*N+2*pos-(lo+hi+2*neg)

def responseIncrement (N lo hi pos neg : ℕ) : ℕ := 4*N+2*pos-(lo+hi+2*neg)

def signedIncrement (N count : ℕ) (positive hit : Bool) : ℕ :=
  if positive then 4*N+2*(if hit then N else 0)-2*count
  else 4*N+2*count-2*(if hit then N else 0)

theorem component_bounds (N count : ℕ) (hN : 0 < N) (hc : count ≤ N) :
    0 ≤ component N count ∧ component N count ≤ 1 := by
  unfold component
  have hn : (0:ℚ) < N := by exact_mod_cast hN
  exact ⟨div_nonneg (by positivity) hn.le, (div_le_one hn).mpr (by exact_mod_cast hc)⟩

theorem primal_magnitude (N lo hi pos neg : ℕ) (hN : 0 < N)
    (hl : lo ≤ N) (hh : hi ≤ N) (hp : pos ≤ N) (hn : neg ≤ N) :
    |primalLoss N lo hi pos neg| ≤ 2 := by
  have h1 := component_bounds N lo hN hl
  have h2 := component_bounds N hi hN hh
  have h3 := component_bounds N pos hN hp
  have h4 := component_bounds N neg hN hn
  unfold primalLoss
  apply abs_le.mpr
  constructor <;> linarith

theorem response_magnitude (N lo hi pos neg : ℕ) (hN : 0 < N)
    (hl : lo ≤ N) (hh : hi ≤ N) (hp : pos ≤ N) (hn : neg ≤ N) :
    |responseLoss N lo hi pos neg| ≤ 2 := by
  have h1 := component_bounds N lo hN hl
  have h2 := component_bounds N hi hN hh
  have h3 := component_bounds N pos hN hp
  have h4 := component_bounds N neg hN hn
  unfold responseLoss
  apply abs_le.mpr
  constructor <;> linarith

theorem signed_magnitude (N count : ℕ) (hN : 0 < N) (hc : count ≤ N) (positive hit : Bool) :
    |signedLoss N count positive hit| ≤ 1 := by
  have h := component_bounds N count hN hc
  cases positive <;> cases hit <;> simp only [signedLoss, Bool.false_eq_true, ↓reduceIte]
    <;> apply abs_le.mpr <;> constructor <;> linarith

theorem primal_increment_loss (N lo hi pos neg : ℕ) (hN : 0 < N)
    (hl : lo ≤ N) (hh : hi ≤ N) (hn : neg ≤ N) :
    executedLoss (1/(N:ℚ)) (primalIncrement N lo hi pos neg) = primalLoss N lo hi pos neg := by
  have hSub : lo+hi+2*neg ≤ 6*N+2*pos := by omega
  have hz : (N:ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  unfold executedLoss primalIncrement primalLoss component
  rw [Nat.cast_sub hSub]
  push_cast
  field_simp
  <;> ring

theorem response_increment_loss (N lo hi pos neg : ℕ) (hN : 0 < N)
    (hl : lo ≤ N) (hh : hi ≤ N) (hn : neg ≤ N) :
    executedLoss (1/(N:ℚ)) (responseIncrement N lo hi pos neg) = responseLoss N lo hi pos neg := by
  have hSub : lo+hi+2*neg ≤ 4*N+2*pos := by omega
  have hz : (N:ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  unfold executedLoss responseIncrement responseLoss component
  rw [Nat.cast_sub hSub]
  push_cast
  field_simp
  <;> ring

theorem signed_increment_loss (N count : ℕ) (hN : 0 < N) (hc : count ≤ N) (positive hit : Bool) :
    executedLoss (1/(N:ℚ)) (signedIncrement N count positive hit) = signedLoss N count positive hit := by
  have hz : (N:ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  cases positive <;> cases hit
    <;> simp only [signedIncrement, signedLoss, Bool.false_eq_true, ↓reduceIte]
    <;> unfold executedLoss component
    <;> rw [Nat.cast_sub (by omega)]
    <;> push_cast
    <;> field_simp
    <;> ring

theorem primal_increment_bound (N lo hi pos neg : ℕ) (hp : pos ≤ N) :
    primalIncrement N lo hi pos neg ≤ 8*N := by unfold primalIncrement; omega

theorem response_increment_bound (N lo hi pos neg : ℕ) (hp : pos ≤ N) :
    responseIncrement N lo hi pos neg ≤ 8*N := by unfold responseIncrement; omega

theorem signed_increment_bound (N count : ℕ) (hc : count ≤ N) (positive hit : Bool) :
    signedIncrement N count positive hit ≤ 8*N := by
  cases positive <;> cases hit <;> simp only [signedIncrement, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem half_tail_error (lo hi pos neg rlo rhi rpos rneg cdfError tailError : ℝ)
    (hl : |lo-rlo| ≤ cdfError) (hh : |hi-rhi| ≤ cdfError)
    (hp : |pos-rpos| ≤ tailError) (hn : |neg-rneg| ≤ tailError) :
    |(-(lo+hi)/2+(pos-neg))-(-(rlo+rhi)/2+(rpos-rneg))| ≤ cdfError+2*tailError := by
  have h1 := abs_le.mp hl
  have h2 := abs_le.mp hh
  have h3 := abs_le.mp hp
  have h4 := abs_le.mp hn
  apply abs_le.mpr
  constructor <;> linarith

theorem primal_error (N lo hi pos neg : ℕ) (trueLo trueHi truePos trueNeg nu theta : ℝ)
    (hl : |trueLo-(component N lo:ℝ)| ≤ 5*nu+theta)
    (hh : |trueHi-(component N hi:ℝ)| ≤ 5*nu+theta)
    (hp : |truePos-(component N pos:ℝ)| ≤ 10*nu+theta)
    (hn : |trueNeg-(component N neg:ℝ)| ≤ 10*nu+theta) :
    |(1-(trueLo+trueHi)/2+(truePos-trueNeg))-(primalLoss N lo hi pos neg:ℝ)| ≤ 25*nu+3*theta := by
  have h := half_tail_error _ _ _ _ _ _ _ _ _ _ hl hh hp hn
  unfold primalLoss
  push_cast
  convert h using 1
  · congr 1
    ring
  · ring

theorem response_error (N lo hi pos neg : ℕ) (trueLo trueHi truePos trueNeg nu theta : ℝ)
    (hl : |trueLo-(component N lo:ℝ)| ≤ 5*nu+theta)
    (hh : |trueHi-(component N hi:ℝ)| ≤ 5*nu+theta)
    (hp : |truePos-(component N pos:ℝ)| ≤ 10*nu+theta)
    (hn : |trueNeg-(component N neg:ℝ)| ≤ 10*nu+theta) :
    |(-(trueLo+trueHi)/2+(truePos-trueNeg))-(responseLoss N lo hi pos neg:ℝ)| ≤ 25*nu+3*theta := by
  have h := half_tail_error _ _ _ _ _ _ _ _ _ _ hl hh hp hn
  unfold responseLoss
  push_cast
  convert h using 1 <;> ring

theorem signed_error (N count : ℕ) (trueCDF nu theta : ℝ) (positive hit : Bool)
    (hNu : 0 ≤ nu) (hTheta : 0 ≤ theta)
    (h : |trueCDF-(component N count:ℝ)| ≤ 5*nu+theta) :
    |(if positive then (if hit then 1 else 0)-trueCDF else trueCDF-(if hit then 1 else 0))-
      (signedLoss N count positive hit:ℝ)| ≤ 25*nu+3*theta := by
  have he := abs_le.mp h
  cases positive <;> cases hit
    <;> simp only [signedLoss, Bool.false_eq_true, ↓reduceIte]
    <;> push_cast
    <;> apply abs_le.mpr <;> constructor <;> linarith

end Blotto.GeneralPaperRoundedLosses
