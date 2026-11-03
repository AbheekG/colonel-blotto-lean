import Blotto.GeneralPaperFinalStaticCheck

/-! The executed static checker is equivalent to ALL original static
inequalities, including zero/repeated anchors and non-strict boundaries.
-/
namespace Blotto.GeneralPaperFinalStaticCheckSound
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStaticRayRows
open GeneralPaperFinalStaticCheck
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem row_iff {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ)
    (beta : ℝ) (i : StaticIndex T m K) :
    (GeneralPaperStaticRayScan.evaluate labels x (fun _ => 0) i).1.intercept≤0 ↔
      (row labels i).Holds beta (fun a => (x a:ℝ)) := by
  have hh := GeneralPaperStaticRaySound.residual_cast labels beta x (fun _ => 0) 0 i
  simp only [GeneralPaperRayAffine.Affine.value,mul_zero,add_zero,Rat.cast_zero] at hh
  constructor
  · intro h
    have hr : ((GeneralPaperStaticRayScan.evaluate labels x (fun _ => 0) i).1.intercept:ℝ)≤0 := by exact_mod_cast h
    rw [hh] at hr
    exact sub_nonpos.mp hr
  · intro h
    have hr : ((GeneralPaperStaticRayScan.evaluate labels x (fun _ => 0) i).1.intercept:ℝ)≤0 := by
      rw [hh]
      exact sub_nonpos.mpr h
    exact_mod_cast hr

theorem correct {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ) (beta : ℝ) :
    (run labels x).accepted=true ↔ ∀ i : StaticIndex T m K,(row labels i).Holds beta (fun a => (x a:ℝ)) := by
  change (loop labels x (enumerate T m K) true 0).accepted=true ↔ _
  rw [loop_accepted]
  constructor
  · intro h i
    exact (row_iff labels x beta i).mp (h.2 i (enumerate_mem i))
  · intro h
    exact ⟨rfl,fun i _ => (row_iff labels x beta i).mpr (h i)⟩

theorem work {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K) (x : Variable m K → ℚ) :
    (run labels x).work≤512*(m*(K-1)+m*T+m+1) := by
  have hSum : ((enumerate T m K).map (fun i => (GeneralPaperStaticRayScan.evaluate labels x (fun _ => 0) i).2+8)).sum≤
      ((enumerate T m K).map GeneralPaperStaticRayScan.charge).sum := by
    apply List.sum_le_sum
    intro i _
    have hh := GeneralPaperStaticRayScan.evaluate_charge labels x (fun _ => 0) i
    omega
  rw [GeneralPaperStaticRayScan.charge_sum] at hSum
  change (loop labels x (enumerate T m K) true 0).work+64*(m+m*(K-1)+T+1)≤_
  rw [loop_work]
  have hT : T≤m*T := by nlinarith only [show 1≤m by omega]
  nlinarith only [hSum,hT]

end Blotto.GeneralPaperFinalStaticCheckSound
