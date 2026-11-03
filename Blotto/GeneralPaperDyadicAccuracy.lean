import Blotto.GeneralPaperTrajectoryParameters

/-! The actual dyadic accuracy choice from the rational input. Only the
guard, doubling and final inversion are evaluated. Natural ceiling is an
erased termination/rank proof, never an executable input-encoding query.
-/
namespace Blotto.GeneralPaperDyadicAccuracy
set_option autoImplicit false
set_option maxHeartbeats 1500000

def loop (target : ℚ) (p : ℕ) (hp : 0<p) : GeneralPaperPowerCeiling.Result :=
  if target≤(p:ℚ) then ⟨p,0,2⟩ else
    let later := loop target (2*p) (by omega)
    ⟨later.power,later.doublings+1,later.work+12⟩
termination_by ⌈target⌉₊-p
decreasing_by
  have hc : p<⌈target⌉₊ := Nat.lt_ceil.mpr (lt_of_not_ge (by assumption))
  omega

theorem loop_spec (target : ℚ) (p : ℕ) (hp : 0<p) :
    (loop target p hp).power=p*2^(loop target p hp).doublings ∧
    target≤((loop target p hp).power:ℚ) ∧
    ((loop target p hp).doublings=0 → (loop target p hp).power=p) ∧
    (0<(loop target p hp).doublings → ((loop target p hp).power:ℚ)<2*target) ∧
    (loop target p hp).work=12*(loop target p hp).doublings+2 := by
  generalize hr : loop target p hp=result
  rw [loop] at hr
  split at hr
  · rename_i hStop
    subst result
    dsimp only
    exact ⟨by simp,hStop,by intro; rfl,by omega,by omega⟩
  · rename_i hContinue
    have ih := loop_spec target (2*p) (by omega)
    subst result
    dsimp only
    refine ⟨?_,ih.2.1,?_,?_,?_⟩
    · rw [ih.1,pow_succ]; ring
    · omega
    · intro _
      by_cases hz : (loop target (2*p) (by omega)).doublings=0
      · have hPower := ih.2.2.1 hz
        rw [hPower,Nat.cast_mul,Nat.cast_ofNat]
        linarith only [lt_of_not_ge hContinue]
      · exact ih.2.2.2.1 (by omega)
    · rw [ih.2.2.2.2]; omega
termination_by ⌈target⌉₊-p
decreasing_by
  have hc : p<⌈target⌉₊ := Nat.lt_ceil.mpr (lt_of_not_ge (by assumption))
  omega

theorem loop_minimal (target : ℚ) (p : ℕ) (hp : 0<p) (j : ℕ) (hTarget : target≤((p*2^j:ℕ):ℚ)) :
    (loop target p hp).doublings≤j := by
  rw [loop]
  split
  · exact Nat.zero_le _
  · rename_i hContinue
    have hj : j≠0 := by
      intro hz
      subst j
      simp only [pow_zero,Nat.mul_one] at hTarget
      exact hContinue hTarget
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have ht : target≤(((2*p)*2^k:ℕ):ℚ) := by
      simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hTarget
    have ih := loop_minimal target (2*p) (by omega) k ht
    change (loop target (2*p) (by omega)).doublings+1≤k+1
    omega
termination_by ⌈target⌉₊-p
decreasing_by
  have hc : p<⌈target⌉₊ := Nat.lt_ceil.mpr (lt_of_not_ge (by assumption))
  omega

theorem loop_depth (target : ℚ) (p : ℕ) (hp : 0<p) :
    (loop target p hp).doublings≤binaryWordWidth ⌈target⌉₊ := by
  have hn : ⌈target⌉₊≤p*2^binaryWordWidth ⌈target⌉₊ :=
    (lt_pow_binaryWordWidth ⌈target⌉₊).le.trans
      (by have h := Nat.mul_le_mul_right (2^binaryWordWidth ⌈target⌉₊) (show 1≤p by omega); simpa only [Nat.one_mul] using h)
  apply loop_minimal
  exact (Nat.le_ceil target).trans (by exact_mod_cast hn)

structure Parameters where
  exponent : ℕ
  accuracy : ℚ
  work : ℕ

def prepare (epsilon : ℚ) : Parameters :=
  let result := loop epsilon⁻¹ 1 (by decide)
  ⟨result.doublings,1/(result.power:ℚ),result.work+8⟩

theorem accuracy_power (epsilon : ℚ) : (prepare epsilon).accuracy=1/(2:ℚ)^(prepare epsilon).exponent := by
  have hp := (loop_spec epsilon⁻¹ 1 (by decide)).1
  simp only [Nat.one_mul] at hp
  change 1/((loop epsilon⁻¹ 1 (by decide)).power:ℚ)=_
  rw [hp,Nat.cast_pow,Nat.cast_ofNat]
  rfl

theorem exponent_positive (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) : 0<(prepare epsilon).exponent := by
  have hs := loop_spec epsilon⁻¹ 1 (by decide)
  change 0<(loop epsilon⁻¹ 1 (by decide)).doublings
  by_contra hn
  have hz : (loop epsilon⁻¹ 1 (by decide)).doublings=0 := by omega
  have hp := hs.2.2.1 hz
  have hl := hs.2.1
  rw [hp,Nat.cast_one] at hl
  have hi := mul_inv_cancel₀ (ne_of_gt hE)
  nlinarith only [hE,hOne,hl,hi]

theorem accuracy_bounds (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) :
    epsilon/2<(prepare epsilon).accuracy ∧ (prepare epsilon).accuracy≤epsilon := by
  have hs := loop_spec epsilon⁻¹ 1 (by decide)
  have hPos : 0<(loop epsilon⁻¹ 1 (by decide)).doublings := exponent_positive epsilon hE hOne
  have hpNat : 0<(loop epsilon⁻¹ 1 (by decide)).power := by
    rw [hs.1]
    positivity
  have hp : (0:ℚ)<(loop epsilon⁻¹ 1 (by decide)).power := by exact_mod_cast hpNat
  have hUpper := hs.2.2.2.1 hPos
  have hScaled := mul_lt_mul_of_pos_left hUpper hE
  have hEq : epsilon*(2*epsilon⁻¹)=2 := by
    rw [mul_left_comm,mul_inv_cancel₀ (ne_of_gt hE),mul_one]
  rw [hEq] at hScaled
  have hLower := mul_le_mul_of_nonneg_left hs.2.1 hE.le
  rw [mul_inv_cancel₀ (ne_of_gt hE)] at hLower
  change epsilon/2<1/((loop epsilon⁻¹ 1 (by decide)).power:ℚ) ∧ 1/((loop epsilon⁻¹ 1 (by decide)).power:ℚ)≤epsilon
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith only [hScaled]
  · exact (div_le_iff₀ hp).mpr hLower

theorem prepare_work (epsilon : ℚ) :
    (prepare epsilon).work≤12*binaryWordWidth ⌈epsilon⁻¹⌉₊+10 := by
  have hd := loop_depth epsilon⁻¹ 1 (by decide)
  have hw := (loop_spec epsilon⁻¹ 1 (by decide)).2.2.2.2
  change (loop epsilon⁻¹ 1 (by decide)).work+8≤_
  omega

theorem prepare_work_exact (epsilon : ℚ) : (prepare epsilon).work=12*(prepare epsilon).exponent+10 := by
  have hw := (loop_spec epsilon⁻¹ 1 (by decide)).2.2.2.2
  change (loop epsilon⁻¹ 1 (by decide)).work+8=12*(loop epsilon⁻¹ 1 (by decide)).doublings+10
  omega

theorem selected_labels (m : ℕ) (epsilon : ℚ) :
    ((GeneralPaperScoreScaleParameters.prepare m (prepare epsilon).exponent).K:ℚ)=128/(prepare epsilon).accuracy := by
  rw [accuracy_power]
  exact GeneralPaperScoreScaleParameters.labels_accuracy _ _

end Blotto.GeneralPaperDyadicAccuracy
