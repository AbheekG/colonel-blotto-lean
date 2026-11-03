import Blotto.GeneralPaperScoreStageBits

/-! The paper's doubling-until-large-enough construction on constructed
integer targets. Termination uses an erased decreasing integer measure;
the executable branch tests the target and doubles, with no logarithm or
input-encoding query. The returned exponent is recorded along the path.
-/
namespace Blotto.GeneralPaperPowerCeiling
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure Result where
  power : ℕ
  doublings : ℕ
  work : ℕ

def loop (target p : ℕ) (hp : 0<p) : Result :=
  if target≤p then ⟨p,0,2⟩ else
    let later := loop target (2*p) (by omega)
    ⟨later.power,later.doublings+1,later.work+12⟩
termination_by target-p
decreasing_by omega

theorem loop_spec (target p : ℕ) (hp : 0<p) :
    (loop target p hp).power=p*2^(loop target p hp).doublings ∧
    target≤(loop target p hp).power ∧
    ((loop target p hp).doublings=0 → (loop target p hp).power=p) ∧
    (0<(loop target p hp).doublings → (loop target p hp).power<2*target) ∧
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
    · rw [ih.1,pow_succ]
      ring
    · omega
    · intro _
      by_cases hz : (loop target (2*p) (by omega)).doublings=0
      · have hPower := ih.2.2.1 hz
        omega
      · exact ih.2.2.2.1 (by omega)
    · rw [ih.2.2.2.2]
      omega
termination_by target-p
decreasing_by omega

theorem loop_minimal (target p : ℕ) (hp : 0<p) (j : ℕ) (hTarget : target≤p*2^j) :
    (loop target p hp).doublings≤j := by
  rw [loop]
  split
  · exact Nat.zero_le _
  · rename_i hContinue
    have hj : j≠0 := by intro hz; subst j; simp only [pow_zero,Nat.mul_one] at hTarget; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have ht : target≤(2*p)*2^k := by
      simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hTarget
    have ih := loop_minimal target (2*p) (by omega) k ht
    change (loop target (2*p) (by omega)).doublings+1≤k+1
    omega
termination_by target-p
decreasing_by omega

theorem loop_depth (target p : ℕ) (hp : 0<p) :
    (loop target p hp).doublings≤binaryWordWidth target := by
  apply loop_minimal
  exact (lt_pow_binaryWordWidth target).le.trans
    (by have h := Nat.mul_le_mul_right (2^binaryWordWidth target) (show 1≤p by omega); simpa only [Nat.one_mul] using h)

def ceiling (target : ℕ) : Result := loop target 1 (by decide)

theorem ceiling_power (target : ℕ) : (ceiling target).power=2^(ceiling target).doublings := by
  simpa only [ceiling,Nat.one_mul] using (loop_spec target 1 (by decide)).1

theorem ceiling_lower (target : ℕ) : target≤(ceiling target).power := (loop_spec target 1 (by decide)).2.1

theorem ceiling_upper (target : ℕ) (ht : 0<target) : (ceiling target).power<2*target := by
  have hs := loop_spec target 1 (by decide)
  by_cases hz : (ceiling target).doublings=0
  · have hp := hs.2.2.1 hz
    change (ceiling target).power=1 at hp
    omega
  · exact hs.2.2.2.1 (Nat.pos_of_ne_zero hz)

theorem ceiling_minimal (target j : ℕ) (ht : target≤2^j) : (ceiling target).doublings≤j :=
  loop_minimal target 1 (by decide) j (by simpa only [Nat.one_mul] using ht)

theorem ceiling_work (target : ℕ) : (ceiling target).work≤12*binaryWordWidth target+2 := by
  have hd := loop_depth target 1 (by decide)
  have hw := (loop_spec target 1 (by decide)).2.2.2.2
  change (ceiling target).doublings≤binaryWordWidth target at hd
  change (ceiling target).work=12*(ceiling target).doublings+2 at hw
  omega

end Blotto.GeneralPaperPowerCeiling
