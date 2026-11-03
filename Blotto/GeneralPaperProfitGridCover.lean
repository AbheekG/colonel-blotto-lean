import Blotto.GeneralPaperProfitGridRound

/-! The actual fixed grid has the relative approximation promised in the
paper. Natural quotients below are erased existence witnesses in proofs;
runtime rounding uses only the cached arithmetic binary search.
-/
namespace Blotto.GeneralPaperProfitGridCover
open GeneralPaperProfitGridPoints GeneralPaperProfitGridPrepare
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem mantissa_cover (w scale D x : ℕ) (hW : 0<w) (hScale : 0<scale) (hD : 0<D)
    (hLow : w*scale*D≤x) (hHigh : x<2*w*scale*D) :
    ∃ a, w≤a ∧ a<2*w ∧ (a*scale)*D≤x ∧ (w-1)*x≤w*((a*scale)*D) := by
  let a := x/(scale*D)
  have hStep := Nat.mul_pos hScale hD
  have ha : w≤a := (Nat.le_div_iff_mul_le hStep).mpr (by simpa only [Nat.mul_assoc] using hLow)
  have hu : a<2*w := (Nat.div_lt_iff_lt_mul hStep).mpr (by simpa only [Nat.mul_assoc] using hHigh)
  have hf : a*(scale*D)≤x := Nat.div_mul_le_self _ _
  have hn : x<(a+1)*(scale*D) := (Nat.div_lt_iff_lt_mul hStep).mp (Nat.lt_succ_self a)
  have hw : w-1+1=w := by omega
  have hc : (w-1)*(a+1)≤w*a := by
    calc
      _ = (w-1)*a+(w-1) := by ring
      _ ≤ (w-1)*a+a := Nat.add_le_add_left (by omega) _
      _ = w*a := by rw [←Nat.add_one_mul,hw]
  refine ⟨a,ha,hu,by simpa only [Nat.mul_assoc] using hf,?_⟩
  calc
    _ ≤ (w-1)*((a+1)*(scale*D)) := Nat.mul_le_mul_left _ hn.le
    _ = ((w-1)*(a+1))*(scale*D) := by ring
    _ ≤ (w*a)*(scale*D) := Nat.mul_le_mul_right _ hc
    _ = _ := by ring

theorem band_cover (w B D x : ℕ) (hW : 0<w) (hD : 0<D)
    (hLow : w*D≤x) (hHigh : x<2*w*2^B*D) :
    ∃ h≤B, ∃ a, w≤a ∧ a<2*w ∧ (a*2^h)*D≤x ∧ (w-1)*x≤w*((a*2^h)*D) := by
  induction B with
  | zero =>
    have he := mantissa_cover w 1 D x hW (by decide) hD
      (by simpa only [Nat.mul_one] using hLow) (by simpa only [pow_zero,Nat.mul_one] using hHigh)
    exact ⟨0,le_rfl,by simpa only [pow_zero] using he⟩
  | succ B ih =>
    by_cases hOld : x<2*w*2^B*D
    · obtain ⟨h,hh,a,ha,hu,hf,hr⟩ := ih hOld
      exact ⟨h,by omega,a,ha,hu,hf,hr⟩
    · have hBase : w*2^(B+1)*D≤x := by
        have he : w*2^(B+1)*D=2*w*2^B*D := by rw [pow_succ]; ring
        rw [he]
        omega
      obtain ⟨a,ha,hu,hf,hr⟩ := mantissa_cover w (2^(B+1)) D x hW (Nat.two_pow_pos _) hD hBase hHigh
      exact ⟨B+1,le_rfl,a,ha,hu,hf,hr⟩

theorem grid_cover (w B D x : ℕ) (hW : 0<w) (hD : 0<D)
    (hLow : w*D≤x) (hHigh : x≤2*denominator w B*D) :
    ∃ value, value∈ordered w B ∧ 0<value ∧ value*D≤x ∧ (w-1)*x≤w*(value*D) := by
  by_cases hEnd : x=2*denominator w B*D
  · refine ⟨2*denominator w B,(member_iff w B _).mpr (Or.inr (Or.inl rfl)),by
      have := denominator_positive w B hW; omega,by omega,?_⟩
    rw [←hEnd]
    exact Nat.mul_le_mul_right x (Nat.sub_le w 1)
  · have hTop : x<2*w*2^B*D := by
      have he : 2*w*2^B*D=2*denominator w B*D := by unfold denominator; ring
      rw [he]
      omega
    obtain ⟨h,hh,a,ha,hu,hf,hr⟩ := band_cover w B D x hW hD hLow hTop
    refine ⟨a*2^h,(member_iff w B _).mpr (Or.inr (Or.inr ?_)),Nat.mul_pos (by omega) (Nat.two_pow_pos _),hf,hr⟩
    exact (points_mem w B _).mpr ⟨h,hh,a,ha,hu,rfl⟩

theorem leaf_relative (q w B P : ℕ) (hQ : 0<q) (hW : 0<w)
    (hLow : q≤P*2^B) (hHigh : P≤2*q) :
    (w-1)*(P*denominator w B)≤w*(q*(prepare q w B).numerators.read
      (GeneralPaperProfitGridRound.leaf (prepare q w B) P).label) := by
  have hLower : w*q≤P*denominator w B := by
    have he := Nat.mul_le_mul_left w hLow
    simpa only [denominator,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using he
  have hUpper : P*denominator w B≤2*denominator w B*q := by
    have he := Nat.mul_le_mul_right (denominator w B) hHigh
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using he
  obtain ⟨value,hValue,hPos,hDown,hRel⟩ := grid_cover w B q (P*denominator w B) hW hQ hLower hUpper
  obtain ⟨i,hi⟩ := represents q w B value hValue
  have hm := GeneralPaperProfitGridRound.leaf_value_maximal q w B P i (by rw [hi]; nlinarith only [hDown])
  rw [hi] at hm
  exact hRel.trans (by nlinarith only [Nat.mul_le_mul_left (w*q) hm])

theorem leaf_positive (q w B P : ℕ) (hQ : 0<q) (hW : 0<w) (hLow : q≤P*2^B) (hHigh : P≤2*q) :
    0<(prepare q w B).numerators.read (GeneralPaperProfitGridRound.leaf (prepare q w B) P).label := by
  have hLower : w*q≤P*denominator w B := by
    have he := Nat.mul_le_mul_left w hLow
    simpa only [denominator,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using he
  have hUpper : P*denominator w B≤2*denominator w B*q := by
    have he := Nat.mul_le_mul_right (denominator w B) hHigh
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using he
  obtain ⟨value,hValue,hPos,hDown,_⟩ := grid_cover w B q (P*denominator w B) hW hQ hLower hUpper
  obtain ⟨i,hi⟩ := represents q w B value hValue
  have hm := GeneralPaperProfitGridRound.leaf_value_maximal q w B P i (by rw [hi]; nlinarith only [hDown])
  rw [hi] at hm
  exact hPos.trans_le hm

theorem merge_relative (q w B P : ℕ) (hW : 0<w) (hLow : w≤P) (hHigh : P≤2*denominator w B) :
    (w-1)*P≤w*(prepare q w B).numerators.read (GeneralPaperProfitGridRound.merge (prepare q w B) P).label := by
  obtain ⟨value,hValue,hPos,hDown,hRel⟩ := grid_cover w B 1 P hW (by decide) (by simpa using hLow) (by simpa using hHigh)
  obtain ⟨i,hi⟩ := represents q w B value hValue
  have hm := GeneralPaperProfitGridRound.merge_value_maximal q w B P i (by rw [hi]; simpa using hDown)
  rw [hi] at hm
  have he := Nat.mul_le_mul_left w hm
  simp only [Nat.mul_one] at hRel
  exact hRel.trans he

theorem merge_positive (q w B P : ℕ) (hW : 0<w) (hLow : w≤P) (hHigh : P≤2*denominator w B) :
    0<(prepare q w B).numerators.read (GeneralPaperProfitGridRound.merge (prepare q w B) P).label := by
  obtain ⟨value,hValue,hPos,hDown,_⟩ := grid_cover w B 1 P hW (by decide) (by simpa using hLow) (by simpa using hHigh)
  obtain ⟨i,hi⟩ := represents q w B value hValue
  have hm := GeneralPaperProfitGridRound.merge_value_maximal q w B P i (by rw [hi]; simpa using hDown)
  rw [hi] at hm
  exact hPos.trans_le hm

end Blotto.GeneralPaperProfitGridCover
