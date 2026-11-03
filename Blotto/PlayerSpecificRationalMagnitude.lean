import Blotto.PlayerSpecificIsolationBounds
import Blotto.RationalAggregateRecognitionCost

/-! Coefficient magnitudes are bounded from actual reduced rational word
lengths. Nonzero inverse magnitudes give a computed leading-coefficient
lower bound. No input height or nonzero-magnitude oracle is supplied. -/
namespace Blotto.PlayerSpecificRationalMagnitude
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization
set_option autoImplicit false
set_option maxHeartbeats 3500000

def inputHeight (p : Data) : ℕ := RationalAggregateRecognitionCost.totalWidth p+1

theorem member_width (p : Data) (q : ℚ) (hq : q∈p) : rationalWordWidth q≤RationalAggregateRecognitionCost.totalWidth p := by
  induction p with
  | nil => simp only [List.not_mem_nil] at hq
  | cons a p ih =>
    simp only [RationalAggregateRecognitionCost.totalWidth,List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp hq with he | ht
    · subst q
      omega
    · have h := ih ht
      dsimp only [RationalAggregateRecognitionCost.totalWidth] at h
      omega

theorem member_height (p : Data) (q : ℚ) (hq : q∈p) : RationalHeight q (inputHeight p) :=
  (rationalHeight_of_wordWidth q).mono ((member_width p q hq).trans (Nat.le_succ _))

theorem coefficient_height (p : Data) (j : ℕ) : RationalHeight ((semantics p).coeff j) (inputHeight p) := by
  rw [coefficient]
  cases he : p[j]? with
  | none =>
    have hz : RationalHeight (0 : ℚ) 1 := by norm_num [RationalHeight]
    exact hz.mono (by unfold inputHeight; omega)
  | some q => exact member_height p q (List.mem_of_getElem? he)

theorem trim_member (p : Data) : ∀ q∈trim p,q∈p := by
  induction p with
  | nil => intro q hq; simp only [trim,List.not_mem_nil] at hq
  | cons a p ih =>
    intro q hq
    rw [trim] at hq
    split at hq
    · simp only [List.not_mem_nil] at hq
    · rcases List.mem_cons.mp hq with he | ht
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem _ (ih q ht)

theorem leading_height (p : Data) (hp : semantics p≠0) :
    RationalHeight ((trim p).getLast?.getD 0) (inputHeight p) := by
  have hn : trim p≠[] := fun h => hp ((trim_nil_iff p).mp h)
  rw [List.getLast?_eq_some_getLast hn,Option.getD_some]
  exact member_height p _ (trim_member p _ (List.mem_of_getLast? (List.getLast?_eq_some_getLast hn)))

theorem real_upper (q : ℚ) (s : ℕ) (h : RationalHeight q s) : |(q : ℝ)|<(2:ℝ)^s := by
  have hn : (q.num.natAbs : ℝ)<(2:ℝ)^s := by exact_mod_cast h.1
  have hnum : |(q.num : ℝ)|<(2:ℝ)^s := by
    rw [Nat.cast_natAbs,Int.cast_abs] at hn
    exact hn
  have hd : (1 : ℝ)≤(q.den : ℝ) := by exact_mod_cast q.den_pos
  have hden : (0 : ℝ)<(q.den : ℝ) := by exact_mod_cast q.den_pos
  have he : (q : ℝ)=(q.num : ℝ)/(q.den : ℝ) := by
    have hh := congrArg (fun r : ℚ => (r : ℝ)) q.num_div_den
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using hh.symm
  rw [he,abs_div,abs_of_pos hden]
  exact (div_le_self (abs_nonneg _) hd).trans_lt hnum

theorem real_lower (q : ℚ) (s : ℕ) (h : RationalHeight q s) (hq : q≠0) :
    (1 : ℝ)/(2:ℝ)^s < |(q : ℝ)| := by
  have hi := real_upper q⁻¹ s h.inv
  have hi' : (1 : ℝ)/|(q : ℝ)| < (2:ℝ)^s := by
    simpa only [Rat.cast_inv,abs_inv,one_div] using hi
  have hqr : (q : ℝ)≠0 := by exact_mod_cast hq
  have hprod := (div_lt_iff₀ (abs_pos.mpr hqr)).mp hi'
  apply (div_lt_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) s)).mpr
  nlinarith only [hprod]

theorem real_coefficient (p : Data) (j : ℕ) :
    (PlayerSpecificSquarefreeAlgorithm.realPolynomial p).coeff j=(((semantics p).coeff j : ℚ) : ℝ) := by
  rw [PlayerSpecificSquarefreeAlgorithm.realPolynomial,Polynomial.coeff_map]
  rfl

theorem real_leading (p : Data) (hp : semantics p≠0) :
    (PlayerSpecificSquarefreeAlgorithm.realPolynomial p).leadingCoeff=(((trim p).getLast?.getD 0 : ℚ) : ℝ) := by
  have hn : trim p≠[] := fun h => hp ((trim_nil_iff p).mp h)
  rw [PlayerSpecificSquarefreeAlgorithm.realPolynomial,Polynomial.leadingCoeff_map]
  change ((semantics p).leadingCoeff : ℝ)=_
  rw [← trim_semantics p,leading_coefficient _ (trim_normalized p) hn]

end Blotto.PlayerSpecificRationalMagnitude
