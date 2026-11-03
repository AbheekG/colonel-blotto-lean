import Blotto.GeneralPaperSourceRowsModelsContract

/-! Repeated squaring in the paper's arithmetic model. Halving and parity
come from the executed growing quotient; division/modulus occur only in
proofs. The quotient fuel is the constructed exponent, not its encoding. -/
namespace Blotto.GeneralPaperPhysicalPowerArithmetic
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem division_cap (exponent : ℕ) : exponent<2*2^exponent := by
  have h : exponent<2^exponent := Nat.lt_two_pow_self
  omega

theorem half_data (exponent : ℕ) :
    (GeneralPaperConstructedNatDivision.run exponent 2 exponent).quotient=exponent/2 ∧
    (GeneralPaperConstructedNatDivision.run exponent 2 exponent).remainder=exponent%2 :=
  ⟨GeneralPaperConstructedNatDivision.quotient_eq exponent 2 exponent (by decide) (division_cap exponent),
    GeneralPaperConstructedNatDivision.remainder_eq exponent 2 exponent (by decide) (division_cap exponent)⟩

def run (base exponent : ℕ) : ℕ × ℕ :=
  if exponent=0 then (1,2) else
    let divided := GeneralPaperConstructedNatDivision.run exponent 2 exponent
    let earlier := run base divided.quotient
    let square := earlier.1*earlier.1
    let value := if divided.remainder=0 then square else square*base
    (value,earlier.2+divided.work+16)
termination_by exponent
decreasing_by rw [(half_data exponent).1]; omega

theorem data (base exponent : ℕ) : (run base exponent).1=base^exponent := by
  rw [run]
  split
  · rename_i hz
    simp only [hz,pow_zero]
  · rename_i hn
    dsimp only
    rw [(half_data exponent).1,(half_data exponent).2,data base (exponent/2)]
    have hd := Nat.mod_add_div exponent 2
    have hm := Nat.mod_lt exponent (by decide : 0<2)
    split
    · rename_i he
      have h : exponent=exponent/2+exponent/2 := by omega
      rw [←pow_add,←h]
    · rename_i he
      have h : exponent=exponent/2+exponent/2+1 := by omega
      rw [←pow_add,←pow_succ,←h]
termination_by exponent
decreasing_by omega

theorem work_depth (base exponent depth : ℕ) (h : exponent<2^depth) :
    (run base exponent).2≤64*(depth+1)^2 := by
  rw [run]
  split
  · dsimp only
    nlinarith only [Nat.zero_le depth]
  · rename_i hn
    have hd : depth≠0 := by intro hz; subst depth; norm_num at h; omega
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    have hh : exponent/2<2^d := by rw [pow_succ] at h; omega
    have hi := work_depth base (exponent/2) d hh
    have hw := GeneralPaperConstructedNatDivision.work_word_bound exponent 2 exponent (by decide) (division_cap exponent)
    rw [(half_data exponent).1] at hw
    have hq := GeneralPaperCFOperandPrice.small_word d (exponent/2) hh
    dsimp only
    rw [(half_data exponent).1]
    nlinarith only [hi,hw,hq]
termination_by exponent
decreasing_by omega

theorem work (base exponent : ℕ) : (run base exponent).2≤64*(binaryWordWidth exponent+1)^2 :=
  work_depth base exponent (binaryWordWidth exponent) (lt_pow_binaryWordWidth exponent)

end Blotto.GeneralPaperPhysicalPowerArithmetic
