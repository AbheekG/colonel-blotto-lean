import Blotto.BinaryWordWidthCore

/-! Executed natural powers by repeated squaring. The operation counter
counts arithmetic/control operations; bit and live-space prices are separate.
The exponent is halved on each recursive call, with no runtime logarithm.
-/
namespace Blotto.GeneralPaperNatPower
set_option autoImplicit false

structure Result where
  power : ℕ
  steps : ℕ
  work : ℕ

def run (base exponent : ℕ) : Result :=
  if exponent=0 then ⟨1,0,2⟩ else
    let earlier := run base (exponent/2)
    let square := earlier.power*earlier.power
    let value := if exponent%2=0 then square else square*base
    ⟨value,earlier.steps+1,earlier.work+12⟩
termination_by exponent
decreasing_by omega

theorem data (base exponent : ℕ) :
    (run base exponent).power=base^exponent ∧
    (run base exponent).work=12*(run base exponent).steps+2 := by
  generalize hr : run base exponent=result
  rw [run] at hr
  split at hr
  · rename_i hz
    subst result
    simp [hz]
  · rename_i hn
    have ih := data base (exponent/2)
    have hd := Nat.mod_add_div exponent 2
    have hm := Nat.mod_lt exponent (by decide : 0<2)
    subst result
    dsimp only
    refine ⟨?_,by rw [ih.2]; omega⟩
    split
    · rename_i he
      have hn : exponent=exponent/2+exponent/2 := by omega
      calc
        _ = base^(exponent/2+exponent/2) := by rw [pow_add,ih.1]
        _ = base^exponent := congrArg (fun n => base^n) hn.symm
    · rename_i ho
      have hn : exponent=exponent/2+exponent/2+1 := by omega
      calc
        _ = base^(exponent/2+exponent/2+1) := by rw [pow_succ,pow_add,ih.1]
        _ = base^exponent := congrArg (fun n => base^n) hn.symm
termination_by exponent
decreasing_by omega

theorem steps_le (base exponent depth : ℕ) (h : exponent<2^depth) :
    (run base exponent).steps≤depth := by
  rw [run]
  split
  · exact Nat.zero_le _
  · rename_i hn
    have hj : depth≠0 := by intro hz; subst depth; norm_num at h; omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hh : exponent/2<2^j := by rw [pow_succ] at h; omega
    have ih := steps_le base (exponent/2) j hh
    change (run base (exponent/2)).steps+1≤j+1
    omega
termination_by exponent
decreasing_by omega

theorem work_bound (base exponent : ℕ) :
    (run base exponent).work≤12*binaryWordWidth exponent+2 := by
  have hs := steps_le base exponent (binaryWordWidth exponent) (lt_pow_binaryWordWidth exponent)
  rw [(data base exponent).2]
  omega

end Blotto.GeneralPaperNatPower
