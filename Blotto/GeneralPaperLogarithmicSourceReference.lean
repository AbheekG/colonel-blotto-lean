import Blotto.GeneralPaperClosedProfileWordGrowth

/-! The derived common source reference width has the paper's logarithmic
parameter growth. The coefficient depends only on fixed fast-arithmetic
constants, not on the source inputs or primitive model. All width/profile
functions are erased analysis of already checked native execution bounds. -/
namespace Blotto.GeneralPaperLogarithmicSourceReference
open GeneralPaperSourceWordGrowth GeneralPaperConstructedWordGrowth GeneralPaperNativeSourceWordGrowth
open GeneralPaperInitializerPreparedPoint
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

theorem tight_dominated {f g : Input → ℕ} (hg : Tight g) (h : ∀ x,f x≤g x) : Tight f := by
  rcases hg with ⟨C,hC⟩
  exact ⟨C,fun x => (h x).trans (hC x)⟩

theorem controls_tight : Tight (fun x => GeneralPaperPrecallControlWord.word x.m x.k) := by
  apply tight_dominated (g:=fun x => 192+8*binaryWordWidth (x.k+1)+8*binaryWordWidth ((alphabet x).lambda+1))
  · fun_prop
  · intro x
    exact GeneralPaperPrecallWordEnvelope.word_bound _ _

noncomputable def width (C d : ℕ) (x : Input) : ℕ :=
  GeneralPaperFastSourceReference.preparedWidth C d x.k x.Qv x.B
    ((alphabet x).lambda+1) ((alphabet x).lambda+1) x.weights
    (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)

theorem width_tight (C d : ℕ) : Tight (width C d) := by
  have hp := GeneralPaperClosedProfileWordGrowth.profile_small C d
  have hw := tight_mul_left 4 _ (word_tight _ hp)
  have hs := tight_add _ _ hw controls_tight
  exact hs

theorem reference_bound (C d : ℕ) :
    ∃ A : ℕ,∀ x,width C d x≤A*(128+x.k+binaryWordWidth (x.m+1)+
      binaryWordWidth ((alphabet x).lambda+1)+binaryWordWidth (x.Qv+1)+binaryWordWidth (x.B+1)) :=
  width_tight C d

theorem profile_envelope (C d : ℕ) : ∃ A : ℕ,∀ x,
    GeneralPaperClosedProfileWordGrowth.atOne C d x<2^(A*logSize x) := by
  rcases GeneralPaperClosedProfileWordGrowth.profile_small C d with ⟨A,hA⟩
  exact ⟨A,fun x => (lt_pow_binaryWordWidth _).trans_le (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (hA x))⟩

theorem power_word_bound (n : ℕ) : 2^binaryWordWidth n≤2*(n+1) := by
  by_cases hn : n=0
  · subst n
    decide
  · have h := Nat.log2_self_le hn
    unfold binaryWordWidth
    rw [pow_succ]
    omega

def parameterProduct (x : Input) : ℕ :=
  2^x.k*(x.m+2)*((alphabet x).lambda+2)*(x.Qv+2)*(x.B+2)

theorem size_power_bound (x : Input) : 2^logSize x≤2^132*parameterProduct x := by
  have hm := power_word_bound (x.m+1)
  have hl := power_word_bound ((alphabet x).lambda+1)
  have hq := power_word_bound (x.Qv+1)
  have hb := power_word_bound (x.B+1)
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.le_refl (2^128*2^x.k)) hm) hl) hq) hb
  calc
    2^logSize x=(2^128*2^x.k)*2^binaryWordWidth (x.m+1)*2^binaryWordWidth ((alphabet x).lambda+1)*
        2^binaryWordWidth (x.Qv+1)*2^binaryWordWidth (x.B+1) := by simp only [logSize,pow_add]
    _≤(2^128*2^x.k)*(2*(x.m+1+1))*(2*((alphabet x).lambda+1+1))*(2*(x.Qv+1+1))*(2*(x.B+1+1)) := hprod
    _=2^132*parameterProduct x := by
      rw [show 132=128+4 by decide,pow_add]
      norm_num only [show (2:ℕ)^4=16 by decide]
      unfold parameterProduct
      ring

theorem polynomial_profile (C d : ℕ) : ∃ K A : ℕ,∀ x,
    GeneralPaperClosedProfileWordGrowth.atOne C d x<K*(parameterProduct x)^A := by
  rcases profile_envelope C d with ⟨A,hA⟩
  refine ⟨(2^132)^A,A,?_⟩
  intro x
  apply (hA x).trans_le
  calc
    2^(A*logSize x)=(2^logSize x)^A := by rw [←pow_mul]; congr 1; ring
    _≤(2^132*parameterProduct x)^A := Nat.pow_le_pow_left (size_power_bound x) A
    _=(2^132)^A*(parameterProduct x)^A := mul_pow ..

end Blotto.GeneralPaperLogarithmicSourceReference
