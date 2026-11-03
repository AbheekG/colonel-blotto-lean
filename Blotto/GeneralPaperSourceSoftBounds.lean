import Blotto.GeneralPaperLogarithmicSourceContract

/-! Soft bounds retain the value of each actual operand and discard only
polynomial factors in the proved logarithmic input measure. In particular,
fast arithmetic preserves a rate when the operand has a checked word bound;
it does not raise that operand rate to a polynomial arithmetic exponent. -/
namespace Blotto.GeneralPaperSourceSoftBounds
open GeneralPaperSourceWordGrowth GeneralPaperFastRationalModel
set_option autoImplicit false
set_option maxHeartbeats 1200000

def Soft (rate f : Input → ℕ) : Prop :=
  ∃ A e : ℕ,∀ x,f x≤A*rate x*(logSize x)^e

@[fun_prop]
def Polylog (f : Input → ℕ) : Prop := Soft (fun _ => 1) f

theorem identity (r : Input → ℕ) : Soft r r := by
  refine ⟨1,0,?_⟩
  intro x
  simp only [Nat.one_mul,pow_zero,Nat.mul_one,le_refl]

theorem dominated {r f g : Input → ℕ} (hg : Soft r g) (h : ∀ x,f x≤g x) : Soft r f := by
  rcases hg with ⟨A,e,hg⟩
  exact ⟨A,e,fun x => (h x).trans (hg x)⟩

theorem rate_mono {r s f : Input → ℕ} (hf : Soft r f) (h : ∀ x,r x≤s x) : Soft s f := by
  rcases hf with ⟨A,e,hf⟩
  exact ⟨A,e,fun x => (hf x).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (h x)))⟩

theorem bounded {f r : Input → ℕ} (A : ℕ) (h : ∀ x,f x≤A*r x) : Soft r f := by
  refine ⟨A,0,?_⟩
  simpa only [pow_zero,Nat.mul_one] using h

theorem add {r s f g : Input → ℕ} (hf : Soft r f) (hg : Soft s g) :
    Soft (fun x => r x+s x) (fun x => f x+g x) := by
  rcases hf with ⟨A,e,hf⟩
  rcases hg with ⟨B,d,hg⟩
  refine ⟨A+B,e+d,?_⟩
  intro x
  have hL := size_positive x
  have he := Nat.pow_le_pow_right hL (show e≤e+d by omega)
  have hd := Nat.pow_le_pow_right hL (show d≤e+d by omega)
  have hf' := (hf x).trans (Nat.mul_le_mul_left (A*r x) he)
  have hg' := (hg x).trans (Nat.mul_le_mul_left (B*s x) hd)
  nlinarith only [hf',hg',Nat.zero_le (A*s x*(logSize x)^(e+d)),Nat.zero_le (B*r x*(logSize x)^(e+d))]

theorem add_same {r f g : Input → ℕ} (hf : Soft r f) (hg : Soft r g) : Soft r (fun x => f x+g x) := by
  rcases add hf hg with ⟨A,e,h⟩
  refine ⟨2*A,e,?_⟩
  intro x
  exact (h x).trans_eq (by ring)

theorem mul {r s f g : Input → ℕ} (hf : Soft r f) (hg : Soft s g) :
    Soft (fun x => r x*s x) (fun x => f x*g x) := by
  rcases hf with ⟨A,e,hf⟩
  rcases hg with ⟨B,d,hg⟩
  refine ⟨A*B,e+d,?_⟩
  intro x
  exact (Nat.mul_le_mul (hf x) (hg x)).trans_eq (by rw [pow_add]; ring)

@[fun_prop]
theorem poly_tight (f : Input → ℕ) (hf : Tight f) : Polylog f := by
  rcases hf with ⟨A,h⟩
  refine ⟨A,1,?_⟩
  simpa only [Nat.mul_one,pow_one] using h

@[fun_prop]
theorem poly_constant (c : ℕ) : Polylog (fun _ => c) := poly_tight _ (tight_constant c)

@[fun_prop]
theorem poly_add (f g : Input → ℕ) (hf : Polylog f) (hg : Polylog g) : Polylog (fun x => f x+g x) :=
  add_same hf hg

@[fun_prop]
theorem poly_mul (f g : Input → ℕ) (hf : Polylog f) (hg : Polylog g) : Polylog (fun x => f x*g x) := by
  change Soft (fun _ => 1) _
  simpa only [Nat.one_mul] using mul hf hg

@[fun_prop]
theorem poly_power (f : Input → ℕ) (n : ℕ) (hf : Polylog f) : Polylog (fun x => (f x)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using poly_constant 1
  | succ n ih => simpa only [pow_succ] using poly_mul _ _ ih hf

@[fun_prop]
theorem poly_word (f : Input → ℕ) (hf : Small f) : Polylog (fun x => binaryWordWidth (f x)) :=
  poly_tight _ hf

@[fun_prop]
theorem factor_poly (d : ℕ) (f : Input → ℕ) (hf : Small f) : Polylog (fun x => logFactor d (f x)) := by
  unfold logFactor
  fun_prop

theorem mul_poly {r f g : Input → ℕ} (hf : Soft r f) (hg : Polylog g) : Soft r (fun x => f x*g x) := by
  simpa only [Nat.mul_one] using mul hf hg

theorem poly_mul_rate {r f g : Input → ℕ} (hf : Polylog f) (hg : Soft r g) : Soft r (fun x => f x*g x) := by
  simpa only [Nat.one_mul] using mul hf hg

theorem poly_at_rate {r f : Input → ℕ} (hf : Polylog f) (hr : ∀ x,1≤r x) : Soft r f :=
  rate_mono hf hr

theorem charge_preserves {r f : Input → ℕ} (C d : ℕ) (hf : Soft r f) (hw : Small f) :
    Soft r (fun x => charge C d (f x)) := by
  exact mul_poly (poly_mul_rate (poly_constant C) hf) (factor_poly d f hw)

@[fun_prop]
theorem poly_charge (C d : ℕ) (f : Input → ℕ) (hf : Polylog f) (hw : Small f) :
    Polylog (fun x => charge C d (f x)) := charge_preserves C d hf hw

theorem primitive_preserves {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    {r f : Input → ℕ} (hf : Soft r f) (hw : Small f) : Soft r (fun x => model.rat (f x)) :=
  dominated (charge_preserves C d hf hw) (fun x => hg (f x))

end Blotto.GeneralPaperSourceSoftBounds
