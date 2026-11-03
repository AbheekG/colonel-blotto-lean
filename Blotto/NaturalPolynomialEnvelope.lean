import Blotto.BinaryWordWidth
import Blotto.RationalExpressionHeight

/-! Closure rules for natural-valued polynomial envelopes. These certify growth
of a formula, not that the formula measures an implementation's full runtime. -/

namespace Blotto

def NaturalPolynomialEnvelope {α : Type*} (size f : α → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ x, f x ≤ C * (size x + 1) ^ d

namespace NaturalPolynomialEnvelope

theorem constant {α : Type*} (size : α → ℕ) (k : ℕ) :
    NaturalPolynomialEnvelope size (fun _ => k) :=
  ⟨k, 0, by intro x; simp⟩

theorem of_le_size {α : Type*} (size f : α → ℕ) (h : ∀ x, f x ≤ size x) :
    NaturalPolynomialEnvelope size f :=
  ⟨1, 1, by intro x; simpa using (h x).trans (Nat.le_succ _)⟩

theorem add {α : Type*} {size f g : α → ℕ}
    (hf : NaturalPolynomialEnvelope size f) (hg : NaturalPolynomialEnvelope size g) :
    NaturalPolynomialEnvelope size (fun x => f x + g x) := by
  rcases hf with ⟨C, d, hf⟩
  rcases hg with ⟨D, e, hg⟩
  refine ⟨C + D, d + e, ?_⟩
  intro x
  have hd : (size x + 1) ^ d ≤ (size x + 1) ^ (d + e) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have he : (size x + 1) ^ e ≤ (size x + 1) ^ (d + e) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc
    f x + g x ≤ C * (size x + 1) ^ d + D * (size x + 1) ^ e := Nat.add_le_add (hf x) (hg x)
    _ ≤ C * (size x + 1) ^ (d + e) + D * (size x + 1) ^ (d + e) :=
      Nat.add_le_add (Nat.mul_le_mul_left C hd) (Nat.mul_le_mul_left D he)
    _ = _ := by ring

theorem mul {α : Type*} {size f g : α → ℕ}
    (hf : NaturalPolynomialEnvelope size f) (hg : NaturalPolynomialEnvelope size g) :
    NaturalPolynomialEnvelope size (fun x => f x * g x) := by
  rcases hf with ⟨C, d, hf⟩
  rcases hg with ⟨D, e, hg⟩
  refine ⟨C * D, d + e, ?_⟩
  intro x
  calc
    f x * g x ≤ (C * (size x + 1) ^ d) * (D * (size x + 1) ^ e) := Nat.mul_le_mul (hf x) (hg x)
    _ = _ := by rw [pow_add]; ring

theorem pow {α : Type*} {size f : α → ℕ}
    (hf : NaturalPolynomialEnvelope size f) (k : ℕ) :
    NaturalPolynomialEnvelope size (fun x => f x ^ k) := by
  induction k with
  | zero => simpa using constant size 1
  | succ k ih => simpa only [pow_succ] using mul ih hf

theorem dominated {α : Type*} {size f g : α → ℕ}
    (hg : NaturalPolynomialEnvelope size g) (h : ∀ x, f x ≤ g x) :
    NaturalPolynomialEnvelope size f := by
  rcases hg with ⟨C, d, hg⟩
  exact ⟨C, d, fun x => (h x).trans (hg x)⟩

theorem sub {α : Type*} {size f g : α → ℕ}
    (hf : NaturalPolynomialEnvelope size f) :
    NaturalPolynomialEnvelope size (fun x => f x - g x) :=
  dominated hf (fun _ => Nat.sub_le _ _)

theorem max {α : Type*} {size f g : α → ℕ}
    (hf : NaturalPolynomialEnvelope size f) (hg : NaturalPolynomialEnvelope size g) :
    NaturalPolynomialEnvelope size (fun x => max (f x) (g x)) :=
  dominated (add hf hg) (fun _ => by omega)

theorem wordWidth {α : Type*} {size f : α → ℕ}
    (hf : NaturalPolynomialEnvelope size f) :
    NaturalPolynomialEnvelope size (fun x => binaryWordWidth (f x)) := by
  apply dominated (add hf (constant size 1))
  intro x
  unfold binaryWordWidth
  have h := Nat.log2_le_self (f x)
  omega

theorem height {α : Type*} {size f : α → ℕ}
    (hf : NaturalPolynomialEnvelope size f) (d : ℕ) :
    NaturalPolynomialEnvelope size (fun x => expressionHeightBudget (f x) d) := by
  unfold expressionHeightBudget
  exact sub (mul (add hf (constant size 1)) (constant size (2 ^ d)))

end NaturalPolynomialEnvelope
end Blotto
