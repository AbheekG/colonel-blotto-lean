import Blotto.PlayerSpecificSourcePolynomialAutomation

/-! Substitution of polynomially bounded reached sizes into a polynomial
source-work bound. This is used to compose nested terminal cost profiles. -/
namespace Blotto.PlayerSpecificPolynomialSubstitution
set_option autoImplicit false

theorem substitute {α β : Type*} {sizeA : α → ℕ} {sizeB : β → ℕ}
    {f : β → ℕ} {g : α → β}
    (hf : NaturalPolynomialEnvelope sizeB f)
    (hg : NaturalPolynomialEnvelope sizeA (fun x => sizeB (g x))) :
    NaturalPolynomialEnvelope sizeA (fun x => f (g x)) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C*(D+1)^d,e*d,?_⟩
  intro x
  let Z := sizeA x+1
  have hZ : 1≤Z := by dsimp [Z]; omega
  have hp : 1≤Z^e := by
    simpa only [one_pow] using Nat.pow_le_pow_left hZ e
  have hs : sizeB (g x)+1≤(D+1)*Z^e := by
    have h := Nat.add_le_add (hg x) hp
    convert h using 1 <;> ring
  calc
    f (g x) ≤ C*(sizeB (g x)+1)^d := hf (g x)
    _ ≤ C*((D+1)*Z^e)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs d)
    _ = (C*(D+1)^d)*Z^(e*d) := by simp only [mul_pow,pow_mul]; ring

end Blotto.PlayerSpecificPolynomialSubstitution
