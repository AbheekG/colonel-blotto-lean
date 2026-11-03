import Blotto.GeneralPaperPowerCeilingBits

/-! Shared literal initializer products. The prefix 4*m*H is formed once
and reused for N and the auxiliary numerator. Word bounds include every
raw product, square and branch, before any rational reduction.
-/
namespace Blotto.GeneralPaperInitializerProducts
set_option autoImplicit false
set_option maxHeartbeats 6000000

structure Products where
  first : ℕ
  shared : ℕ
  third : ℕ
  N : ℕ
  chosen : ℕ
  square : ℕ
  scaled : ℕ

def run (m H p q : ℕ) (reciprocal : Bool) : Products :=
  let first := 4*m
  let shared := first*H
  let third := shared*p
  let N := third*q
  let chosen := if reciprocal then q else p
  let square := chosen*chosen
  ⟨first,shared,third,N,chosen,square,shared*square⟩

def width (m H p q : ℕ) : ℕ := 4+binaryWordWidth m+binaryWordWidth H+binaryWordWidth p+binaryWordWidth q

theorem words (m H p q : ℕ) (reciprocal : Bool) :
    let c := run m H p q reciprocal
    let F := width m H p q
    binaryWordWidth m≤F ∧ binaryWordWidth H≤F ∧ binaryWordWidth p≤F ∧ binaryWordWidth q≤F ∧
    binaryWordWidth c.first≤F ∧ binaryWordWidth c.shared≤F ∧ binaryWordWidth c.third≤F ∧ binaryWordWidth c.N≤F ∧
    binaryWordWidth c.chosen≤F ∧ binaryWordWidth c.square≤2*F ∧ binaryWordWidth c.scaled≤3*F := by
  let c := run m H p q reciprocal
  let F := width m H p q
  have h4 : binaryWordWidth 4=3 := by decide
  have h1 := binaryWordWidth_mul 4 m
  have h2 := binaryWordWidth_mul (4*m) H
  have h3 := binaryWordWidth_mul (4*m*H) p
  have h4p := binaryWordWidth_mul (4*m*H*p) q
  have hc : binaryWordWidth c.chosen≤F := by
    dsimp only [c,run]
    split <;> unfold F width <;> omega
  have hs := binaryWordWidth_mul c.chosen c.chosen
  have hb := binaryWordWidth_mul c.shared c.square
  change binaryWordWidth c.square≤binaryWordWidth c.chosen+binaryWordWidth c.chosen at hs
  change binaryWordWidth c.scaled≤binaryWordWidth c.shared+binaryWordWidth c.square at hb
  change binaryWordWidth c.first≤binaryWordWidth 4+binaryWordWidth m at h1
  change binaryWordWidth c.shared≤binaryWordWidth c.first+binaryWordWidth H at h2
  change binaryWordWidth c.third≤binaryWordWidth c.shared+binaryWordWidth p at h3
  change binaryWordWidth c.N≤binaryWordWidth c.third+binaryWordWidth q at h4p
  change binaryWordWidth m≤F ∧ binaryWordWidth H≤F ∧ binaryWordWidth p≤F ∧ binaryWordWidth q≤F ∧
    binaryWordWidth c.first≤F ∧ binaryWordWidth c.shared≤F ∧ binaryWordWidth c.third≤F ∧ binaryWordWidth c.N≤F ∧
    binaryWordWidth c.chosen≤F ∧ binaryWordWidth c.square≤2*F ∧ binaryWordWidth c.scaled≤3*F
  unfold F width at *
  omega

end Blotto.GeneralPaperInitializerProducts
