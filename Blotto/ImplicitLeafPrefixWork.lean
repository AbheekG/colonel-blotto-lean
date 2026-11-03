import Blotto.ImplicitResourcePrefix

/-! Exact expanded leaf prefixes with explicit per-block callback prices.
The observer charges the clipped-count/multiply callback and one rational add
per block. Implementing those callbacks in finite binary words remains separate. -/

namespace Blotto.ImplicitLeafCounts

def prefixWithWork (price : Block → ℤ → ℕ) (addPrice : ℕ) : List Block → ℤ → ℚ × ℕ
  | [], _ => (0, 1)
  | block :: rest, cutoff =>
      let later := prefixWithWork price addPrice rest cutoff
      (blockMass block cutoff + later.1, price block cutoff + addPrice + 3 + later.2)

theorem prefixWithWork_state (price : Block → ℤ → ℕ) (addPrice : ℕ) (blocks : List Block) (cutoff : ℤ) :
    (prefixWithWork price addPrice blocks cutoff).1 = prefixMass blocks cutoff := by
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp only [prefixWithWork, prefixMass, ih]

theorem prefixWithWork_bound (price : Block → ℤ → ℕ) (addPrice : ℕ) (blocks : List Block) (cutoff : ℤ)
    (P : ℕ) (hp : ∀ block ∈ blocks, price block cutoff ≤ P) :
    (prefixWithWork price addPrice blocks cutoff).2 ≤ blocks.length * (P + addPrice + 3) + 1 := by
  induction blocks with
  | nil => simp [prefixWithWork]
  | cons block rest ih =>
    have hHead := hp block (by simp)
    have hRest := ih (fun b hb => hp b (by simp [hb]))
    simp only [prefixWithWork, List.length_cons]
    nlinarith

def prefixPrimitivePrice (_block : Block) (_cutoff : ℤ) : ℕ := 7

theorem prefixPrimitiveWork (blocks : List Block) (cutoff : ℤ) :
    (prefixWithWork prefixPrimitivePrice 1 blocks cutoff).2 ≤ 11 * blocks.length + 1 := by
  have he := prefixWithWork_bound prefixPrimitivePrice 1 blocks cutoff 7 (by intro b hb; exact le_rfl)
  simpa only [Nat.add_assoc, Nat.mul_comm] using he

end Blotto.ImplicitLeafCounts
