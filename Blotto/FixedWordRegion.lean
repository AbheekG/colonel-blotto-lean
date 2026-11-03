import Blotto.TableStoreRAM

/-! Fixed-width slot addresses for a finite binary RAM region. Every bit
address lies in its allocated interval and fits its derived address width.
The layout is injective; unrelated prefix/suffix addresses are disjoint.
Address arithmetic implementation costs remain an explicit backend contract. -/

namespace Blotto.FixedWordRegion

def localAddress {n W : ℕ} (j : Fin n) (offset : Fin W) : Fin (n * W) := finProdFinEquiv (j, offset)

theorem localAddress_val {n W : ℕ} (j : Fin n) (offset : Fin W) :
    (localAddress j offset).val = j.val * W + offset.val := by
  change offset.val + W * j.val = _
  ring

theorem localAddress_injective (n W : ℕ) :
    Function.Injective (fun p : Fin n × Fin W => localAddress p.1 p.2) := finProdFinEquiv.injective

def address {n W : ℕ} (base : ℕ) (j : Fin n) (offset : Fin W) : ℕ := base + (localAddress j offset).val

theorem address_bounds {n W : ℕ} (base : ℕ) (j : Fin n) (offset : Fin W) :
    base ≤ address base j offset ∧ address base j offset < base + n * W :=
  ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (localAddress j offset).isLt base⟩

theorem address_injective {n W : ℕ} (base : ℕ) :
    Function.Injective (fun p : Fin n × Fin W => address base p.1 p.2) := by
  intro p q hpq
  apply localAddress_injective n W
  apply Fin.ext
  exact Nat.add_left_cancel hpq

theorem address_excludes_frame {n W : ℕ} (base : ℕ) (j : Fin n) (offset : Fin W) (other : ℕ)
    (hOther : other < base ∨ base + n * W ≤ other) : address base j offset ≠ other := by
  have h := address_bounds base j offset
  rcases hOther with hOther | hOther <;> omega

def addressWidth (base n W : ℕ) : ℕ := binaryWordWidth (base + n * W + 1)

theorem address_wordWidth {n W : ℕ} (base : ℕ) (j : Fin n) (offset : Fin W) :
    binaryWordWidth (address base j offset) ≤ addressWidth base n W :=
  binaryWordWidth_mono (by have h := address_bounds base j offset; omega)

theorem address_fits {n W : ℕ} (base : ℕ) (j : Fin n) (offset : Fin W) :
    address base j offset < 2 ^ addressWidth base n W := by
  have hBound := address_bounds base j offset
  exact (show address base j offset ≤ base + n * W + 1 by omega).trans_lt (lt_pow_binaryWordWidth _)

theorem bit_region_size (n W : ℕ) : Fintype.card (Fin n × Fin W) = n * W := by simp

end Blotto.FixedWordRegion
