import Blotto.ImplicitLeafCounts
import Blotto.CumulativeGuideLogSize

/-! Expanded positive blocks have a logarithmic mass range. The last theorem
instantiates the weight bounds with the actual stored-rounded field history;
block/history correspondence is explicit until the sparse block updater is
connected. No minimum-weight oracle or numerical code enumeration is executed. -/

namespace Blotto.ImplicitLeafCounts
open scoped BigOperators Classical

theorem partition_labelMass_bounds (C : ℕ) (blocks : List Block)
    (hp : Partition C blocks) (lower upper : ℚ)
    (hw : ∀ block ∈ blocks, lower ≤ block.weight ∧ block.weight ≤ upper)
    (code : Fin (C + 1)) : lower ≤ labelMass blocks code.val ∧ labelMass blocks code.val ≤ upper := by
  rcases coversFrom_unique_weight C 0 blocks hp code.val ⟨Nat.zero_le _, by omega⟩ with
    ⟨block, hb, _, he⟩
  rw [he]
  exact hw block hb

theorem partition_totalMass_labels (C : ℕ) (blocks : List Block) (hp : Partition C blocks) :
    totalMass blocks = ∑ code : Fin (C + 1), labelMass blocks code.val := by
  rw [← partition_prefixMass_full C blocks hp (C : ℤ) le_rfl,
    partition_prefixMass_labels C blocks hp]
  apply Finset.sum_congr rfl
  intro code _
  have hc : (code.val : ℤ) ≤ (C : ℤ) := by omega
  rw [ite_eq_left hc]

theorem partition_totalMass_upper (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (upper : ℚ) (hw : ∀ block ∈ blocks, block.weight ≤ upper) :
    totalMass blocks ≤ ((C + 1 : ℕ) : ℚ) * upper := by
  rw [partition_totalMass_labels C blocks hp]
  calc
    (∑ code : Fin (C + 1), labelMass blocks code.val) ≤ ∑ _code : Fin (C + 1), upper := by
      apply Finset.sum_le_sum
      intro code _
      rcases coversFrom_unique_weight C 0 blocks hp code.val ⟨Nat.zero_le _, by omega⟩ with
        ⟨block, hb, _, he⟩
      rw [he]
      exact hw block hb
    _ = ((C + 1 : ℕ) : ℚ) * upper := by simp

theorem partition_prefix_zero (C : ℕ) (blocks : List Block) (hp : Partition C blocks) :
    prefixMass blocks 0 = labelMass blocks 0 := by
  rw [partition_prefixMass_labels C blocks hp]
  have he : (fun code : Fin (C + 1) =>
      if (code.val : ℤ) ≤ 0 then labelMass blocks code.val else 0) =
      (fun code => if code = (⟨0, by omega⟩ : Fin (C + 1)) then labelMass blocks 0 else 0) := by
    funext code
    by_cases hc : code.val = 0
    · have heq : code = (⟨0, by omega⟩ : Fin (C + 1)) := Fin.ext hc
      simp [heq]
    · have heq : code ≠ (⟨0, by omega⟩ : Fin (C + 1)) := by intro heq; exact hc (congrArg Fin.val heq)
      simp only [show ¬(code.val : ℤ) ≤ 0 by omega, heq, ite_false]
  rw [he]
  apply Finset.sum_eq_single (⟨0, by omega⟩ : Fin (C + 1))
  · intro code _ hc
    rw [ite_eq_right hc]
  · intro hc
    exact False.elim (hc (Finset.mem_univ _))

theorem partition_log_range (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (hw : Positive blocks) (decay : ℝ)
    (hl : Real.exp (-decay) ≤ (prefixMass blocks 0 : ℝ))
    (hu : totalMass blocks ≤ ((C + 1 : ℕ) : ℚ)) :
    Real.log ((totalMass blocks : ℝ) / (prefixMass blocks 0 : ℝ)) ≤
      Real.log ((C + 1 : ℕ) : ℝ) + decay := by
  have hf : (0 : ℝ) < prefixMass blocks 0 := by
    exact_mod_cast partition_prefixMass_positive C blocks hp hw 0 le_rfl
  have ht : (0 : ℝ) < totalMass blocks := by
    rw [← partition_prefixMass_full C blocks hp (C : ℤ) le_rfl]
    exact_mod_cast partition_prefixMass_positive C blocks hp hw (C : ℤ) (by omega)
  have hC : (0 : ℝ) < ((C + 1 : ℕ) : ℝ) := by positivity
  have huR : (totalMass blocks : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by exact_mod_cast hu
  have hratio : (totalMass blocks : ℝ) / (prefixMass blocks 0 : ℝ) ≤
      ((C + 1 : ℕ) : ℝ) / Real.exp (-decay) :=
    div_le_div₀ hC.le huR (Real.exp_pos _) hl
  have hlog := Real.log_le_log (div_pos ht hf) hratio
  rw [Real.log_div hC.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  linarith

theorem rounded_history_log_range {a m : ℕ} {sizes : Fin m → ℕ}
    (selected : List (Fin a) → Fin a → Fin m)
    (localLoss : (h : List (Fin a)) → (x : Fin a) → Fin (sizes (selected h x)) → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2)
    (hl : ∀ h x code, 0 ≤ localLoss h x code ∧ localLoss h x code ≤ 1)
    (past : List (Fin a)) (field : Fin m) (C : ℕ) (hs : sizes field = C + 1)
    (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (he : ∀ code : Fin (C + 1), labelMass blocks code.val =
      SparseMW.roundedFieldHistory selected localLoss eta theta past field (code.cast hs.symm)) :
    Real.log ((totalMass blocks : ℝ) / (prefixMass blocks 0 : ℝ)) ≤
      Real.log ((C + 1 : ℕ) : ℝ) +
        (SparseMW.fieldUpdateCount selected past field : ℝ) * ((eta : ℝ) + 3 * (theta : ℝ)) := by
  apply partition_log_range C blocks hp hw
  · rw [partition_prefix_zero C blocks hp, he ⟨0, by omega⟩]
    convert SparseMW.roundedFieldHistory_exp_lower selected localLoss eta theta heta ht hl past field
      ((⟨0, by omega⟩ : Fin (C + 1)).cast hs.symm) using 1
    congr 1
    ring
  · rw [partition_totalMass_labels C blocks hp]
    calc
      (∑ code : Fin (C + 1), labelMass blocks code.val) ≤ ∑ _code : Fin (C + 1), (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro code _
        rw [he code]
        exact SparseMW.roundedFieldHistory_le_one selected localLoss eta theta heta ht hl past field _
      _ = ((C + 1 : ℕ) : ℚ) := by simp

end Blotto.ImplicitLeafCounts
