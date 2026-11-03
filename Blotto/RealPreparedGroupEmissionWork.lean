import Blotto.RealCachedGroupOutput

/-! Unit-price exact-real emission counts available scalar reads/writes and
arithmetic primitives in the cached coordinate pass. Group-vector production,
route preparation, address/tag representation, physical allocation and ownership
remain separate. These labels are a real-RAM component contract. -/

namespace Blotto.RealPreparedGroupOutput
open scoped BigOperators

noncomputable def routedValue {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G)
    (y : Allocation m) (j : Fin n) : ℝ :=
  match (p.table.read j).1 with
  | none => 0
  | some g => (p.table.read j).2 * y g

theorem routedValue_eq {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G)
    (y : Allocation m) (j : Fin n) : p.routedValue y j = (p.emit y).read j := by
  simp only [routedValue, emit, FixedArrayTable.read_ofFn]
  rfl

def routedArithmeticWork {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G) (j : Fin n) : ℕ :=
  match (p.table.read j).1 with
  | none => 0
  | some _ => 1

def emitArithmeticWork {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G) : ℕ :=
  ∑ j, p.routedArithmeticWork j

theorem emitArithmeticWork_bound {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G) :
    p.emitArithmeticWork ≤ n := by
  have h : ∀ j, p.routedArithmeticWork j ≤ 1 := by
    intro j
    unfold routedArithmeticWork
    split <;> omega
  calc
    _ ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

def emitMixedArithmeticWork {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G) : ℕ :=
  ∑ j, (p.routedArithmeticWork j + 1)

theorem emitMixedArithmeticWork_bound {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G) :
    p.emitMixedArithmeticWork ≤ 2 * n := by
  unfold emitMixedArithmeticWork
  rw [Finset.sum_add_distrib]
  have h := p.emitArithmeticWork_bound
  change (∑ j, p.routedArithmeticWork j) ≤ n at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]
  omega

-- One route read (two fields), a branch, an output store, and either a zero
-- literal or coefficient/sample reads plus multiplication.
def routedScalarWork {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G) (j : Fin n) : ℕ :=
  2 + 1 + 1 + match (p.table.read j).1 with
    | none => 1
    | some _ => 1 + 1 + 1

def emitScalarWork {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G) : ℕ :=
  2 * m + ∑ j, p.routedScalarWork j

theorem emitScalarWork_bound {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G) :
    p.emitScalarWork ≤ 2 * m + 7 * n := by
  have h : ∀ j, p.routedScalarWork j ≤ 7 := by
    intro j
    unfold routedScalarWork
    split <;> norm_num
  have hp : (∑ j, p.routedScalarWork j) ≤ 7 * n := by
    calc
      _ ≤ ∑ _j : Fin n, 7 := Finset.sum_le_sum (fun j _ => h j)
      _ = _ := by simp [Nat.mul_comm]
  unfold emitScalarWork
  omega

-- The mixed pass also compares the pivot, reads or creates the extra scalar,
-- and adds it. Four additional unit labels allow either branch.
def emitMixedScalarWork {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G) : ℕ :=
  2 * (m + 1) + ∑ j, (p.routedScalarWork j + 4)

theorem emitMixedScalarWork_bound {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G) :
    p.emitMixedScalarWork ≤ 2 * (m + 1) + 11 * n := by
  have hp := p.emitScalarWork_bound
  unfold emitMixedScalarWork emitScalarWork at *
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

end Blotto.RealPreparedGroupOutput
