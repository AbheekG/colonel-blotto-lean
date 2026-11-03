import Blotto.CachedGroupRoutes

/-! Prepared routing tables store the labels and coefficients for emission.
The small sampled group vector is materialized once before the output-array
pass, which reads only cached values. The pivot is copied in that same pass. -/

namespace Blotto

namespace RationalProportionalGroups

def emitMixed {n m : ℕ} (_G : RationalProportionalGroups n m) (table : FixedArrayTable n (GroupRoute m))
    (pivot : Fin n) (y : Fin (m + 1) → ℚ) : RationalResourceArray n :=
  RationalResourceArray.ofAllocation (fun j =>
    (let r := table.read j
     match r.1 with
     | none => 0
     | some g => r.2 * y g.castSucc) + if j = pivot then y (Fin.last m) else 0)

theorem emitMixed_allocation_add {n m : ℕ} (G : RationalProportionalGroups n m)
    (table : FixedArrayTable n (GroupRoute m)) (pivot : Fin n) (y : Fin (m + 1) → ℚ) (j : Fin n) :
    (G.emitMixed table pivot y).allocation j =
      (G.emit table (fun g => y g.castSucc)).allocation j + if j = pivot then y (Fin.last m) else 0 := by
  simp only [emitMixed, emit, RationalResourceArray.allocation_ofAllocation]
  cases (table.read j).1 <;> rfl

theorem emitMixed_real {n m : ℕ} (G : RationalProportionalGroups n m) (pivot : Fin n)
    (y : Fin (m + 1) → ℚ) :
    (G.emitMixed G.routes pivot y).realAllocation = G.real.splitMixed pivot (fun g => (y g : ℝ)) := by
  funext j
  have he := congrFun (G.emit_real (fun g => y g.castSucc)) j
  change ((G.emit G.routes (fun g => y g.castSucc)).allocation j : ℝ) = _ at he
  change ((G.emitMixed G.routes pivot y).allocation j : ℝ) = _
  rw [G.emitMixed_allocation_add, Rat.cast_add, he]
  by_cases hj : j = pivot <;> simp [ProportionalGroups.splitMixed, hj]

theorem emitMixed_fullBudget {n m : ℕ} (G : RationalProportionalGroups n m) (pivot : Fin n)
    {B : ℚ} {y : Fin (m + 1) → ℚ} (hy : FullBudget (B : ℝ) (fun g => (y g : ℝ))) :
    FullBudget (B : ℝ) (G.emitMixed G.routes pivot y).realAllocation := by
  rw [G.emitMixed_real]
  exact G.real.splitMixed_fullBudget pivot hy

end RationalProportionalGroups

structure PreparedGroupOutput {n m : ℕ} (G : RationalProportionalGroups n m) where
  table : FixedArrayTable n (GroupRoute m)
  correct : ∀ j, table.read j = G.routes.read j

namespace PreparedGroupOutput

def prepare {n m : ℕ} (G : RationalProportionalGroups n m) : PreparedGroupOutput G :=
  ⟨G.routes, fun _ => rfl⟩

def emit {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (y : Fin m → ℚ) : RationalResourceArray n :=
  let sampled := FixedArrayTable.ofFn y
  G.emit p.table sampled.read

def emitMixed {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (pivot : Fin n) (y : Fin (m + 1) → ℚ) : RationalResourceArray n :=
  let sampled := FixedArrayTable.ofFn y
  G.emitMixed p.table pivot sampled.read

theorem emit_allocation {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (y : Fin m → ℚ) : (p.emit y).allocation = (G.emit G.routes y).allocation := by
  funext j
  simp only [emit, RationalProportionalGroups.emit, RationalResourceArray.allocation_ofAllocation,
    FixedArrayTable.read_ofFn, p.correct]

theorem emitMixed_allocation {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (pivot : Fin n) (y : Fin (m + 1) → ℚ) :
    (p.emitMixed pivot y).allocation = (G.emitMixed G.routes pivot y).allocation := by
  funext j
  simp only [emitMixed, RationalProportionalGroups.emitMixed, RationalResourceArray.allocation_ofAllocation,
    FixedArrayTable.read_ofFn, p.correct]

theorem emit_real {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G) (y : Fin m → ℚ) :
    (p.emit y).realAllocation = G.real.split (fun g => (y g : ℝ)) := by
  change (fun j => ((p.emit y).allocation j : ℝ)) = _
  rw [p.emit_allocation]
  exact G.emit_real y

theorem emitMixed_real {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (pivot : Fin n) (y : Fin (m + 1) → ℚ) :
    (p.emitMixed pivot y).realAllocation = G.real.splitMixed pivot (fun g => (y g : ℝ)) := by
  change (fun j => ((p.emitMixed pivot y).allocation j : ℝ)) = _
  rw [p.emitMixed_allocation]
  exact G.emitMixed_real pivot y

theorem emit_fullBudget {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    {B : ℚ} {y : Fin m → ℚ} (hy : FullBudget (B : ℝ) (fun g => (y g : ℝ))) :
    FullBudget (B : ℝ) (p.emit y).realAllocation := by
  rw [p.emit_real]
  exact G.real.split_fullBudget hy

theorem emitMixed_fullBudget {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (pivot : Fin n) {B : ℚ} {y : Fin (m + 1) → ℚ} (hy : FullBudget (B : ℝ) (fun g => (y g : ℝ))) :
    FullBudget (B : ℝ) (p.emitMixed pivot y).realAllocation := by
  rw [p.emitMixed_real]
  exact G.real.splitMixed_fullBudget pivot hy

end PreparedGroupOutput
end Blotto
