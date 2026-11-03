import Blotto.BinaryOverlapInputPreparation

/-! Already computed Boolean segment tables supply the actual sixteen-word
overlap environment by selected array reads. No rational frame encoder or Rat
conversion is executed. Refinement to a retained rational parent descriptor is
a proof-only field contract; canonical inputs and extraction prices then follow
from the stored arrays and source heights. The parent controller and physical
allocator/GC remain separate. -/

namespace Blotto.BinaryStoredOverlapEnvironment
open BinaryRationalNormalization BinaryRationalEncoding
open scoped BigOperators

structure Segment (n k : ℕ) where
  weight : FixedArrayTable k SignedWord
  P : FixedArrayTable k (FixedArrayTable n SignedWord)
  Q : FixedArrayTable k (FixedArrayTable n SignedWord)

namespace Segment

def Canonical {n k : ℕ} (segment : Segment n k) : Prop :=
  (∀ i, CanonicalWord (segment.weight.read i)) ∧
    (∀ i r, CanonicalWord ((segment.P.read i).read r)) ∧
    (∀ i r, CanonicalWord ((segment.Q.read i).read r))

def Refines {n k : ℕ} (segment : Segment n k) (source : RationalSegmentLottery n k) : Prop :=
  (∀ i, value (segment.weight.read i) = source.weight i) ∧
    (∀ i r, value ((segment.P.read i).read r) = source.P i r) ∧
    (∀ i r, value ((segment.Q.read i).read r) = source.Q i r)

end Segment

def environment {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) : FixedArrayTable 16 SignedWord :=
  FixedArrayTable.ofFn ![(first.P.read i).read 0, (first.P.read i).read 1, (first.P.read i).read 2,
    (first.Q.read i).read 0, (first.Q.read i).read 1, (first.Q.read i).read 2,
    (second.P.read j).read 0, (second.P.read j).read 1, (second.P.read j).read 2,
    (second.Q.read j).read 0, (second.Q.read j).read 1, (second.Q.read j).read 2,
    first.weight.read i, second.weight.read j, interval, budget]

theorem environment_canonical {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h)
    (hFirst : first.Canonical) (hSecond : second.Canonical)
    (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget) :
    ∀ r, CanonicalWord ((environment first second interval budget i j).read r) := by
  intro r
  fin_cases r <;> simp only [environment, FixedArrayTable.read_ofFn]
  all_goals first | exact hFirst.1 _ | exact hFirst.2.1 _ _ | exact hFirst.2.2 _ _ |
    exact hSecond.1 _ | exact hSecond.2.1 _ _ | exact hSecond.2.2 _ _ | exact hInterval | exact hBudget

theorem environment_value {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (hFirst : first.Refines G.first) (hSecond : second.Refines G.second)
    (hInterval : value interval = G.d) (hBudget : value budget = B) :
    ∀ r, value ((environment first second interval budget i j).read r) =
      (RationalOverlapFormula.environment G B i j).read r := by
  intro r
  unfold environment RationalOverlapFormula.environment
  rw [FixedArrayTable.read_ofFn, FixedArrayTable.read_ofFn]
  fin_cases r
  · change value ((first.P.read i).read 0) = G.first.P i 0; exact hFirst.2.1 i 0
  · change value ((first.P.read i).read 1) = G.first.P i 1; exact hFirst.2.1 i 1
  · change value ((first.P.read i).read 2) = G.first.P i 2; exact hFirst.2.1 i 2
  · change value ((first.Q.read i).read 0) = G.first.Q i 0; exact hFirst.2.2 i 0
  · change value ((first.Q.read i).read 1) = G.first.Q i 1; exact hFirst.2.2 i 1
  · change value ((first.Q.read i).read 2) = G.first.Q i 2; exact hFirst.2.2 i 2
  · change value ((second.P.read j).read 0) = G.second.P j 0; exact hSecond.2.1 j 0
  · change value ((second.P.read j).read 1) = G.second.P j 1; exact hSecond.2.1 j 1
  · change value ((second.P.read j).read 2) = G.second.P j 2; exact hSecond.2.1 j 2
  · change value ((second.Q.read j).read 0) = G.second.Q j 0; exact hSecond.2.2 j 0
  · change value ((second.Q.read j).read 1) = G.second.Q j 1; exact hSecond.2.2 j 1
  · change value ((second.Q.read j).read 2) = G.second.Q j 2; exact hSecond.2.2 j 2
  · change value (first.weight.read i) = G.first.weight i; exact hFirst.1 i
  · change value (second.weight.read j) = G.second.weight j; exact hSecond.1 j
  · change value interval = G.d; exact hInterval
  · change value budget = B; exact hBudget

theorem environment_refines {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (hFirst : first.Refines G.first) (hSecond : second.Refines G.second)
    (hInterval : value interval = G.d) (hBudget : value budget = B) :
    BinaryRationalExpression.interpretedEnvironment (environment first second interval budget i j) =
      RationalOverlapFormula.environment G B i j := by
  apply BinaryOverlapInputPreparation.table_ext
  intro r
  rw [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn]
  exact environment_value first second interval budget G B i j hFirst hSecond hInterval hBudget r

-- Four selected row-array reads, fourteen selected field reads, sixteen copied
-- signed-word payloads and the emitted sixteen-entry environment array.
def extractionWork {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) : ℕ :=
  64 + 2 * BinaryRationalExpression.environmentPayload (environment first second interval budget i j)

def environmentWithWork {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) : FixedArrayTable 16 SignedWord × ℕ :=
  (environment first second interval budget i j, extractionWork first second interval budget i j)

theorem extractionWork_bound {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) (s : ℕ)
    (hCanonical : ∀ r, CanonicalWord ((environment first second interval budget i j).read r))
    (hHeight : ∀ r, RationalHeight (value ((environment first second interval budget i j).read r)) s) :
    extractionWork first second interval budget i j ≤ 64 + 32 * (4 * s + 3) := by
  have hp := BinaryRationalExpression.environmentPayload_bound (environment first second interval budget i j) s hCanonical hHeight
  unfold extractionWork
  omega

theorem source_environment_height {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (hFirst : first.Refines G.first) (hSecond : second.Refines G.second)
    (hInterval : value interval = G.d) (hBudget : value budget = B)
    (s : ℕ) (hFirstHeight : G.first.HeightAt s) (hSecondHeight : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    ∀ r, RationalHeight (value ((environment first second interval budget i j).read r)) s := by
  have hi := environment_refines first second interval budget G B i j hFirst hSecond hInterval hBudget
  intro r
  have hh := RationalOverlapFormula.environment_height G B i j s hFirstHeight hSecondHeight hD hB r
  rw [← hi] at hh
  simpa only [BinaryRationalExpression.interpretedEnvironment, FixedArrayTable.read_ofFn] using hh

theorem stored_overlap_contract {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (hFirstCanonical : first.Canonical) (hSecondCanonical : second.Canonical)
    (hIntervalCanonical : CanonicalWord interval) (hBudgetCanonical : CanonicalWord budget)
    (hFirst : first.Refines G.first) (hSecond : second.Refines G.second)
    (hInterval : value interval = G.d) (hBudget : value budget = B)
    (s : ℕ) (hs : 2 ≤ s) (hFirstHeight : G.first.HeightAt s) (hSecondHeight : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    let env := environment first second interval budget i j
    value (BinaryOverlapCompilerBridge.weight.compile.runWithWorkspace env).1.1 = G.weight i j ∧
      (∀ r, value ((BinaryOverlapCompilerBridge.safeP r).compile.runWithWorkspace env).1.1 = G.safeP B i j r) ∧
      (∀ r, value ((BinaryOverlapCompilerBridge.safeQ r).compile.runWithWorkspace env).1.1 = G.safeQ B i j r) ∧
      extractionWork first second interval budget i j ≤ 64 + 32 * (4 * s + 3) ∧
      BinaryOverlapCompilerBridge.weight.compile.evaluationStorageWithWorkspace env ≤ BinaryOverlapCompilerBridge.weightStorageBound s ∧
      (∀ r, (BinaryOverlapCompilerBridge.safeP r).compile.evaluationStorageWithWorkspace env ≤ BinaryOverlapCompilerBridge.endpointStorageBound s) ∧
      (∀ r, (BinaryOverlapCompilerBridge.safeQ r).compile.evaluationStorageWithWorkspace env ≤ BinaryOverlapCompilerBridge.endpointStorageBound s) := by
  have hc := environment_canonical first second interval budget i j hFirstCanonical hSecondCanonical hIntervalCanonical hBudgetCanonical
  have hi := environment_refines first second interval budget G B i j hFirst hSecond hInterval hBudget
  have hh := source_environment_height first second interval budget G B i j hFirst hSecond hInterval hBudget s hFirstHeight hSecondHeight hD hB
  have he := BinaryOverlapCompilerBridge.gluing_workspace_contract G B i j _ hc hi s hs hFirstHeight hSecondHeight hD hB
  exact ⟨he.1, he.2.1, he.2.2.1, extractionWork_bound first second interval budget i j s hc hh,
    he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩

def compileDescriptor {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) : Segment 4 (k * h) where
  weight := FixedArrayTable.ofFn (fun slot =>
    let pair := finProdFinEquiv.symm slot
    (BinaryOverlapCompilerBridge.weight.compile.run (environment first second interval budget pair.1 pair.2)).1)
  P := FixedArrayTable.ofFn (fun slot =>
    let pair := finProdFinEquiv.symm slot
    FixedArrayTable.ofFn (fun r => ((BinaryOverlapCompilerBridge.safeP r).compile.run
      (environment first second interval budget pair.1 pair.2)).1))
  Q := FixedArrayTable.ofFn (fun slot =>
    let pair := finProdFinEquiv.symm slot
    FixedArrayTable.ofFn (fun r => ((BinaryOverlapCompilerBridge.safeQ r).compile.run
      (environment first second interval budget pair.1 pair.2)).1))

theorem compileDescriptor_canonical {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (hFirst : first.Canonical) (hSecond : second.Canonical)
    (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget) :
    (compileDescriptor first second interval budget).Canonical := by
  constructor
  · intro slot
    simp only [compileDescriptor, FixedArrayTable.read_ofFn]
    exact (BinaryOverlapCompilerBridge.compiled_canonical_outputs _
      (environment_canonical first second interval budget _ _ hFirst hSecond hInterval hBudget)).1
  · constructor
    · intro slot r
      simp only [compileDescriptor, FixedArrayTable.read_ofFn]
      exact (BinaryOverlapCompilerBridge.compiled_canonical_outputs _
        (environment_canonical first second interval budget _ _ hFirst hSecond hInterval hBudget)).2.1 r
    · intro slot r
      simp only [compileDescriptor, FixedArrayTable.read_ofFn]
      exact (BinaryOverlapCompilerBridge.compiled_canonical_outputs _
        (environment_canonical first second interval budget _ _ hFirst hSecond hInterval hBudget)).2.2 r

theorem compileDescriptor_refines {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (G : RationalOverlapGluing k h) (B : ℚ)
    (hFirstCanonical : first.Canonical) (hSecondCanonical : second.Canonical)
    (hIntervalCanonical : CanonicalWord interval) (hBudgetCanonical : CanonicalWord budget)
    (hFirst : first.Refines G.first) (hSecond : second.Refines G.second)
    (hInterval : value interval = G.d) (hBudget : value budget = B) :
    (compileDescriptor first second interval budget).Refines (RationalOverlapFormula.descriptor G B) := by
  rw [RationalOverlapFormula.descriptor_eq]
  have hSlot : ∀ i j,
      value (BinaryOverlapCompilerBridge.weight.compile.run (environment first second interval budget i j)).1 = G.weight i j ∧
      (∀ r, value ((BinaryOverlapCompilerBridge.safeP r).compile.run (environment first second interval budget i j)).1 = G.safeP B i j r) ∧
      (∀ r, value ((BinaryOverlapCompilerBridge.safeQ r).compile.run (environment first second interval budget i j)).1 = G.safeQ B i j r) := by
    intro i j
    exact BinaryOverlapCompilerBridge.gluing_values G B i j _
      (fun r => (environment_canonical first second interval budget i j hFirstCanonical hSecondCanonical hIntervalCanonical hBudgetCanonical r).1)
      (environment_refines first second interval budget G B i j hFirst hSecond hInterval hBudget)
  constructor
  · intro slot
    simp only [compileDescriptor, FixedArrayTable.read_ofFn, RationalOverlapGluing.descriptor]
    exact (hSlot _ _).1
  · constructor
    · intro slot r
      simp only [compileDescriptor, FixedArrayTable.read_ofFn, RationalOverlapGluing.descriptor]
      exact (hSlot _ _).2.1 r
    · intro slot r
      simp only [compileDescriptor, FixedArrayTable.read_ofFn, RationalOverlapGluing.descriptor]
      exact (hSlot _ _).2.2 r

-- The separate weight/P/Q table passes each construct their selected sixteen
-- word environment; all nine constructions per slot are charged explicitly.
def slotWork {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) : ℕ :=
  let env := environment first second interval budget i j
  9 * extractionWork first second interval budget i j +
    BinaryOverlapCompilerBridge.weight.compile.bitWork env +
    (∑ r : Fin 4, (BinaryOverlapCompilerBridge.safeP r).compile.bitWork env) +
    (∑ r : Fin 4, (BinaryOverlapCompilerBridge.safeQ r).compile.bitWork env) + 13088

def compileDescriptorWork {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) : ℕ :=
  (∑ slot : Fin (k * h),
    slotWork first second interval budget (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2) +
    6 * (k * h) + 3

def compileDescriptorWithWork {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) : Segment 4 (k * h) × ℕ :=
  (compileDescriptor first second interval budget, compileDescriptorWork first second interval budget)

theorem slotWork_bound {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h)
    (hFirstCanonical : first.Canonical) (hSecondCanonical : second.Canonical)
    (hIntervalCanonical : CanonicalWord interval) (hBudgetCanonical : CanonicalWord budget)
    (hFirst : first.Refines G.first) (hSecond : second.Refines G.second)
    (hInterval : value interval = G.d) (hBudget : value budget = B)
    (s : ℕ) (hs : 2 ≤ s) (hFirstHeight : G.first.HeightAt s) (hSecondHeight : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    slotWork first second interval budget i j ≤
      9 * (64 + 32 * (4 * s + 3)) + BinaryOverlapInputPreparation.evaluationWorkBound s + 13088 := by
  have hc := environment_canonical first second interval budget i j hFirstCanonical hSecondCanonical hIntervalCanonical hBudgetCanonical
  have hh := source_environment_height first second interval budget G B i j hFirst hSecond hInterval hBudget s hFirstHeight hSecondHeight hD hB
  have hx := extractionWork_bound first second interval budget i j s hc hh
  have he := BinaryOverlapCompilerBridge.compiled_bitWork _ hc s hs hh
  have hp : (∑ r : Fin 4, (BinaryOverlapCompilerBridge.safeP r).compile.bitWork
      (environment first second interval budget i j)) ≤ 4 * (256 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 9)) := by
    exact (Finset.sum_le_sum (fun r _ => he.2.1 r)).trans_eq (by simp)
  have hq : (∑ r : Fin 4, (BinaryOverlapCompilerBridge.safeQ r).compile.bitWork
      (environment first second interval budget i j)) ≤ 4 * (256 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 9)) := by
    exact (Finset.sum_le_sum (fun r _ => he.2.2 r)).trans_eq (by simp)
  unfold slotWork BinaryOverlapInputPreparation.evaluationWorkBound
  dsimp only
  omega

theorem compileDescriptorWork_bound {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (G : RationalOverlapGluing k h) (B : ℚ)
    (hFirstCanonical : first.Canonical) (hSecondCanonical : second.Canonical)
    (hIntervalCanonical : CanonicalWord interval) (hBudgetCanonical : CanonicalWord budget)
    (hFirst : first.Refines G.first) (hSecond : second.Refines G.second)
    (hInterval : value interval = G.d) (hBudget : value budget = B)
    (s : ℕ) (hs : 2 ≤ s) (hFirstHeight : G.first.HeightAt s) (hSecondHeight : G.second.HeightAt s)
    (hD : RationalHeight G.d s) (hB : RationalHeight B s) :
    compileDescriptorWork first second interval budget ≤
      (k * h) * (9 * (64 + 32 * (4 * s + 3)) + BinaryOverlapInputPreparation.evaluationWorkBound s + 13094) + 3 := by
  have he : (∑ slot : Fin (k * h), slotWork first second interval budget
      (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2) ≤
      (k * h) * (9 * (64 + 32 * (4 * s + 3)) + BinaryOverlapInputPreparation.evaluationWorkBound s + 13088) := by
    exact (Finset.sum_le_sum (fun slot _ => slotWork_bound first second interval budget G B _ _
      hFirstCanonical hSecondCanonical hIntervalCanonical hBudgetCanonical hFirst hSecond hInterval hBudget
      s hs hFirstHeight hSecondHeight hD hB)).trans_eq (by simp)
  unfold compileDescriptorWork
  nlinarith

end Blotto.BinaryStoredOverlapEnvironment
