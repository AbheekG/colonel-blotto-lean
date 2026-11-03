import Blotto.GeneralPaperMeasuredBlockLayout

/-! A measured inner pool and wider outer-record pool share one address
line. The outer start comes from the executed inner cursor. Each pool encodes
references at its own width; their actual blocks are mutually disjoint. -/
namespace Blotto.GeneralPaperMeasuredTwoPoolLayout
open GeneralPaperMeasuredBlockPlan GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

structure Result (A B : ℕ) where
  inner : List (Region A)
  outer : List (Region B)
  boundary : ℕ
  finish : ℕ
  work : ℕ

def run (model : RationalCostModel) (S A B : ℕ) (inner outer : Plan) : Result A B :=
  let first := GeneralPaperMeasuredBlockLayout.run model S A 0 inner
  let second := GeneralPaperMeasuredBlockLayout.run model S B first.2.1 outer
  ⟨first.1,second.1,first.2.1,second.2.1,first.2.2 + second.2.2 + 64 * (S + A + B + 1)⟩

theorem boundary (model : RationalCostModel) (S A B : ℕ) (inner outer : Plan) :
    (run model S A B inner outer).boundary = inner.sizes.sum := by
  dsimp only [run]
  rw [GeneralPaperMeasuredBlockLayout.cursor,Nat.zero_add]

theorem finish (model : RationalCostModel) (S A B : ℕ) (inner outer : Plan) :
    (run model S A B inner outer).finish = inner.sizes.sum + outer.sizes.sum := by
  dsimp only [run]
  rw [GeneralPaperMeasuredBlockLayout.cursor,GeneralPaperMeasuredBlockLayout.cursor,Nat.zero_add]

theorem inner_lengths (model : RationalCostModel) (S A B : ℕ) (inner outer : Plan) :
    (run model S A B inner outer).inner.map Region.length = inner.sizes :=
  GeneralPaperMeasuredBlockLayout.lengths model S A 0 inner

theorem outer_lengths (model : RationalCostModel) (S A B : ℕ) (inner outer : Plan) :
    (run model S A B inner outer).outer.map Region.length = outer.sizes :=
  GeneralPaperMeasuredBlockLayout.lengths model S B _ outer

theorem inner_references (model : RationalCostModel) (S A B : ℕ) (inner outer : Plan)
    (hInner : inner.sizes.sum < 2 ^ A) :
    ∀ r ∈ (run model S A B inner outer).inner,r.reference.value = r.start :=
  GeneralPaperMeasuredBlockLayout.references model S A 0 inner (by omega)

theorem outer_references (model : RationalCostModel) (S A B : ℕ) (inner outer : Plan)
    (hTotal : inner.sizes.sum + outer.sizes.sum < 2 ^ B) :
    ∀ r ∈ (run model S A B inner outer).outer,r.reference.value = r.start := by
  apply GeneralPaperMeasuredBlockLayout.references
  rw [GeneralPaperMeasuredBlockLayout.cursor,Nat.zero_add]
  exact hTotal

theorem disjoint_pools (model : RationalCostModel) (S A B : ℕ) (inner outer : Plan) :
    ∀ r ∈ (run model S A B inner outer).inner,∀ s ∈ (run model S A B inner outer).outer,
      Disjoint (Set.Ico r.start r.stop) (Set.Ico s.start s.stop) := by
  intro r hr s hs
  have hInner := GeneralPaperMeasuredBlockLayout.range model S A 0 inner r hr
  have hOuter := GeneralPaperMeasuredBlockLayout.range model S B
    (GeneralPaperMeasuredBlockLayout.run model S A 0 inner).2.1 outer s hs
  rw [GeneralPaperMeasuredBlockLayout.cursor,Nat.zero_add] at hOuter
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [Set.mem_Ico] at hx hy
  omega

theorem work (model : RationalCostModel) (S A B : ℕ) (inner outer : Plan)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hInner : inner.sizes.sum < 2 ^ A)
    (hTotal : inner.sizes.sum + outer.sizes.sum < 2 ^ B) :
    (run model S A B inner outer).work ≤ inner.work + outer.work +
      (inner.sizes.length + 1) * stepPrice model S A + (outer.sizes.length + 1) * stepPrice model S B +
      192 * (S + A + B + 1) := by
  have hFirst := GeneralPaperMeasuredBlockLayout.work model S A 0 inner hA (by omega)
  have hSecond := GeneralPaperMeasuredBlockLayout.work model S B
    (GeneralPaperMeasuredBlockLayout.run model S A 0 inner).2.1 outer hB (by
      rw [GeneralPaperMeasuredBlockLayout.cursor,Nat.zero_add]
      exact hTotal)
  dsimp only [run]
  omega

end Blotto.GeneralPaperMeasuredTwoPoolLayout
