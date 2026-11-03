import Blotto.GeneralPaperMeasuredListPlanLifetime

/-! Actual route, Boolean-word and labelled-row size constructors. All
child lifetime conditions are derived compositionally from their executed
plans. No component scratch/space bound is supplied by a caller. Full
array/prepared-cache and enclosing native capacity joins remain separate. -/
namespace Blotto.GeneralPaperMeasuredLeafRecordLifetime
open GeneralPaperMeasuredBlockPlan (Plan)
open GeneralPaperEqualMeasuredLeafPlans
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperMeasuredScalarPlanLifetime
open GeneralPaperMeasuredRecordPlanLifetime
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem reserve_good (model : RationalCostModel) (S A arity : ℕ) (hA : 0 < A)
    (hArity : 0 < arity) (hArity64 : arity ≤ 64) :
    Good model S A 4 (reserve model S A arity) (referencesWindow model S A 0 0 arity) := by
  have hw := binaryWordWidth_mono hArity64
  have h64 : binaryWordWidth 64 = 7 := by decide
  exact references_good model S A 0 0 arity hA (by simpa only [Nat.mul_zero,Nat.zero_add] using Nat.mul_pos hA hArity)
    (by change 1 ≤ A + 8; omega) (by change 1 ≤ A + 8; omega) (by omega)

def labelWindow {m : ℕ} (model : RationalCostModel) (S : ℕ) : Option (Fin m) → ℕ
  | none => constantWindow S (empty S)
  | some g => naturalWindow model S g.val

def labelPlan {m : ℕ} (model : RationalCostModel) (S : ℕ) : Option (Fin m) → Plan
  | none => empty S
  | some g => GeneralPaperMeasuredBlockPlan.natural model S g.val

theorem label_good {m : ℕ} (model : RationalCostModel) (S A : ℕ) (label : Option (Fin m)) (hA : 0 < A) :
    Good model S A 4 (labelPlan model S label) (labelWindow model S label) := by
  cases label with
  | none => exact mono model S A 2 4 _ _ (empty_good model S A hA) (by decide)
  | some g => exact natural_good model S A g.val hA

def routeWindow {m : ℕ} (model : RationalCostModel) (S A : ℕ) (x : GroupRoute m) : ℕ :=
  sequenceWindow S A [(tag S,constantWindow S (tag S)),(labelPlan model S x.1,labelWindow model S x.1),
    (GeneralPaperMeasuredBlockPlan.rational model S x.2,rationalWindow model S x.2),
    (reserve model S A 16,referencesWindow model S A 0 0 16)]

theorem route_good {m : ℕ} (model : RationalCostModel) (S A : ℕ) (x : GroupRoute m) (hA : 0 < A) :
    Good model S A 50 (route model S A x) (routeWindow model S A x) := by
  have h := sequence_good model S A 4
    [(tag S,constantWindow S (tag S)),(labelPlan model S x.1,labelWindow model S x.1),
      (GeneralPaperMeasuredBlockPlan.rational model S x.2,rationalWindow model S x.2),
      (reserve model S A 16,referencesWindow model S A 0 0 16)] hA (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl
    · exact mono model S A 2 4 _ _ (tag_good model S A hA) (by decide)
    · exact label_good model S A x.1 hA
    · exact rational_good model S A x.2 hA
    · exact reserve_good model S A 16 hA (by decide) (by decide))
  cases x with
  | mk label coefficient =>
    cases label <;>
      simpa only [route,routeWindow,labelPlan,labelWindow,List.map_cons,List.map_nil,List.length_cons,List.length_nil,
        Nat.reduceAdd,Nat.reduceMul] using h

def wordWindow {w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : FixedBinaryWord w) : ℕ :=
  joinWindow S A (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (bit S) x.bits) (reserve model S A 16)
    (GeneralPaperMeasuredListPlanLifetime.window model S A 2 32 (bit S) (fun b => constantWindow S (bit S b)) x.bits)
    (referencesWindow model S A 0 0 16)

theorem word_good {w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : FixedBinaryWord w) (hA : 0 < A) :
    Good model S A 38 (word model S A x) (wordWindow model S A x) := by
  have hList := GeneralPaperMeasuredListPlanLifetime.run_good model S A 2 2 32 (bit S)
    (fun b => constantWindow S (bit S b)) x.bits hA (by decide) (by decide) (by decide) (by decide)
    (fun _ _ => tag_good model S A hA)
  exact join_good model S A 26 4 _ _ _ _ hA hList (reserve_good model S A 16 hA (by decide) (by decide))

def rowWindow {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : Fin r × FixedBinaryWord w) : ℕ :=
  sequenceWindow S A [(GeneralPaperMeasuredBlockPlan.natural model S x.1.val,naturalWindow model S x.1.val),
    (word model S A x.2,wordWindow model S A x.2),(reserve model S A 16,referencesWindow model S A 0 0 16)]

theorem row_good {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (x : Fin r × FixedBinaryWord w) (hA : 0 < A) :
    Good model S A 140 (row model S A x) (rowWindow model S A x) := by
  have h := sequence_good model S A 38
    [(GeneralPaperMeasuredBlockPlan.natural model S x.1.val,naturalWindow model S x.1.val),
      (word model S A x.2,wordWindow model S A x.2),(reserve model S A 16,referencesWindow model S A 0 0 16)] hA (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · exact mono model S A 4 38 _ _ (natural_good model S A x.1.val hA) (by decide)
    · exact word_good model S A x.2 hA
    · exact mono model S A 4 38 _ _ (reserve_good model S A 16 hA (by decide) (by decide)) (by decide))
  simpa only [row,rowWindow,List.map_cons,List.map_nil,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul] using h

end Blotto.GeneralPaperMeasuredLeafRecordLifetime
