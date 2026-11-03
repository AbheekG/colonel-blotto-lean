import Blotto.GeneralPaperRayAffineMinimum

/-! On a refined open bracket, every predecessor comparison is fixed.
The affine minimum selected at one interior point is therefore exactly
the executed minimum at every other interior point, including stable
choices between identically equal candidates.
-/
namespace Blotto.GeneralPaperRayStableMinimum
open GeneralPaperRayAffine GeneralPaperRayAffineComparison GeneralPaperRayAffineMinimum
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem scan_stable {i : Type*} {K : ℕ} (options : i → Option (Choice K)) (xs : List i) (sample t : ℚ)
    (hCompare : ∀ i∈xs,∀ j∈xs,∀ a b,options i=some a → options j=some b →
      (a.expression.value sample≤b.expression.value sample ↔ a.expression.value t≤b.expression.value t)) :
    scan sample options xs=scan t options xs := by
  induction xs with
  | nil => rfl
  | cons i rest ih =>
    have hr := ih (fun a ha b hb f g hf hg => hCompare a (List.mem_cons_of_mem _ ha) b
      (List.mem_cons_of_mem _ hb) f g hf hg)
    rw [scan,scan,←hr]
    cases hi : options i with
    | none => rfl
    | some a =>
      cases he : scan sample options rest with
      | none => rfl
      | some b =>
        obtain ⟨j,hj,hb⟩ := scan_origin sample options rest b he
        have hc := hCompare i List.mem_cons_self j (List.mem_cons_of_mem _ hj) a b hi hb
        change (if a.expression.value sample≤b.expression.value sample then some a else some b)=
          (if a.expression.value t≤b.expression.value t then some a else some b)
        by_cases hs : a.expression.value sample≤b.expression.value sample
        · rw [ite_eq_left hs,ite_eq_left (hc.mp hs)]
        · rw [ite_eq_right hs,ite_eq_right (fun ht => hs (hc.mpr ht))]

theorem no_crossing_stable {i : Type*} {K : ℕ} (options : i → Option (Choice K)) (xs : List i)
    (lo hi sample t : ℚ) (hSample : lo<sample ∧ sample<hi) (ht : lo<t ∧ t<hi)
    (hNoCross : ∀ i∈xs,∀ j∈xs,∀ a b,options i=some a → options j=some b →
      a.expression.slope≠b.expression.slope →
        ¬(lo<(difference a.expression b.expression).crossing ∧ (difference a.expression b.expression).crossing<hi)) :
    scan sample options xs=scan t options xs := by
  apply scan_stable
  intro i hiMem j hjMem a b ha hb
  exact ⟨stable_order a.expression b.expression lo hi sample t hSample ht (hNoCross i hiMem j hjMem a b ha hb),
    stable_order a.expression b.expression lo hi t sample ht hSample (hNoCross i hiMem j hjMem a b ha hb)⟩

def expressions {S K : ℕ} (options : Fin (S+1) → Fin K → Option (Choice K)) : Fin (S+1) → Fin K → Option Affine :=
  fun s l => (options s l).map Choice.expression

theorem batch_stable {S K : ℕ} (options : Fin (S+1) → Fin K → Option (Choice K))
    (lo hi sample t : ℚ) (hSample : lo<sample ∧ sample<hi) (ht : lo<t ∧ t<hi)
    (hNoCross : ∀ c∈GeneralPaperRayCrossingPairs.batch (expressions options),¬(lo<c ∧ c<hi))
    (s : Fin (S+1)) : scan sample (options s) (List.finRange K)=scan t (options s) (List.finRange K) := by
  apply no_crossing_stable (options s) (List.finRange K) lo hi sample t hSample ht
  intro i _ j _ a b ha hb hSlope
  apply hNoCross
  apply GeneralPaperRayCrossingPairs.batch_complete (expressions options) s i j a.expression b.expression
  · simp only [expressions,ha,Option.map_some]
  · simp only [expressions,hb,Option.map_some]
  · exact hSlope

theorem midpoint_inside (lo hi : ℚ) (hOrder : lo<hi) : lo<(lo+hi)/2 ∧ (lo+hi)/2<hi := by
  constructor <;> linarith only [hOrder]

end Blotto.GeneralPaperRayStableMinimum
