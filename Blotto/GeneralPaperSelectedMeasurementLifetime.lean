import Blotto.GeneralPaperMeasuredRetainedPlanLifetime

/-! Complete measured-plan windows for the actual selected two-pool
constructor. Inner branch widths stay separate from the outer header width.
All concrete child conditions are discharged; native capacities derive from
source contracts. Full caller/cursor/outer-attachment scratch is separate. -/
namespace Blotto.GeneralPaperSelectedMeasurementLifetime
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperMeasuredScalarPlanLifetime
open GeneralPaperMeasuredRecordPlanLifetime
open GeneralPaperMeasuredLeafRecordLifetime
open GeneralPaperMeasuredRetainedPlanLifetime
open GeneralPaperEqualMeasuredLeafPlans
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def dominantWindow {n : ℕ} (model : RationalCostModel) (S A : ℕ) (values : FixedArrayTable n ℚ) (chosen : Fin n) : ℕ :=
  sequenceWindow S A [(GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) values,
      GeneralPaperMeasuredArrayPlanLifetime.window model S A (GeneralPaperMeasuredBlockPlan.rational model S) (rationalWindow model S) values),
    (GeneralPaperMeasuredBlockPlan.natural model S chosen.val,naturalWindow model S chosen.val),
    (reserve model S A 32,referencesWindow model S A 0 0 32)]

theorem dominant_good {n : ℕ} (model : RationalCostModel) (S A : ℕ) (values : FixedArrayTable n ℚ) (chosen : Fin n) (hA : 0 < A) :
    Good model S A 134 (GeneralPaperMeasuredBlockPlan.sequence S
      [GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) values,
        GeneralPaperMeasuredBlockPlan.natural model S chosen.val,reserve model S A 32]) (dominantWindow model S A values chosen) := by
  have h := sequence_good model S A 36
    [(GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) values,
        GeneralPaperMeasuredArrayPlanLifetime.window model S A (GeneralPaperMeasuredBlockPlan.rational model S) (rationalWindow model S) values),
      (GeneralPaperMeasuredBlockPlan.natural model S chosen.val,naturalWindow model S chosen.val),
      (reserve model S A 32,referencesWindow model S A 0 0 32)] hA (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · exact GeneralPaperMeasuredArrayPlanLifetime.good model S A 4 _ _ values hA (fun j => rational_good model S A (values.read j) hA)
    · exact mono model S A 4 36 _ _ (natural_good model S A chosen.val hA) (by decide)
    · exact mono model S A 4 36 _ _ (reserve_good model S A 32 hA (by decide) (by decide)) (by decide))
  simpa only [dominantWindow,List.map_cons,List.map_nil,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul] using h

def headerWindow (model : RationalCostModel) (S A : ℕ) : ℕ :=
  joinWindow S A (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) [A])
    (reserve model S A 64)
    (GeneralPaperMeasuredListPlanLifetime.window model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) (naturalWindow model S) [A])
    (referencesWindow model S A 0 0 64)

theorem header_good (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    Good model S A 40 (GeneralPaperEqualMeasuredSelectedPlan.header model S A) (headerWindow model S A) := by
  exact join_good model S A 28 4 _ _ _ _ hA
    (GeneralPaperMeasuredListPlanLifetime.run_good model S A 4 1 32 _ _ [A] hA
      (by decide) (by decide) (by decide) (by decide) (fun value _ => natural_good model S A value hA))
    (reserve_good model S A 64 hA (by decide) (by decide))

def innerWindow {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  match source with
  | ⟨.dominant chosen _ row _,A,_⟩ => dominantWindow model S A ⟨row.data,row.size⟩ chosen
  | ⟨.grouped _ sampler _ _,_,_⟩ => samplerWindow model S sampler.address sampler

theorem inner_good {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :
    Good model S (innerWidth source) 7578 (inner model S source) (innerWindow model S source) := by
  have hWidths := widths_positive source
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      exact mono model S A 134 7578 _ _ (dominant_good model S A ⟨row.data,row.size⟩ chosen hWidths.2) (by decide)
    | grouped small sampler hK hB => exact sampler_good model S sampler.address sampler hWidths.1

def window {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  innerWindow model S source + headerWindow model S source.address

def bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  ((inner model S source).sizes.sum + 1) * 7578 * unit model S (innerWidth source) (inner model S source).work +
    ((outer model S source).sizes.sum + 1) * 40 * unit model S source.address (outer model S source).work

theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source := by
  have hWidths := widths_positive source
  have hInner := (inner_good model S source).2 _ (inner_capacity model W S k values v hv budget source) le_rfl
  have hTotal := total_capacity model W S k values v hv budget source
  have hOuter := (header_good model S source.address hWidths.2).2
    (outer model S source).work (show (outer model S source).sizes.sum < 2 ^ source.address by omega) le_rfl
  exact Nat.add_le_add hInner hOuter

end Blotto.GeneralPaperSelectedMeasurementLifetime
