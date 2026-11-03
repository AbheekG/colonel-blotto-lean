import Blotto.GeneralPaperRayAnchorBound

/-! All roots in an executed candidate-pair batch inherit coefficient
heights. Parallel pairs contribute no root; sorting/filtering do not
create new rational parameters. No list of whole tuples is introduced.
-/
namespace Blotto.GeneralPaperRayCrossingSize
open GeneralPaperRayAffine
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem crossing {D E A B : ℕ} (hD : 0<D) (hE : 0<E) (f g : Affine)
    (hf : GeneralPaperRayAffineBound.Bounded D E A B f) (hg : GeneralPaperRayAffineBound.Bounded D E A B g)
    (c : ℚ) (hc : GeneralPaperRayCrossingPairs.crossing f g=some c) :
    RationalHeight c (GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)) := by
  unfold GeneralPaperRayCrossingPairs.crossing at hc
  split at hc
  · contradiction
  · have he := Option.some.inj hc
    rw [←he]
    exact GeneralPaperRayAffineBound.crossing_height hD hE (GeneralPaperRayAffineBound.difference hf hg)

theorem optional {D E A B : ℕ} (hD : 0<D) (hE : 0<E) (a b : Option Affine)
    (ha : ∀ f,a=some f → GeneralPaperRayAffineBound.Bounded D E A B f)
    (hb : ∀ f,b=some f → GeneralPaperRayAffineBound.Bounded D E A B f)
    (c : ℚ) (hc : GeneralPaperRayCrossingPairs.optional a b=some c) :
    RationalHeight c (GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)) := by
  cases a with
  | none => contradiction
  | some f =>
    cases b with
    | none => contradiction
    | some g => exact crossing hD hE f g (ha f rfl) (hb g rfl) c hc

theorem pairs {i : Type*} {D E A B : ℕ} (hD : 0<D) (hE : 0<E) (options : i → Option Affine) (xs : List i)
    (h : ∀ i∈xs,∀ f,options i=some f → GeneralPaperRayAffineBound.Bounded D E A B f)
    (c : ℚ) (hc : c∈GeneralPaperRayCrossingPairs.pairs options xs) :
    RationalHeight c (GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)) := by
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp hc
  obtain ⟨b,hb,he⟩ := List.mem_filterMap.mp ht
  exact optional hD hE (options a) (options b) (h a ha) (h b hb) c he

theorem batch {S K D E A B : ℕ} (hD : 0<D) (hE : 0<E)
    (options : Fin (S+1) → Fin K → Option Affine)
    (h : ∀ s l f,options s l=some f → GeneralPaperRayAffineBound.Bounded D E A B f)
    (c : ℚ) (hc : c∈GeneralPaperRayCrossingPairs.batch options) :
    RationalHeight c (GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)) := by
  obtain ⟨s,_,hs⟩ := List.mem_flatMap.mp hc
  exact pairs hD hE (options s) (List.finRange K) (fun l _ => h s l) c hs

theorem stage_batch {S K D E X W n : ℕ} (hD : 0<D) (hE : 0<E)
    (field : GeneralPaperRayAffineScoreStep.Field K) (previous : GeneralPaperRayAffineScoreStep.Table S K)
    (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X W field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X W n previous)
    (c : ℚ) (hc : c∈GeneralPaperRayAffineScoreStep.crossings field previous) :
    RationalHeight c (GeneralPaperRayAffineBound.rootWidth D E ((n+1)*X+(n+1)*X) ((n+1)*W+(n+1)*W)) := by
  apply batch hD hE (GeneralPaperRayStableMinimum.expressions (GeneralPaperRayAffineScoreStep.candidate field previous)) _ c hc
  intro s l f he
  cases ht : GeneralPaperRayAffineScoreStep.candidate field previous s l with
  | none =>
    simp only [GeneralPaperRayStableMinimum.expressions,ht,Option.map_none] at he
    contradiction
  | some chosen =>
    have hExpr : chosen.expression=f := by
      simpa only [GeneralPaperRayStableMinimum.expressions,ht,Option.map_some,Option.some.injEq] using he
    rw [←hExpr]
    exact (GeneralPaperRayAffineDPSize.candidate D E X W n field previous hf hp s l chosen ht).1

end Blotto.GeneralPaperRayCrossingSize
