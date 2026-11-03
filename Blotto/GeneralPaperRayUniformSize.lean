import Blotto.GeneralPaperRaySparseSize

/-! One uniform root width covers original residuals, every parametric
candidate-pair batch and the final high-score budget batch. Candidate
coefficients depend on the number of fields, not previous test roots.
-/
namespace Blotto.GeneralPaperRayUniformSize
open GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 4500000

def interceptCap (m X P : ℕ) : ℕ := (m+1)*(X+P+1)
def slopeCap (m W : ℕ) : ℕ := (m+1)*(W+1)
def width (D E m X W P : ℕ) : ℕ :=
  GeneralPaperRayAffineBound.rootWidth D E (interceptCap m X P+interceptCap m X P) (slopeCap m W+slopeCap m W)

theorem scale_caps (m X W P n : ℕ) (hn : n≤m) : n*X≤ interceptCap m X P ∧ n*W≤slopeCap m W := by
  have hx := Nat.mul_le_mul_right X hn
  have hw := Nat.mul_le_mul_right W hn
  unfold interceptCap slopeCap
  constructor <;> nlinarith

theorem stage_roots {S K D E X W P m n : ℕ} (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : GeneralPaperRayAffineScoreStep.Field K) (previous : GeneralPaperRayAffineScoreStep.Table S K)
    (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X W field)
    (hp : GeneralPaperRayAffineDPSize.TableBounded D E X W n previous)
    (c : ℚ) (hc : c∈GeneralPaperRayAffineScoreStep.crossings field previous) : RationalHeight c (width D E m X W P) := by
  have hh := GeneralPaperRayCrossingSize.stage_batch hD hE field previous hf hp c hc
  have hb := scale_caps m X W P (n+1) hn
  exact hh.mono (GeneralPaperRayAffineBound.rootWidth_mono D E _ _ _ _
    (Nat.add_le_add hb.1 hb.1) (Nat.add_le_add hb.2 hb.2))

theorem budget_roots {S K D E X W P m n : ℕ} (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : GeneralPaperRayAffineScoreStep.Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X W n table)
    (h : ℕ) (beta : ℚ) (hb : Bounded D P beta) (c : ℚ) (hc : c∈GeneralPaperRayBudgetCrossings.batch table h beta) :
    RationalHeight c (width D E m X W P) := by
  obtain ⟨s,_,hc⟩ := List.mem_filterMap.mp hc
  by_cases hs : h<s.val
  · cases ht : table.read s with
    | none =>
      simp only [GeneralPaperRayBudgetCrossings.candidate,hs,ite_true,ht] at hc
      contradiction
    | some chosen =>
      have hCross : GeneralPaperRayCrossingPairs.crossing (GeneralPaperRayBudgetCrossings.constant beta) chosen.expression=some c := by
        simpa only [GeneralPaperRayBudgetCrossings.candidate,hs,ite_true,ht] using hc
      have hCap := scale_caps m X W P n hn
      have hP : P≤ interceptCap m X P := by unfold interceptCap; nlinarith
      have hConst : GeneralPaperRayAffineBound.Bounded D E (interceptCap m X P) (slopeCap m W)
          (GeneralPaperRayBudgetCrossings.constant beta) := ⟨hb.mono hP,(Bounded.zero E).mono (Nat.zero_le _)⟩
      exact GeneralPaperRayCrossingSize.crossing hD hE _ _ hConst
        (GeneralPaperRayAffineBound.mono (hp s chosen ht).1 hCap.1 hCap.2) c hCross
  · simp only [GeneralPaperRayBudgetCrossings.candidate,hs,ite_false] at hc
    contradiction

theorem original_root {T m K D E X W P : ℕ} (hm : 0<m) (hD : 0<D) (hE : 0<E)
    (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (i : GeneralPaperAffineConstraintRows.Index T m K scores h) (beta : ℚ) (x w : RationalOrderCell.Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a)) (hb : Bounded D P beta) :
    RationalHeight (GeneralPaperRayOriginalResidual.evaluate (GeneralPaperAffineConstraintRows.constraints labels scores h i) beta x w).crossing
      (width D E m X W P) := by
  have hr := GeneralPaperRaySparseSize.original_bound hm D E X W P labels scores h i beta x w hx hw hb
  have hA : (m+1)*X+(m+1)+(m+1)*P≤ interceptCap m X P := by unfold interceptCap; nlinarith
  have hB : (m+1)*W≤slopeCap m W := by unfold slopeCap; nlinarith
  have hh := GeneralPaperRayAffineBound.crossing_height hD hE (GeneralPaperRayAffineBound.mono hr hA hB)
  exact hh.mono (GeneralPaperRayAffineBound.rootWidth_mono D E _ _ _ _ (Nat.le_add_right _ _) (Nat.le_add_right _ _))

theorem static_time {T m K D E X W P : ℕ} (hm : 0<m) (hD : 0<D) (hE : 0<E)
    (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ) (beta : ℚ)
    (x w : RationalOrderCell.Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a)) (hb : Bounded D P beta)
    (chosen : GeneralPaperRayMinimum.Choice (GeneralPaperStaticRayRows.StaticIndex T m K))
    (hc : (GeneralPaperStaticRayScan.scan labels x w).choice=some chosen) : RationalHeight chosen.time (width D E m X W P) := by
  have hr := GeneralPaperRayMinimum.scan_best (GeneralPaperStaticRayScan.evaluate labels x w) (GeneralPaperStaticRayRows.enumerate T m K)
  change GeneralPaperRayMinimum.Best _ (GeneralPaperStaticRayScan.scan labels x w).choice at hr
  rw [hc] at hr
  obtain ⟨i,_,hi⟩ := hr.1
  rw [hi.2.1]
  have hh := original_root hm hD hE labels scores h (GeneralPaperStaticRayRows.embed i) beta x w hx hw hb
  rw [←GeneralPaperStaticRayRows.row_eq,GeneralPaperRayOriginalResidual.static_eq] at hh
  exact hh

end Blotto.GeneralPaperRayUniformSize
