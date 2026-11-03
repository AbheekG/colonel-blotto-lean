import Blotto.GeneralPaperRayBracketSize

/-! Native sparse residual sums and every accumulator prefix retain their
fixed point/velocity lattices. Actual original rows supply their own unit
term and row-length/RHS bounds; static scans use exactly those rows.
-/
namespace Blotto.GeneralPaperRaySparseSize
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperRayRationalBound
open GeneralPaperRaySparseEvaluation
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem term {v : Type*} (D X : ℕ) (x : v → ℚ) (hx : ∀ a,Bounded D X (x a))
    (a : v × ℤ) (ha : a.2.natAbs≤1) : Bounded D X ((a.2:ℚ)*x a.1) := by
  have hh := (hx a.1).int_mul a.2
  exact hh.mono (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right X ha)

theorem loop_bound {v : Type*} (D E X W A B : ℕ) (x w : v → ℚ) (terms : List (v × ℤ))
    (a b : ℚ) (spent : ℕ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a))
    (hc : ∀ t∈terms,t.2.natAbs≤1) (ha : Bounded D A a) (hb : Bounded E B b) :
    Bounded D (A+terms.length*X) (loop x w terms a b spent).point ∧
      Bounded E (B+terms.length*W) (loop x w terms a b spent).velocity := by
  have hData := loop_data x w terms a b spent
  rw [hData.1,hData.2.1]
  exact ⟨ha.add (Bounded.list_sum D X _ terms (fun t ht => term D X x hx t (hc t ht))),
    hb.add (Bounded.list_sum E W _ terms (fun t ht => term E W w hw t (hc t ht)))⟩

theorem prefix_bound {v : Type*} (D E X W : ℕ) (x w : v → ℚ) (terms : List (v × ℤ)) (t : ℕ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a)) (hc : ∀ a∈terms,a.2.natAbs≤1) :
    Bounded D (terms.length*X) (loop x w (terms.take t) 0 0 0).point ∧
      Bounded E (terms.length*W) (loop x w (terms.take t) 0 0 0).velocity := by
  have hh := loop_bound D E X W 0 0 x w (terms.take t) 0 0 0 hx hw
    (fun a ha => hc a (List.mem_of_mem_take ha)) (Bounded.zero D) (Bounded.zero E)
  simp only [Nat.zero_add] at hh
  have hl : (terms.take t).length≤terms.length := by rw [List.length_take]; exact Nat.min_le_right _ _
  exact ⟨hh.1.mono (Nat.mul_le_mul_right X hl),hh.2.mono (Nat.mul_le_mul_right W hl)⟩

theorem evaluate_bound {v : Type*} (D E X W : ℕ) (r : Row v) (x w : v → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a)) (hc : ∀ a∈r.terms,a.2.natAbs≤1) :
    GeneralPaperRayAffineBound.Bounded D E (r.terms.length*X+r.constant.natAbs) (r.terms.length*W) (evaluate r x w).1 := by
  have hh := loop_bound D E X W 0 0 x w r.terms 0 0 0 hx hw hc (Bounded.zero D) (Bounded.zero E)
  simp only [Nat.zero_add] at hh
  exact ⟨hh.1.sub (Bounded.intCast D r.constant),hh.2⟩

theorem original_bound {T m K : ℕ} (hm : 0<m) (D E X W P : ℕ) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (i : Index T m K scores h) (beta : ℚ) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a)) (hb : Bounded D P beta) :
    GeneralPaperRayAffineBound.Bounded D E ((m+1)*X+(m+1)+(m+1)*P) ((m+1)*W)
      (GeneralPaperRayOriginalResidual.evaluate (constraints labels scores h i) beta x w) := by
  let r := constraints labels scores h i
  have hc : ∀ a∈r.terms,a.2.natAbs≤1 := by
    intro a ha
    rcases unit_terms labels scores h i a ha with he|he <;> simp only [he,Int.natAbs_one,Int.natAbs_neg,le_refl]
  have he := evaluate_bound D E X W r x w hx hw hc
  have hMassC := GeneralPaperAffineConstraintMass.augmented_terms hm labels scores h i false
  have hMassS := GeneralPaperAffineConstraintMass.augmented_terms hm labels scores h i true
  change r.terms.length+r.constant.natAbs≤m+1 at hMassC
  change r.terms.length+r.slope.natAbs≤m+1 at hMassS
  have hLen : r.terms.length≤m+1 := by omega
  have hC : r.constant.natAbs≤m+1 := by omega
  have hS : r.slope.natAbs≤m+1 := by omega
  have hBeta := hb.int_mul r.slope
  rw [mul_comm (r.slope:ℚ) beta] at hBeta
  refine ⟨?_,he.2.mono (Nat.mul_le_mul_right W hLen)⟩
  have hIntercept := he.1.sub hBeta
  exact hIntercept.mono (Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_right X hLen) hC) (Nat.mul_le_mul_right P hS))

theorem static_bound {T m K : ℕ} (hm : 0<m) (D E X W P : ℕ) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (i : GeneralPaperStaticRayRows.StaticIndex T m K)
    (beta : ℚ) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a)) (hb : Bounded D P beta) :
    GeneralPaperRayAffineBound.Bounded D E ((m+1)*X+(m+1)+(m+1)*P) ((m+1)*W)
      (GeneralPaperStaticRayScan.evaluate labels x w i).1 := by
  have hh := original_bound hm D E X W P labels scores h (GeneralPaperStaticRayRows.embed i) beta x w hx hw hb
  rw [←GeneralPaperStaticRayRows.row_eq,GeneralPaperRayOriginalResidual.static_eq] at hh
  exact hh

end Blotto.GeneralPaperRaySparseSize
