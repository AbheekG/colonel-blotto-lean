import Blotto.PlayerSpecificDyadicEndpoints

/-! Stored rows and actual rational endpoint evaluations in the prepared
Sturm counter have fixed-degree coefficient-size bounds. -/
namespace Blotto.PlayerSpecificSturmHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificSquarefreeHeights
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem next_bounds (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    HasHeight (PlayerSpecificSturmSequence.next p q) (PlayerSpecificDivisionHeights.height H) ∧
      (PlayerSpecificSturmSequence.next p q).length≤4 := by
  have h := (PlayerSpecificDivisionHeights.run_height p q H hp hq hH hpl hql).2
  refine ⟨trim_height (negative_height h),?_⟩
  have ht := trim_length (scale (-1) (PlayerSpecificPolynomialDivision.run p q).2)
  rw [scale_length] at ht
  exact ht.trans ((PlayerSpecificDivisionHeights.remainder_length p q).trans hpl)

theorem chain_bounds (fuel : ℕ) (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    ∀ row∈PlayerSpecificSturmSequence.chain fuel p q,
      HasHeight row (PlayerSpecificExtendedGCDHeights.height fuel H) ∧ row.length≤4 := by
  induction fuel generalizing p q H with
  | zero =>
    rw [PlayerSpecificSturmSequence.chain]
    split
    · intro row hr; cases hr
    · intro row hr
      have he := List.mem_singleton.mp hr
      subst row
      exact ⟨mono hq (PlayerSpecificExtendedGCDHeights.height_ge _ _),hql⟩
  | succ fuel ih =>
    rw [PlayerSpecificSturmSequence.chain]
    split
    · intro row hr; cases hr
    · intro row hr
      rcases List.mem_cons.mp hr with he | ht
      · subst row
        exact ⟨mono hq (PlayerSpecificExtendedGCDHeights.height_ge _ _),hql⟩
      · have hn := next_bounds p q H hp hq hH hpl hql
        have hD := PlayerSpecificDivisionHeights.height_ge H
        have h := ih q (PlayerSpecificSturmSequence.next p q) (PlayerSpecificDivisionHeights.height H)
          (mono hq hD) hn.1 (hH.trans hD) hql hn.2 row ht
        refine ⟨mono h.1 ?_,h.2⟩
        rw [PlayerSpecificExtendedGCDHeights.height]
        omega

theorem run_bounds (p : Data) (H : ℕ) (hp : HasHeight p H) (hlen : p.length≤4) :
    ∀ row∈PlayerSpecificSturmSequence.run p,HasHeight row (gcdHeight H) ∧ row.length≤4 := by
  have hfirst := trim_height hp
  have hflen := (trim_length p).trans hlen
  have hsecond := trim_height (derivative_height_four (trim p) H hfirst hflen)
  have hslen := (trim_length (derivative (trim p))).trans ((derivative_length (trim p)).trans hflen)
  have hcap := PlayerSpecificExtendedGCDHeights.fuel_mono (5*(H+1)) hslen
  unfold PlayerSpecificSturmSequence.run
  dsimp only
  split
  · intro row hr; cases hr
  · intro row hr
    rcases List.mem_cons.mp hr with he | ht
    · subst row
      exact ⟨mono hfirst (gcdHeight_ge H),hflen⟩
    · have h := chain_bounds (trim (derivative (trim p))).length (trim p) (trim (derivative (trim p))) (5*(H+1))
        (mono hfirst (by omega)) hsecond (by omega) hflen hslen row ht
      exact ⟨mono h.1 hcap,h.2⟩

theorem rows_bounds (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    ∀ row∈PlayerSpecificSturmRootCount.rows p,HasHeight row (certificateHeight H) ∧ row.length≤4 := by
  have hs := quotient_bounds p H hp hH hlen
  exact run_bounds (PlayerSpecificSquarefreeAlgorithm.run p) _ hs.1 hs.2

theorem rows_length (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    (PlayerSpecificSturmRootCount.rows p).length≤5 := by
  have h := PlayerSpecificSturmSequence.run_length (PlayerSpecificSquarefreeAlgorithm.run p)
  have hs := (quotient_bounds p H hp hH hlen).2
  change (PlayerSpecificSturmRootCount.rows p).length≤_ at h
  omega

theorem row_evaluate_height (p : Data) (H T : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4)
    (row : Data) (hr : row∈PlayerSpecificSturmRootCount.rows p) (x : ℚ) (hx : RationalHeight x T) :
    RationalHeight (evaluate row x) (4*(certificateHeight H+T+1)+1) := by
  have h := rows_bounds p H hp hH hlen row hr
  apply (evaluate_height h.1 hx).mono
  nlinarith

end Blotto.PlayerSpecificSturmHeights
