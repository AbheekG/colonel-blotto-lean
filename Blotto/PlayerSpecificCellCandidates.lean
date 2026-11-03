import Blotto.PlayerSpecificCells

/-! All positive interior roots and the separate rational-breakpoint test.
The root list is the explicitly allowed augmented-real-RAM primitive from
PlayerSpecificPolynomial, not an implementation of finite-bit root isolation. -/
namespace Blotto.PlayerSpecificCellCandidates
open PlayerSpecificCubic PlayerSpecificSweep PlayerSpecificSweepBounds PlayerSpecificCells
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000

def Interior (c : Cell) (gamma : ℝ) : Prop :=
  0<gamma ∧ c.lower<gamma ∧ match c.upper with
    | none => True
    | some upper => gamma<upper

noncomputable def breakpoints (c : Cell) (b : ℝ) : List ℝ :=
  match c.upper with
  | none => []
  | some upper => if 0<upper ∧ c.lower≤upper ∧ cubic c.state.coefficients b upper=0 then [upper] else []

noncomputable def candidates (c : Cell) (b : ℝ) : List ℝ :=
  (PlayerSpecificPolynomial.roots c.state.coefficients b).filter (fun gamma => decide (Interior c gamma))++
    breakpoints c b

theorem breakpoint_count (c : Cell) (b : ℝ) : (breakpoints c b).length≤1 := by
  unfold breakpoints
  split
  · simp only [List.length_nil]; omega
  · split <;> simp

theorem count (c : Cell) (b : ℝ) : (candidates c b).length≤4 := by
  have hr := PlayerSpecificPolynomial.root_count c.state.coefficients b
  have hf := List.length_filter_le (fun gamma => decide (Interior c gamma))
    (PlayerSpecificPolynomial.roots c.state.coefficients b)
  have hb := breakpoint_count c b
  rw [candidates,List.length_append]
  omega

theorem breakpoint_sound (c : Cell) (b gamma : ℝ) (h : gamma∈breakpoints c b) :
    ClosedRange c gamma ∧ cubic c.state.coefficients b gamma=0 := by
  unfold breakpoints at h
  split at h
  · simp only [List.not_mem_nil] at h
  · rename_i upper hu
    split at h
    · rename_i hp
      have he : gamma=upper := List.mem_singleton.mp h
      subst gamma
      refine ⟨⟨hp.1,hp.2.1,?_⟩,hp.2.2⟩
      intro u hmem
      rw [hu] at hmem
      have he : upper=u := by simpa only [Option.mem_def,Option.some.injEq] using hmem
      exact he.le
    · simp only [List.not_mem_nil] at h

theorem interior_range (c : Cell) (gamma : ℝ) (h : Interior c gamma) : ClosedRange c gamma := by
  refine ⟨h.1,h.2.1.le,?_⟩
  intro upper hu
  cases hupper : c.upper with
  | none => simp only [hupper,Option.not_mem_none] at hu
  | some u =>
    have he : u=upper := by simpa only [hupper,Option.mem_def,Option.some.injEq] using hu
    subst upper
    exact (by simpa only [Interior,hupper] using h : 0<gamma ∧ c.lower<gamma ∧ gamma<u).2.2.le

theorem sound (c : Cell) (b gamma : ℝ) (hp : PlayerSpecificPolynomial.polynomial c.state.coefficients b≠0)
    (h : gamma∈candidates c b) : ClosedRange c gamma ∧ cubic c.state.coefficients b gamma=0 := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨hr,hi⟩ := List.mem_filter.mp h
    exact ⟨interior_range c gamma (of_decide_eq_true hi),
      (PlayerSpecificPolynomial.root_membership c.state.coefficients b gamma hp).mp hr⟩
  · exact breakpoint_sound c b gamma h

theorem complete (c : Cell) (b gamma : ℝ) (hp : PlayerSpecificPolynomial.polynomial c.state.coefficients b≠0)
    (hr : ClosedRange c gamma) (hl : c.lower<gamma) (hc : cubic c.state.coefficients b gamma=0) :
    gamma∈candidates c b := by
  have hroot := (PlayerSpecificPolynomial.root_membership c.state.coefficients b gamma hp).mpr hc
  cases hu : c.upper with
  | none =>
    apply List.mem_append_left
    apply List.mem_filter.mpr
    exact ⟨hroot,decide_eq_true (show Interior c gamma from ⟨hr.1,hl,by simp only [hu]⟩)⟩
  | some upper =>
    have hle := hr.2.2 upper (by rw [hu]; exact Option.mem_some_self _)
    rcases lt_or_eq_of_le hle with hlt | heq
    · apply List.mem_append_left
      apply List.mem_filter.mpr
      exact ⟨hroot,decide_eq_true (show Interior c gamma from ⟨hr.1,hl,by simpa only [hu] using hlt⟩)⟩
    · apply List.mem_append_right
      subst gamma
      simp only [breakpoints,hu,hr.1,hr.2.1,hc,and_self,ite_true,List.mem_singleton]

def Passes (c : Cell) (b gamma : ℝ) : Prop :=
  max c.state.prefixMax (gamma*c.suffixMax)≤b*candidateScale c.state.coefficients b gamma

theorem gate_iff {n : ℕ} (v w : Values n) (low high : List (Fin n))
    (hp : (low++high).Perm (List.finRange n)) (c : Cell) (hf : Fits v.weight w.weight low high c)
    (b gamma : ℝ) (hb : 0<b) (hr : ClosedRange c gamma) :
    Passes c b gamma ↔ ∀ j,PlayerSpecificMarginals.length (v.weight j) (w.weight j) gamma
      (candidateScale c.state.coefficients b gamma)≤b := by
  have hc := PlayerSpecificSweepIndexed.coefficients_eq v.weight w.weight c.state low high hp hf.1.1
  have hscale := PlayerSpecificCandidate.scale_positive v.weight w.weight (PlayerSpecificSweepIndexed.highMask high) b gamma
    (PlayerSpecificAcceptance.count_positive v) v.positive w.positive hb hr.1
  rw [← hc] at hscale
  have hs := fits_respects v.weight w.weight low high hp c hf gamma hr w.positive
  have hprefix : c.state.prefixMax=maximum v.weight low :=
    hf.1.2.trans (maximum_map v.weight w.weight low).1
  rw [Passes,hprefix,hf.2.1,
    PlayerSpecificSweepIndexed.indexed_gate v.weight w.weight low high hp gamma _ hr.1 (mul_pos hb hscale).le]
  exact (PlayerSpecificAcceptance.endpoint_test v.weight w.weight _ b gamma _
    v.positive w.positive hr.1 hscale hs).symm

end Blotto.PlayerSpecificCellCandidates
