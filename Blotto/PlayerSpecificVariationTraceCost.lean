import Blotto.PlayerSpecificVariationExecution

/-! Actual sign-variation comparisons have bounded operand/control widths
and a polynomial source trace. This joins the executed counter, not a
caller-provided count or sign oracle, to the rational-primitive prices. -/
namespace Blotto.PlayerSpecificVariationTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificVariationExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem frame_fits (row : Data) (a b : ℚ) (W : ℕ)
    (hrow : ∀ q∈row,rationalWordWidth q≤W) (ha : rationalWordWidth a≤W) (hb : rationalWordWidth b≤W)
    (hz : rationalWordWidth (0:ℚ)≤W) (hc : row.length+1≤W) : Fits W (frame row a b) := by
  have hW : 1≤W := by omega
  have hcopy := copyRow_fits W row hrow hc
  have hza := equalZero_fits W a ha hz hW
  have hzb := equalZero_fits W b hb hz hW
  have hlast : Fits W [.compare a 0,.compare 0 a,.compare b 0,.compare 0 b,.control row.length] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ha,hz⟩
    · exact ⟨hz,ha⟩
    · exact ⟨hb,hz⟩
    · exact ⟨hz,hb⟩
    · exact (control_width row.length).trans hc
  simpa only [frame,fits_append] using And.intro (And.intro (And.intro hcopy hza) hzb) hlast

theorem assemble_fits (W : ℕ) (pre : Trace) (rest : ℕ×Trace) (increment : ℕ)
    (hp : Fits W pre) (hr : Fits W rest.2) (hn : rest.1+increment+2≤W) :
    Fits W (assemble pre rest increment).2 := by
  have hc : Fits W [.control rest.1,.control increment,.control (rest.1+increment)] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl <;> exact (control_width _).trans (by omega)
  simpa only [assemble,fits_append] using And.intro (And.intro hp hr) hc

theorem run_fits (row : Data) (W : ℕ) (hrow : ∀ q∈row,rationalWordWidth q≤W)
    (hz : rationalWordWidth (0:ℚ)≤W) (hc : row.length+5≤W) : Fits W (run row).2 := by
  induction hn : row.length using Nat.strong_induction_on generalizing row with
  | h n ih =>
    cases row with
    | nil =>
      rw [run.eq_def]
      intro e he
      have he' := List.mem_singleton.mp he
      subst e
      exact (control_width 0).trans (by omega)
    | cons a tail =>
      cases tail with
      | nil =>
        have ha := hrow a List.mem_cons_self
        have hcopy := copyRow_fits W [a] hrow (by simp only [List.length_cons,List.length_nil]; omega)
        have hzero := equalZero_fits W a ha hz (by omega)
        have hlast : Fits W [.control 0] := by
          intro e he
          have he' := List.mem_singleton.mp he
          subst e
          exact (control_width 0).trans (by omega)
        rw [run.eq_def]
        simpa only [fits_append] using And.intro (And.intro hcopy hzero) hlast
      | cons b rest =>
        have hlen : rest.length+2=n := by simpa only [List.length_cons,Nat.add_assoc] using hn
        have hlrow : ∀ q∈b::rest,rationalWordWidth q≤W := fun q hq => hrow q (List.mem_cons_of_mem a hq)
        have hrrow : ∀ q∈a::rest,rationalWordWidth q≤W := by
          intro q hq
          rcases List.mem_cons.mp hq with he | ht
          · subst q; exact hrow a List.mem_cons_self
          · exact hrow q (List.mem_cons_of_mem a (List.mem_cons_of_mem b ht))
        have hl := ih (rest.length+1) (by omega) (b::rest) hlrow (by simp only [List.length_cons]; omega) rfl
        have hr := ih (rest.length+1) (by omega) (a::rest) hrrow (by simp only [List.length_cons]; omega) rfl
        have hp := frame_fits (a::b::rest) a b W hrow (hrow a List.mem_cons_self)
          (hrow b (List.mem_cons_of_mem a List.mem_cons_self)) hz (by simp only [List.length_cons]; omega)
        have hcountl := count_le_length (b::rest)
        have hcountr := count_le_length (a::rest)
        simp only [List.length_cons] at hcountl hcountr
        rw [run.eq_def]
        dsimp only
        split_ifs <;> apply assemble_fits W _ _ _ hp <;> first | exact hl | exact hr | omega

def width (H N : ℕ) : ℕ := 2*H+N+8

theorem run_fits_height (row : Data) (H N : ℕ) (h : HasHeight row H) (hlen : row.length≤N) :
    Fits (width H N) (run row).2 := by
  apply run_fits
  · intro q hq
    exact (rationalWordWidth_of_height (h q hq)).trans (by unfold width; omega)
  · exact (rationalWordWidth_of_height zero_height).trans (by unfold width; omega)
  · unfold width; omega

theorem run_cost (model : RationalCostModel) (row : Data) (H N : ℕ) (h : HasHeight row H) (hlen : row.length≤N) :
    price model (run row).2≤60*(row.length+1)^2*model.rat (width H N) := by
  have hp := price_bound model (width H N) (by unfold width; omega) _ (run_fits_height row H N h hlen)
  have hl := trace_length row
  nlinarith

end Blotto.PlayerSpecificVariationTraceCost
