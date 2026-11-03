import Blotto.PlayerSpecificSuffixExecution

/-! Complete original-field source word and price bounds for actual cached
suffix maxima, including every returned-list copy and control word. -/
namespace Blotto.PlayerSpecificSuffixCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalSweepHeights
open PlayerSpecificRationalTrace PlayerSpecificSuffixExecution PlayerSpecificSweepTraceFits
set_option autoImplicit false
set_option maxHeartbeats 2500000

def RowsHeight (rows : Rows) (H : ℕ) : Prop :=
  ∀ x∈rows,RationalHeight x.1.1 H ∧ RationalHeight x.1.2 H ∧ RationalHeight x.2 H

theorem returned_heights (fields : List (ℚ×ℚ)) (H : ℕ) (hf : FieldsHeight fields H) (hH : 1≤H) :
    RationalHeight (run fields).1.1 H ∧ RowsHeight (run fields).1.2 H := by
  have hv:=values fields
  rw [hv.1,hv.2,PlayerSpecificSweepBounds.suffixes_maximum]
  exact ⟨maximum_height fields H hf hH,suffix_height fields H hf hH⟩

theorem copy_fits (rows : Rows) (H W : ℕ) (hr : RowsHeight rows H)
    (hHW : 1+2*H≤W) (hrows : rows.length+1≤W) (hW : 4≤W) : Fits W (copyRows rows) := by
  rw [copyRows,fits_append]
  constructor
  · intro e he
    have heq:=List.mem_singleton.mp he
    subst e
    exact (PlayerSpecificRationalTrace.control_width _).trans hrows
  · intro e he
    obtain ⟨x,hx,hevent⟩:=List.mem_flatMap.mp he
    have hh:=hr x hx
    have hrow : HasHeight [x.1.1,x.1.2,x.2] H :=
      cons_height hh.1 (cons_height hh.2.1 (cons_height hh.2.2 (nil_height _)))
    exact copyRow_fits W _ (fun q hq => (rationalWordWidth_of_height (hrow q hq)).trans hHW) hW e hevent

theorem fits (fields : List (ℚ×ℚ)) (N H : ℕ) (hf : FieldsHeight fields H)
    (hn : fields.length≤N) (hH : 1≤H) : Fits (width H N) (run fields).2 := by
  have hW : 6≤width H N := by unfold width; omega
  have hHW : 1+2*H≤width H N := by unfold width; omega
  have hNW : N+1≤width H N := by unfold width; omega
  have control (n : ℕ) (hh : n≤N) : Fits (width H N) [.control n] := by
    intro e he
    have heq:=List.mem_singleton.mp he
    subst e
    exact (PlayerSpecificRationalTrace.control_width n).trans ((Nat.add_le_add_right hh 1).trans hNW)
  have row (p : Data) (hp : HasHeight p H) (hpLen : p.length≤5) : Fits (width H N) (copyRow p) :=
    copyRow_fits _ p (fun q hq => (rationalWordWidth_of_height (hp q hq)).trans hHW) (by omega)
  induction fields with
  | nil =>
    have hz:=row [0] (cons_height (zero_height.mono hH) (nil_height _)) (by simp)
    have hr:=copy_fits [] H (width H N) (by simp [RowsHeight]) hHW (by simp; omega) (by omega)
    simpa only [run,fits_append] using ⟨⟨hz,hr⟩,control 0 (by omega)⟩
  | cons x xs ih =>
    have hxs : FieldsHeight xs H := fun y hy => hf y (List.mem_cons_of_mem x hy)
    have hx:=hf x List.mem_cons_self
    have hnTail : xs.length≤N := by simp only [List.length_cons] at hn; omega
    have ht:=ih hxs hnTail
    have hhTail:=returned_heights xs H hxs hH
    have hmax:=PlayerSpecificRationalMaximumExecution.fits x.2 (run xs).1.1 H (width H N) hx.2 hhTail.1 hHW hW
    have hpair:=row [x.1,x.2] (cons_height hx.1 (cons_height hx.2 (nil_height _))) (by simp)
    have hhResult:=returned_heights (x::xs) H hf hH
    have hbound:=row [(run (x::xs)).1.1] (cons_height hhResult.1 (nil_height _)) (by simp)
    have hrows:=copy_fits (run (x::xs)).1.2 H (width H N) hhResult.2 hHW
      (by rw [rows_length]; exact (Nat.add_le_add_right hn 1).trans hNW) (by omega)
    have hc:=control (run (x::xs)).1.2.length (by rw [rows_length]; exact hn)
    simp only [run] at hbound hrows hc ⊢
    simpa only [fits_append] using ⟨⟨⟨⟨⟨ht,hmax⟩,hpair⟩,hbound⟩,hrows⟩,hc⟩

theorem source_cost (model : RationalCostModel) (fields : List (ℚ×ℚ)) (N H : ℕ)
    (hf : FieldsHeight fields H) (hn : fields.length≤N) (hH : 1≤H) :
    price model (run fields).2≤300*(fields.length+1)^2*model.rat (width H N) := by
  have hp:=price_bound model (width H N) (by unfold width; omega) _ (fits fields N H hf hn hH)
  exact hp.trans (by
    have hm:=Nat.mul_le_mul_right (3*model.rat (width H N)) (trace_length fields)
    nlinarith only [hm])

end Blotto.PlayerSpecificSuffixCost
