import Blotto.PlayerSpecificSweepTraceFits

/-! Complete source word/price bounds for the actual initial rational
sums. Full returned-state and input-list copies are included at each frame. -/
namespace Blotto.PlayerSpecificSweepInitialCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalSweepHeights
open PlayerSpecificSweep PlayerSpecificRationalTrace PlayerSpecificSweepExecution PlayerSpecificSweepTraceFits
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem fits (fields : List (ℚ×ℚ)) (N H : ℕ) (hf : FieldsHeight fields H)
    (hn : fields.length≤N) (hH : 1≤H) :
    Fits (width (initialBound N H) N) (PlayerSpecificSweepExecution.initial fields).2 := by
  let T:=initialBound N H
  let W:=width T N
  have hlarge:=initial_width N H
  have hT : 1≤T := by unfold T initialBound; omega
  have hW : 6≤W := by unfold W width; omega
  have hTW : 1+2*T≤W := by unfold W width; omega
  have hsmall : H≤T := hlarge.1
  have scalar_fit (op : Arithmetic) (a b : ℚ) (ha : RationalHeight a T) (hb : RationalHeight b T) :
      Fits W (scalar op a b).2 :=
    fits_mono (scalar_fits_height op a b T ha hb) hlarge.2.2.1
  induction fields with
  | nil =>
    have hz : StateHeight (PlayerSpecificSweepExecution.initial []).1 T := by
      exact ⟨zero_height.mono hT,zero_height.mono hT,zero_height.mono hT,zero_height.mono hT,zero_height.mono hT⟩
    have hs:=copy_state_fits _ T W hz hTW hW
    have hc : Fits W [.control 0] := by
      intro e he
      have heq:=List.mem_singleton.mp he
      subst e
      exact (PlayerSpecificRationalTrace.control_width 0).trans (by omega)
    exact (fits_append _ _ _).mpr ⟨hs,hc⟩
  | cons x xs ih =>
    have hxs : FieldsHeight xs H := fun y hy => hf y (List.mem_cons_of_mem x hy)
    have hx:=hf x List.mem_cons_self
    have hnTail : xs.length≤N := by simp only [List.length_cons] at hn; omega
    have ht:=ih hxs hnTail
    have hs:=PlayerSpecificSweepTraceFits.initial_height xs N H hxs hnTail hH
    have hresult:=PlayerSpecificSweepTraceFits.initial_height (x::xs) N H hf hn hH
    have hsquare : RationalHeight (scalar .multiply x.2 x.2).1 T := by
      simpa only [scalar_value,Arithmetic.apply] using (hx.2.mul hx.2).mono (show H+H≤T by omega)
    have hterm : RationalHeight (scalar .divide (scalar .multiply x.2 x.2).1 x.1).1 T := by
      simpa only [scalar_value,Arithmetic.apply,pow_two] using (square_divide x.2 x.1 H hx.2 hx.1).mono hlarge.2.1
    have hsq:=scalar_fit .multiply x.2 x.2 (hx.2.mono hsmall) (hx.2.mono hsmall)
    have hdiv:=scalar_fit .divide _ x.1 hsquare (hx.1.mono hsmall)
    have hfirst:=scalar_fit .add x.2 (PlayerSpecificSweepExecution.initial xs).1.coefficients.A1 (hx.2.mono hsmall) hs.1
    have hthird:=scalar_fit .add _ (PlayerSpecificSweepExecution.initial xs).1.coefficients.B1 hterm hs.2.2.1
    have hfields:=copy_fields_fits (x::xs) T W (fun y hy =>
      ⟨(hf y hy).1.mono hsmall,(hf y hy).2.mono hsmall⟩) hTW (by
        have hh:=hlarge.2.2.2
        exact (Nat.add_le_add_right hn 1).trans hh) (by omega)
    have hout:=copy_state_fits _ T W hresult hTW hW
    have hc : Fits W [.control (x::xs).length] := by
      intro e he
      have heq:=List.mem_singleton.mp he
      subst e
      exact (PlayerSpecificRationalTrace.control_width _).trans ((Nat.add_le_add_right hn 1).trans hlarge.2.2.2)
    simp only [PlayerSpecificSweepExecution.initial] at hout ⊢
    simpa only [fits_append] using ⟨⟨⟨⟨⟨⟨⟨ht,hsq⟩,hdiv⟩,hfirst⟩,hthird⟩,hfields⟩,hout⟩,hc⟩

theorem source_cost (model : RationalCostModel) (fields : List (ℚ×ℚ)) (N H : ℕ)
    (hf : FieldsHeight fields H) (hn : fields.length≤N) (hH : 1≤H) :
    price model (PlayerSpecificSweepExecution.initial fields).2≤300*(fields.length+1)^2*model.rat (width (initialBound N H) N) := by
  have hp:=price_bound model (width (initialBound N H) N) (by unfold width; omega) _ (fits fields N H hf hn hH)
  exact hp.trans (by
    have hm:=Nat.mul_le_mul_right (3*model.rat (width (initialBound N H) N)) (initial_length fields)
    nlinarith only [hm])

end Blotto.PlayerSpecificSweepInitialCost
