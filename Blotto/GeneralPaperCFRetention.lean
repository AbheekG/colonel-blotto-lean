import Blotto.GeneralPaperCFModelOrder

/-! The actual arithmetic source retains an approximation at least as close
as every bounded-denominator future regular convergent. Termination uses the
already derived Stops predicate; rejection cannot skip a feasible future
convergent because its denominators are nondecreasing after the first term.
-/
namespace Blotto.GeneralPaperCFRetention
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel GeneralPaperCFError GeneralPaperCFAdvanceData
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem stopped_large_denominator (D N M width : ℕ) (s : State) (h : Post N M width s)
    (hd : 0<s.denominator) (hStop : (advance D (width+2) s).2=false) :
    D<(advance D (width+2) s).1.previousDen := by
  have hPos : 0<(GeneralPaperConstructedNatDivision.run s.numerator s.denominator (width+2)).quotient*s.previousDen+s.olderDen := by
    rw [←(continuants D (width+2) s hd).2.2.2]
    exact h.positiveDen.trans_le (previous_den_mono D width s h.pair h.order)
  rw [(continuants D (width+2) s hd).2.2.2]
  apply lt_of_not_ge
  intro hBound
  have hMore : (advance D (width+2) s).2=true := by simp [advance,hd.ne',hPos,hBound]
  rw [hMore] at hStop
  cases hStop

theorem future_ge_actual_next (D width : ℕ) (s : State) (hPair : PairBound width s)
    (hOrder : s.denominator≤s.numerator) (k : ℕ) :
    (advance D (width+2) s).1.previousDen≤(GeneralPaperCFModel.future (GeneralPaperCFModel.view s) k).2 := by
  have he := GeneralPaperCFModelOrder.future_den_ge_step (GeneralPaperCFModel.view s) k hOrder
  have hv := congrArg GeneralPaperCFModel.Core.previousDen (GeneralPaperCFModel.advance_view D width s hPair)
  change (advance D (width+2) s).1.previousDen=(GeneralPaperCFModel.step (GeneralPaperCFModel.view s)).previousDen at hv
  rw [←hv] at he
  exact he

theorem future_zero_actual (D width : ℕ) (s : State) (hPair : PairBound width s) :
    GeneralPaperCFModel.future (GeneralPaperCFModel.view s) 0=
      ((advance D (width+2) s).1.previousNum,(advance D (width+2) s).1.previousDen) := by
  change ((GeneralPaperCFModel.step (GeneralPaperCFModel.view s)).previousNum,
    (GeneralPaperCFModel.step (GeneralPaperCFModel.view s)).previousDen)=_
  rw [←GeneralPaperCFModel.advance_view D width s hPair]
  rfl

theorem future_succ_actual (D width : ℕ) (s : State) (hPair : PairBound width s) (k : ℕ) :
    GeneralPaperCFModel.future (GeneralPaperCFModel.view s) (k+1)=
      GeneralPaperCFModel.future (GeneralPaperCFModel.view (advance D (width+2) s).1) k := by
  rw [GeneralPaperCFModel.future_succ,←GeneralPaperCFModel.advance_view D width s hPair]

theorem run_future_dominance (D N M width fuel : ℕ) (s : State) (hM : 0<M) (h : Post N M width s)
    (hSelected : CurrentSelected s) (hStops : Stops D (width+2) fuel s) (k : ℕ)
    (hBound : (GeneralPaperCFModel.future (GeneralPaperCFModel.view s) k).2≤D) :
    ∃ f, (run D (width+2) fuel s).selected=some f ∧
      valueError N M f.value≤valueError N M
        (((GeneralPaperCFModel.future (GeneralPaperCFModel.view s) k).1:ℚ)/
          (GeneralPaperCFModel.future (GeneralPaperCFModel.view s) k).2) := by
  induction fuel generalizing s k with
  | zero => exact hStops.elim
  | succ fuel ih =>
    cases hb : (advance D (width+2) s).2 with
    | false =>
      by_cases hz : s.denominator=0
      · obtain ⟨f,hf,he⟩ := run_selected_dominance D N M width (fuel+1) s hM h hSelected
        refine ⟨f,hf,?_⟩
        rw [GeneralPaperCFModel.future_zero_denominator _ k hz]
        exact he
      · have hd : 0<s.denominator := by omega
        have hLarge := stopped_large_denominator D N M width s h hd hb
        have hGe := future_ge_actual_next D width s h.pair h.order k
        omega
    | true =>
      have hn := advance_post D N M width s h
      have hs : CurrentSelected (advance D (width+2) s).1 := continuing_selection D (width+2) s hb
      have hTail : Stops D (width+2) fuel (advance D (width+2) s).1 :=
        hStops.elim (fun hBad => by simp only [hb,Bool.true_eq_false] at hBad) id
      cases k with
      | zero =>
        obtain ⟨f,hf,he⟩ := run_selected_dominance D N M width fuel _ hM hn hs
        refine ⟨f,by simpa only [run,hb,ite_true] using hf,?_⟩
        rw [future_zero_actual D width s h.pair]
        exact he
      | succ k =>
        have hFuture := future_succ_actual D width s h.pair k
        have hNextBound : (GeneralPaperCFModel.future (GeneralPaperCFModel.view (advance D (width+2) s).1) k).2≤D := by
          rw [←hFuture]
          exact hBound
        obtain ⟨f,hf,he⟩ := ih _ hn hs hTail k hNextBound
        exact ⟨f,by simpa only [run,hb,ite_true] using hf,by rw [hFuture]; exact he⟩

end Blotto.GeneralPaperCFRetention
