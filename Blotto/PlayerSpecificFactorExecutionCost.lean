import Blotto.PlayerSpecificFactorBudget

/-! Complete source prices for the actual bounded factor-removal recursion.
Every query and quotient uses derived linear heights, with no supplied root,
step-price, height or factorization oracle. -/
namespace Blotto.PlayerSpecificFactorExecutionCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificFactorHeights PlayerSpecificFactorBudget PlayerSpecificLinearFactor
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem output_bounds (model : RationalCostModel) (fuel : ℕ) (p : Data)
    (hp : semantics p≠0) (hlen : p.length≤4) (hfuel : p.length≤fuel)
    (H : ℕ) (hH : HasHeight p H) :
    HasHeight (PlayerSpecificFactorExecution.run model fuel p).1.1 (height fuel H) ∧
      HasHeight (PlayerSpecificFactorExecution.run model fuel p).1.2 (height fuel H) ∧
      (PlayerSpecificFactorExecution.run model fuel p).1.1.length≤3 ∧
      (PlayerSpecificFactorExecution.run model fuel p).1.2.length≤4 := by
  rw [PlayerSpecificFactorExecution.value]
  have hh:=run_height fuel p hp hlen hfuel H hH
  have hc:=PlayerSpecificRationalFactors.contract fuel p hp hlen hfuel
  have hd:=PlayerSpecificPolynomialNormalization.degree_le p
  exact ⟨hh.1,hh.2,by omega,hc.2.2.2.2.1.trans hlen⟩

theorem run_cost (model : RationalCostModel) (fuel : ℕ) (p : Data)
    (hp : semantics p≠0) (hlen : p.length≤4) (hfuel : p.length≤fuel) (hcap : fuel≤4)
    (H : ℕ) (hH : HasHeight p H) (hpos : 1≤H) :
    (PlayerSpecificFactorExecution.run model fuel p).2≤
      (fuel+1)*workCoefficient*(height fuel H+1)*model.rat (width (height fuel H)) := by
  induction fuel generalizing p H with
  | zero =>
    have hz : p=[] := List.length_eq_zero_iff.mp (by omega)
    exact (hp (by rw [hz]; rfl)).elim
  | succ fuel ih =>
    let U:=height (fuel+1) H
    have hHU : H≤U := height_ge (fuel+1) H
    have hSU : step H≤U := height_ge fuel (step H)
    have hRU : 56*H+37≤U := (show 56*H+37≤step H by unfold step; omega).trans hSU
    have hbig:=large U
    have hrprice:=root_cost model p hp hlen H U hH hHU
    have hrootlen: (PlayerSpecificRationalRootExecution.run model p).1.length≤3 :=
      (PlayerSpecificRationalRootContract.actual_contract model p hp hlen).1
    have hrootheight : HasHeight (PlayerSpecificRationalRootExecution.run model p).1 U := by
      intro q hq
      have hqroot:=((PlayerSpecificRationalRootContract.actual_contract model p hp hlen).2.1 q).mp hq
      exact (recovered_height p hp hlen H hH q hqroot).mono hRU
    cases hr : (PlayerSpecificRationalRootExecution.run model p).1 with
    | nil =>
      have ht:=PlayerSpecificDenseOperationCost.trim_cost model p H 4 hH hlen
      rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at ht
      have htw : 40*H+64≤width U := by omega
      have htp:=ht.trans (Nat.mul_le_mul_left 375000 (model.monotone htw))
      have hres : HasHeight (PlayerSpecificDenseExecution.trim p).1 U := by
        rw [PlayerSpecificDenseExecution.trim_value]
        exact mono (trim_height hH) hHU
      have hreslen : (PlayerSpecificDenseExecution.trim p).1.length≤4 := by
        rw [PlayerSpecificDenseExecution.trim_value]
        exact (trim_length p).trans hlen
      have hf:=frame_cost model (fuel+1) p [] ([],(PlayerSpecificDenseExecution.trim p).1) U
        (mono hH hHU) (nil_height U) (nil_height U) hres hlen (by simp) (by simp) hreslen hcap
      simp only [PlayerSpecificFactorExecution.run,hr]
      change _≤(fuel+2)*workCoefficient*(U+1)*model.rat (width U)
      have hm:=Nat.mul_le_mul_right (workCoefficient*(U+1)*model.rat (width U))
        (by omega : 1≤fuel+2)
      have hmono : workCoefficient*(U+1)*model.rat (width U)≤
          (fuel+2)*workCoefficient*(U+1)*model.rat (width U) := by
        simpa only [one_mul,mul_assoc] using hm
      apply le_trans ?_ hmono
      unfold workCoefficient
      nlinarith only [hrprice,htp,hf]
    | cons q qs =>
      have hq : evaluate p q=0 := ((PlayerSpecificRationalRootContract.actual_contract model p hp hlen).2.1 q).mp
        (by rw [hr]; exact List.mem_cons_self)
      have hqheight:=recovered_height p hp hlen H hH q hq
      have hdrop:=length_drop p hp q hq
      have hqnonzero:=quotient_nonzero p hp q hq
      have hquot:=quotient_height p hp hlen H hH q hq
      have hc:=ih (quotient p q) hqnonzero (by omega) (by omega) (by omega)
        (step H) hquot (by unfold step; omega)
      have hb:=output_bounds model fuel (quotient p q) hqnonzero (by omega) (by omega) (step H) hquot
      have hlin:=PlayerSpecificLinearFactorExecution.run_cost model q (56*H+37) hqheight (by omega)
      have hlw : 8*(56*H+37)+16≤width U := by omega
      have hlp:=hlin.trans (Nat.mul_le_mul_left 60 (model.monotone hlw))
      have hd:=PlayerSpecificDivisionTraceCost.run_cost model p (PlayerSpecificLinearFactorExecution.run q).1
        (56*H+37) (mono hH (by omega)) (by
          rw [PlayerSpecificLinearFactorExecution.value]
          exact linear_height q _ hqheight (by omega)) (by omega) hlen (by
          rw [PlayerSpecificLinearFactorExecution.value]
          simp only [linear,List.length_cons,List.length_nil]
          decide)
      have hdp:=hd.trans (Nat.mul_le_mul_left 100000000 (model.monotone (division_width H U hHU)))
      have hrv : (PlayerSpecificDivisionExecution.run p (PlayerSpecificLinearFactorExecution.run q).1).1.1=quotient p q := by
        rw [PlayerSpecificDivisionExecution.value,PlayerSpecificLinearFactorExecution.value]
        rfl
      have hf:=frame_cost model (fuel+1) p (q::qs)
        (q::(PlayerSpecificFactorExecution.run model fuel (quotient p q)).1.1,
          (PlayerSpecificFactorExecution.run model fuel (quotient p q)).1.2) U
        (mono hH hHU) (by rw [←hr]; exact hrootheight)
        (cons_height (hqheight.mono hRU) hb.1) hb.2.1 hlen (by rw [←hr]; exact hrootlen)
        (by simp only [List.length_cons]; omega) hb.2.2.2 hcap
      simp only [PlayerSpecificFactorExecution.run,hr,hrv]
      change _≤(fuel+2)*workCoefficient*(U+1)*model.rat (width U)
      change _≤(fuel+1)*workCoefficient*(U+1)*model.rat (width U) at hc
      unfold workCoefficient at hc ⊢
      nlinarith only [hrprice,hlp,hdp,hc,hf]

end Blotto.PlayerSpecificFactorExecutionCost
