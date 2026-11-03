import Blotto.PlayerSpecificModularBudget

/-! Complete actual modular-Horner source price, including all arithmetic,
four-entry divisions, retained coefficient rows and returned copies. -/
namespace Blotto.PlayerSpecificModularExecutionCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificModularHeights PlayerSpecificModularBudget
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem run_cost (model : RationalCostModel) (m b a : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hbl : b.length≤3) (hal : a.length≤17)
    (H : ℕ) (hmH : HasHeight m H) (hbH : HasHeight b H) (haH : HasHeight a H) :
    (PlayerSpecificModularExecution.run model m b a).2≤
      200000000*(a.length+1)*model.rat (width a.length H) := by
  induction a with
  | nil =>
    have hg:=height_ge 0 H
    have hw:=large 0 H
    have hf:=frame_cost model m b [] [] (height 0 H) (width 0 H)
      (mono hmH (by omega)) (mono hbH (by omega)) (nil_height _) (nil_height _)
      hml hbl (by simp) (by simp) (by omega) (by omega)
    simp only [PlayerSpecificModularExecution.run,List.length_nil]
    exact hf.trans (Nat.mul_le_mul_right _ (by decide : 300≤200000000*(0+1)))
  | cons c cs ih =>
    let G:=height cs.length H
    let J:=height (cs.length+1) H
    let W:=width (cs.length+1) H
    have hg : H+1≤G := height_ge cs.length H
    have hj : H+1≤J := height_ge (cs.length+1) H
    have hgj : G≤J := fuel_mono H (Nat.le_succ _)
    have hw : 1024*(J+1)≤W := large (cs.length+1) H
    have hrestH : HasHeight (PlayerSpecificModularExecution.run model m b cs).1 G := by
      rw [PlayerSpecificModularExecution.value]
      exact run_height m b cs hm hm0 hml hbl H hmH hbH (tail_height haH)
    have hrestlen : (PlayerSpecificModularExecution.run model m b cs).1.length≤3 := by
      rw [PlayerSpecificModularExecution.value]
      have hr:=(PlayerSpecificModularHorner.reduced m b cs hm hm0).2
      omega
    have hscaledH : HasHeight (PlayerSpecificDenseExecution.scale c b).1 (4*G) := by
      rw [PlayerSpecificDenseExecution.scale_value]
      exact mono (scale_height (head_height haH) hbH) (by omega)
    have hscaledlen : (PlayerSpecificDenseExecution.scale c b).1.length≤4 := by
      rw [PlayerSpecificDenseExecution.scale_value,scale_length]; omega
    have hshiftH : HasHeight (PlayerSpecificDenseExecution.shift (PlayerSpecificModularExecution.run model m b cs).1).1 (4*G) := by
      rw [PlayerSpecificDenseExecution.shift_value]
      exact mono (shift_height hrestH (by omega)) (by omega)
    have hshiftlen : (PlayerSpecificDenseExecution.shift (PlayerSpecificModularExecution.run model m b cs).1).1.length≤4 := by
      change (PlayerSpecificModularExecution.run model m b cs).1.length+1≤4
      omega
    have hinputH : HasHeight
        (PlayerSpecificDenseExecution.add (PlayerSpecificDenseExecution.scale c b).1
          (PlayerSpecificDenseExecution.shift (PlayerSpecificModularExecution.run model m b cs).1).1).1 (4*G) := by
      rw [PlayerSpecificDenseExecution.add_value,PlayerSpecificDenseExecution.scale_value,
        PlayerSpecificDenseExecution.shift_value,PlayerSpecificModularExecution.value]
      exact input_height c b _ H G (head_height haH) hbH (by rwa [←PlayerSpecificModularExecution.value model m b cs]) hg
    have hinputlen : (PlayerSpecificDenseExecution.add (PlayerSpecificDenseExecution.scale c b).1
        (PlayerSpecificDenseExecution.shift (PlayerSpecificModularExecution.run model m b cs).1).1).1.length≤4 := by
      rw [PlayerSpecificDenseExecution.add_value,add_length]
      omega
    have hcscale:=PlayerSpecificDenseOperationCost.scale_cost model c b (4*G) 4
      ((head_height haH).mono (by omega)) (mono hbH (by omega)) (by omega)
    have hcshift:=PlayerSpecificDenseOperationCost.shift_cost model (PlayerSpecificModularExecution.run model m b cs).1 (4*G) 4
      (mono hrestH (by omega)) (by omega) (by omega)
    have hcadd:=PlayerSpecificDenseOperationCost.add_cost model _ _ (4*G) 4 hscaledH hshiftH hscaledlen hshiftlen
    rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hcscale hcshift hcadd
    have hdw : 40*(4*G)+64≤W := by omega
    have hsp:=hcscale.trans (Nat.mul_le_mul_left 375000 (model.monotone hdw))
    have hxp:=hcshift.trans (Nat.mul_le_mul_left 375000 (model.monotone hdw))
    have hap:=hcadd.trans (Nat.mul_le_mul_left 375000 (model.monotone hdw))
    have hd:=PlayerSpecificDivisionTraceCost.run_cost model _ m (4*G) hinputH (mono hmH (by omega)) (by omega) hinputlen hml
    have hdp:=hd.trans (Nat.mul_le_mul_left 100000000 (model.monotone (division_width cs.length H)))
    have hi:=ih (by simp only [List.length_cons] at hal; omega) (tail_height haH)
    have hip:=hi.trans (Nat.mul_le_mul_left _ (model.monotone (width_mono H (Nat.le_succ cs.length))))
    have hresultH : HasHeight (PlayerSpecificModularExecution.run model m b (c::cs)).1 J := by
      rw [PlayerSpecificModularExecution.value]
      exact run_height m b (c::cs) hm hm0 hml hbl H hmH hbH haH
    have hresultlen : (PlayerSpecificModularExecution.run model m b (c::cs)).1.length≤3 := by
      rw [PlayerSpecificModularExecution.value]
      have hr:=(PlayerSpecificModularHorner.reduced m b (c::cs) hm hm0).2
      omega
    have hf:=frame_cost model m b (c::cs) (PlayerSpecificModularExecution.run model m b (c::cs)).1 J W
      (mono hmH (by omega)) (mono hbH (by omega)) (mono haH (by omega)) hresultH hml hbl hal hresultlen (by omega) (by omega)
    simp only [PlayerSpecificModularExecution.run] at hf ⊢
    simp only [List.length_cons]
    change _≤200000000*(cs.length+1+1)*model.rat W
    nlinarith only [hsp,hxp,hap,hdp,hip,hf]

end Blotto.PlayerSpecificModularExecutionCost
