import Blotto.PlayerSpecificExtendedCopyCost

/-! Complete source price for the executed Bezout algorithm. All polynomial
and coefficient-update intermediates have derived fixed-degree length and
height bounds; no coefficient or aggregate price oracle is supplied. -/
namespace Blotto.PlayerSpecificExtendedGCDTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificExtendedGCDExecution PlayerSpecificEuclideanBudget
set_option autoImplicit false
set_option maxHeartbeats 7000000

theorem terminal_cost (model : RationalCostModel) (fuel : ℕ) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) (hcap : fuel≤4) :
    let current := PlayerSpecificDenseExecution.trim p
    let result : PlayerSpecificExtendedGCD.Result := ⟨current.1,[1],[]⟩
    price model (PlayerSpecificGCDExecution.header fuel p q++current.2++copyResult result++[.control 0])≤
      1000000*model.rat (width fuel H) := by
  let current := PlayerSpecificDenseExecution.trim p
  let result : PlayerSpecificExtendedGCD.Result := ⟨current.1,[1],[]⟩
  have hW := width_large fuel H
  have hW6 : 6≤width fuel H := (by decide : 6≤32).trans hW
  have hHW := PlayerSpecificGCDTraceCost.input_width fuel H
  have hh := PlayerSpecificGCDTraceCost.header_cost model fuel p q H (width fuel H) hp hq hpl hql hcap hHW hW6
  have hcH : HasHeight current.1 H := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_height hp
  have hcl : current.1.length≤4 := by rw [PlayerSpecificDenseExecution.trim_value]; exact (trim_length p).trans hpl
  have ht := PlayerSpecificDenseOperationCost.trim_cost model p H 4 hp hpl
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at ht
  have htp : price model current.2≤375000*model.rat (width fuel H) :=
    ht.trans (Nat.mul_le_mul_left 375000 (model.monotone (dense_width fuel H)))
  have hlH : HasHeight [1] H := cons_height (one_height.mono hH) (nil_height _)
  have hcopy := PlayerSpecificExtendedCopyCost.result_cost model result H (width fuel H) hcH hlH (nil_height _)
    (hcl.trans (by decide)) (by change (1:ℕ)≤21; decide) (by change (0:ℕ)≤21; decide) hHW hW
  have hf := PlayerSpecificMonicDivisionBudget.control_cost model 0 (width fuel H) (by decide) hW6
  change price model (PlayerSpecificGCDExecution.header fuel p q++current.2++copyResult result++[.control 0])≤_
  simp only [price_append]
  nlinarith

theorem loop_cost (model : RationalCostModel) (fuel : ℕ) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) (hcap : fuel≤4) :
    price model (loop fuel p q).2≤300000000*(fuel+1)*model.rat (width fuel H) := by
  induction fuel generalizing p q H with
  | zero =>
    have h := terminal_cost model 0 p q H hp hq hH hpl hql hcap
    change price model (loop 0 p q).2≤1000000*model.rat (width 0 H) at h
    nlinarith
  | succ fuel ih =>
    have hW := width_large (fuel+1) H
    have hW6 : 6≤width (fuel+1) H := (by decide : 6≤32).trans hW
    have hh := PlayerSpecificGCDTraceCost.header_cost model (fuel+1) p q H (width (fuel+1) H) hp hq hpl hql hcap
      (PlayerSpecificGCDTraceCost.input_width (fuel+1) H) hW6
    have hf := PlayerSpecificMonicDivisionBudget.control_cost model 1 (width (fuel+1) H) (by decide) hW6
    rw [loop]
    split
    · have ht := terminal_cost model (fuel+1) p q H hp hq hH hpl hql hcap
      dsimp only at ht
      have hm := Nat.mul_le_mul_right (model.rat (width (fuel+1) H)) (show 1≤fuel+1+1 by omega)
      nlinarith
    · let divided := PlayerSpecificDivisionExecution.run p q
      have hd := PlayerSpecificDivisionTraceCost.run_cost model p q H hp hq hH hpl hql
      have hdp : price model divided.2≤100000000*model.rat (width (fuel+1) H) :=
        hd.trans (Nat.mul_le_mul_left 100000000 (model.monotone (division_width (fuel+1) H)))
      have hdiv := PlayerSpecificDivisionExecution.heights p q H hp hq hH hpl hql
      have hquot : HasHeight divided.1.1 (step H) := hdiv.1
      have hrem : HasHeight divided.1.2 (step H) := hdiv.2
      have hdlen := PlayerSpecificDivisionExecution.lengths p q
      have hquotlen : divided.1.1.length≤4 := hdlen.1.trans hpl
      have hremlen : divided.1.2.length≤4 := hdlen.2.trans hpl
      have hqnext := mono hq (step_ge H)
      have hstep : 1≤step H := hH.trans (step_ge H)
      have hfcap : fuel≤4 := by omega
      have hi := ih q divided.1.2 (step H) hqnext hrem hstep hql hremlen hfcap
      let rest := loop fuel q divided.1.2
      have hip : price model rest.2≤300000000*(fuel+1)*model.rat (width (fuel+1) H) :=
        hi.trans (Nat.mul_le_mul_left (300000000*(fuel+1)) (model.monotone (next_width fuel H)))
      have hb := loop_bounds fuel q divided.1.2 (step H) hqnext hrem hstep hql hremlen hfcap
      let T := PlayerSpecificExtendedGCDHeights.linearConstant*(step H+1)
      have hgH : HasHeight rest.1.gcd T := hb.1
      have hlH : HasHeight rest.1.left T := hb.2.1
      have hrH : HasHeight rest.1.right T := hb.2.2.1
      have hgl : rest.1.gcd.length≤4 := hb.2.2.2.1
      have hll : rest.1.left.length≤17 := hb.2.2.2.2.1
      have hrl : rest.1.right.length≤17 := hb.2.2.2.2.2
      let product := PlayerSpecificDenseExecution.multiply divided.1.1 rest.1.right
      let difference := PlayerSpecificDenseExecution.subtract rest.1.left product.1
      let normalized := PlayerSpecificDenseExecution.trim difference.1
      let result : PlayerSpecificExtendedGCD.Result := ⟨rest.1.gcd,rest.1.right,normalized.1⟩
      have hprod : HasHeight product.1 ((step H+T+1)*5) := by
        rw [PlayerSpecificDenseExecution.multiply_value]
        exact mono (s := (step H+T+1)*(divided.1.1.length+1)) (t := (step H+T+1)*5)
          (multiply_height hquot hrH) (Nat.mul_le_mul_left _ (by omega))
      have hprodPost : HasHeight product.1 (postHeight H) :=
        mono (s := (step H+T+1)*5) (t := postHeight H) hprod (product_height H)
      have hprodl : product.1.length≤21 := by
        rw [PlayerSpecificDenseExecution.multiply_value]
        exact (PlayerSpecificDensePolynomial.multiply_length divided.1.1 rest.1.right).trans (by omega)
      have hdiff : HasHeight difference.1 (postHeight H) := by
        rw [PlayerSpecificDenseExecution.subtract_value]
        exact mono (s := T+(step H+T+1)*5+1) (t := postHeight H) (subtract_height hlH hprod) (update_height H)
      have hdiffl : difference.1.length≤21 := by
        rw [PlayerSpecificDenseExecution.subtract_value,PlayerSpecificDensePolynomial.subtract,
          PlayerSpecificDensePolynomial.add_length,PlayerSpecificDensePolynomial.scale_length]
        exact max_le (by omega) hprodl
      have hnorm : HasHeight normalized.1 (postHeight H) := by
        rw [PlayerSpecificDenseExecution.trim_value]
        exact trim_height hdiff
      have hnorml : normalized.1.length≤21 := by
        rw [PlayerSpecificDenseExecution.trim_value]
        exact (trim_length difference.1).trans hdiffl
      have hpost : 1≤postHeight H := hH.trans (post_ge H)
      have hqp := mono (s := step H) (t := postHeight H) hquot (step_le_post H)
      have hgp := mono (s := T) (t := postHeight H) hgH (tail_height H)
      have hlp := mono (s := T) (t := postHeight H) hlH (tail_height H)
      have hrp := mono (s := T) (t := postHeight H) hrH (tail_height H)
      have hmp := PlayerSpecificDenseOperationCost.multiply_cost model divided.1.1 rest.1.right (postHeight H) 21
        hqp hrp (by omega) (by omega)
      change price model product.2≤31944000*model.rat (PlayerSpecificCompositeTraceFits.width (postHeight H) 21) at hmp
      have hmprice : price model product.2≤31944000*model.rat (width (fuel+1) H) :=
        hmp.trans (Nat.mul_le_mul_left 31944000 (model.monotone (post_width (fuel+1) H)))
      have hsp := PlayerSpecificDenseOperationCost.subtract_cost model rest.1.left product.1 (postHeight H) 21
        hlp hprodPost hpost (by omega) hprodl
      change price model difference.2≤31944000*model.rat (PlayerSpecificCompositeTraceFits.width (postHeight H) 21) at hsp
      have hsprice : price model difference.2≤31944000*model.rat (width (fuel+1) H) :=
        hsp.trans (Nat.mul_le_mul_left 31944000 (model.monotone (post_width (fuel+1) H)))
      have hnp := PlayerSpecificDenseOperationCost.trim_cost model difference.1 (postHeight H) 21 hdiff hdiffl
      change price model normalized.2≤31944000*model.rat (PlayerSpecificCompositeTraceFits.width (postHeight H) 21) at hnp
      have hnprice : price model normalized.2≤31944000*model.rat (width (fuel+1) H) :=
        hnp.trans (Nat.mul_le_mul_left 31944000 (model.monotone (post_width (fuel+1) H)))
      have hcopy := PlayerSpecificExtendedCopyCost.result_cost model result (postHeight H) (width (fuel+1) H)
        hgp hrp hnorm (hgl.trans (by decide : 4≤21)) (hrl.trans (by decide : 17≤21)) hnorml (copy_width (fuel+1) H) hW
      change price model (PlayerSpecificGCDExecution.header (fuel+1) p q++divided.2++rest.2++product.2++difference.2++
        normalized.2++copyResult result++[.control 1])≤_
      simp only [price_append]
      nlinarith

theorem run_cost (model : RationalCostModel) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    price model (run p q).2≤2000000000*model.rat (PlayerSpecificGCDTraceCost.capWidth H) := by
  let divisor := PlayerSpecificDenseExecution.trim q
  have hdH : HasHeight divisor.1 H := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_height hq
  have hdl : divisor.1.length≤4 := by rw [PlayerSpecificDenseExecution.trim_value]; exact (trim_length q).trans hql
  have hc := loop_cost model divisor.1.length p divisor.1 H hp hdH hH hpl hdl hdl
  have hw := model.monotone (width_cap divisor.1.length H hdl)
  have hloop := hc.trans (Nat.mul_le_mul_left (300000000*(divisor.1.length+1)) hw)
  have hfactor := Nat.mul_le_mul_right (model.rat (PlayerSpecificGCDTraceCost.capWidth H))
    (show 300000000*(divisor.1.length+1)≤1500000000 by omega)
  have hloop' : price model (loop divisor.1.length p divisor.1).2≤1500000000*model.rat (PlayerSpecificGCDTraceCost.capWidth H) := hloop.trans hfactor
  have hbase := PlayerSpecificDenseOperationCost.trim_cost model q H 4 hq hql
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hbase
  have htrim : price model divisor.2≤375000*model.rat (PlayerSpecificGCDTraceCost.capWidth H) :=
    hbase.trans (Nat.mul_le_mul_left 375000 (model.monotone ((dense_width 0 H).trans (width_cap 0 H (by omega)))))
  have hW : 6≤PlayerSpecificGCDTraceCost.capWidth H :=
    ((by decide : 6≤32).trans (width_large 0 H)).trans (width_cap 0 H (by omega))
  have hmeta := PlayerSpecificMonicDivisionBudget.control_cost model divisor.1.length (PlayerSpecificGCDTraceCost.capWidth H) hdl hW
  change price model (divisor.2++(loop divisor.1.length p divisor.1).2++[.control divisor.1.length])≤_
  simp only [price_append]
  nlinarith

end Blotto.PlayerSpecificExtendedGCDTraceCost
