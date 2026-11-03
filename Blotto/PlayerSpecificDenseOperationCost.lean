import Blotto.PlayerSpecificCompositeTraceFits

/-! One explicit polynomial source-price envelope covers every actual dense
elementary operation. In fixed degree it has linear operand width and a
constant number of rational-primitive/copy/control events. -/
namespace Blotto.PlayerSpecificDenseOperationCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def traceCap (N : ℕ) : ℕ := 1000*(N+1)^3
def cost (model : RationalCostModel) (H N : ℕ) : ℕ :=
  3*traceCap N*model.rat (PlayerSpecificCompositeTraceFits.width H N)

theorem dense_width (H N : ℕ) : PlayerSpecificDenseTraceFits.width H N≤PlayerSpecificCompositeTraceFits.width H N := by
  have h := PlayerSpecificCompositeTraceFits.height_ge H N
  unfold PlayerSpecificDenseTraceFits.width PlayerSpecificCompositeTraceFits.width
  omega

theorem readonly_width (H N : ℕ) : PlayerSpecificReadOnlyTraceFits.width H N≤PlayerSpecificCompositeTraceFits.width H N := by
  have h := PlayerSpecificCompositeTraceFits.height_ge H N
  unfold PlayerSpecificReadOnlyTraceFits.width PlayerSpecificCompositeTraceFits.width
  omega

theorem trace_price (model : RationalCostModel) (H N : ℕ) (trace : Trace)
    (hf : Fits (PlayerSpecificCompositeTraceFits.width H N) trace) (hl : trace.length≤traceCap N) :
    price model trace≤cost model H N := by
  have hp := price_bound model (PlayerSpecificCompositeTraceFits.width H N)
    (by unfold PlayerSpecificCompositeTraceFits.width; omega) trace hf
  have hm := Nat.mul_le_mul_right (3*model.rat (PlayerSpecificCompositeTraceFits.width H N)) hl
  unfold cost
  nlinarith

theorem recursive_cap (N n : ℕ) (hn : n≤N) : PlayerSpecificCompositeTraceLength.recursiveLength N*(n+1)≤traceCap N := by
  have h := Nat.mul_le_mul_left (100*(N+1)^2) (Nat.add_le_add_right hn 1)
  unfold PlayerSpecificCompositeTraceLength.recursiveLength traceCap
  nlinarith

theorem square_cap (N : ℕ) : 1000*(N+1)^2≤traceCap N := by
  have h := Nat.mul_le_mul_left ((N+1)^2) (show 1≤N+1 by omega)
  rw [Nat.mul_one,← pow_succ] at h
  exact Nat.mul_le_mul_left 1000 h

theorem add_cost (model : RationalCostModel) (p q : Data) (H N : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hpl : p.length≤N) (hql : q.length≤N) :
    price model (PlayerSpecificDenseExecution.add p q).2≤cost model H N := by
  apply trace_price
  · exact fits_mono (PlayerSpecificDenseTraceFits.add_fits p q H N hp hq hpl hql) (dense_width H N)
  · have h := PlayerSpecificDenseTraceLength.add_length p q N hpl hql
    have hm := Nat.mul_le_mul_left (N+10) (show p.length+q.length+1≤2*N+1 by omega)
    apply le_trans ?_ (square_cap N)
    nlinarith

theorem scale_cost (model : RationalCostModel) (a : ℚ) (p : Data) (H N : ℕ)
    (ha : RationalHeight a H) (hp : HasHeight p H) (hlen : p.length≤N) :
    price model (PlayerSpecificDenseExecution.scale a p).2≤cost model H N := by
  apply trace_price
  · exact fits_mono (PlayerSpecificDenseTraceFits.scale_fits a p H N ha hp hlen) (dense_width H N)
  · have h := PlayerSpecificDenseTraceLength.scale_length a p N hlen
    have hm := Nat.mul_le_mul_left (N+8) (Nat.add_le_add_right hlen 1)
    apply le_trans ?_ (square_cap N)
    nlinarith

theorem shift_cost (model : RationalCostModel) (p : Data) (H N : ℕ)
    (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤N) :
    price model (PlayerSpecificDenseExecution.shift p).2≤cost model H N := by
  apply trace_price
  · exact fits_mono (PlayerSpecificReadOnlyTraceFits.shift_fits p H N hp hH hlen) (readonly_width H N)
  · rw [PlayerSpecificDenseTraceLength.shift_length]
    apply le_trans ?_ (square_cap N)
    nlinarith

theorem trim_cost (model : RationalCostModel) (p : Data) (H N : ℕ)
    (hp : HasHeight p H) (hlen : p.length≤N) :
    price model (PlayerSpecificDenseExecution.trim p).2≤cost model H N := by
  apply trace_price
  · exact fits_mono (PlayerSpecificReadOnlyTraceFits.trim_fits p H N hp hlen) (readonly_width H N)
  · have h := PlayerSpecificDenseTraceLength.trim_length p N hlen
    have hm := Nat.mul_le_mul_left (N+8) (Nat.add_le_add_right hlen 1)
    apply le_trans ?_ (square_cap N)
    nlinarith

theorem subtract_cost (model : RationalCostModel) (p q : Data) (H N : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤N) (hql : q.length≤N) :
    price model (PlayerSpecificDenseExecution.subtract p q).2≤cost model H N := by
  apply trace_price
  · exact fits_mono (PlayerSpecificReadOnlyTraceFits.subtract_fits p q H N hp hq hH hpl hql) (dense_width H N)
  · have h := PlayerSpecificCompositeTraceLength.subtract_length p q N hpl hql
    apply le_trans ?_ (square_cap N)
    nlinarith

theorem multiply_cost (model : RationalCostModel) (p q : Data) (H N : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hpl : p.length≤N) (hql : q.length≤N) :
    price model (PlayerSpecificDenseExecution.multiply p q).2≤cost model H N := by
  apply trace_price
  · exact PlayerSpecificCompositeTraceFits.multiply_fits p q H N hp hq hpl hql
  · exact (PlayerSpecificCompositeTraceLength.multiply_length p q N hpl hql).trans (recursive_cap N p.length hpl)

theorem derivative_cost (model : RationalCostModel) (p : Data) (H N : ℕ)
    (hp : HasHeight p H) (hlen : p.length≤N) :
    price model (PlayerSpecificDenseExecution.derivative p).2≤cost model H N := by
  apply trace_price
  · exact PlayerSpecificCompositeTraceFits.derivative_fits p H N hp hlen
  · exact (PlayerSpecificCompositeTraceLength.derivative_length p N hlen).trans (recursive_cap N p.length hlen)

theorem fixed_degree_price (model : RationalCostModel) (H : ℕ) : cost model H 4=375000*model.rat (40*H+64) := by
  unfold cost traceCap PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height
  congr 2
  ring

end Blotto.PlayerSpecificDenseOperationCost
