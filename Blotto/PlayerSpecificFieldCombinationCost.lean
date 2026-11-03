import Blotto.PlayerSpecificFieldCombination

/-! Complete fixed-degree source prices for actual addition/subtraction
and reduction, including all retained and returned rows. -/
namespace Blotto.PlayerSpecificFieldCombinationCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificFieldCombination
set_option autoImplicit false
set_option maxHeartbeats 3000000

def widthCoefficient : ℕ := 4*1000000^6+1024*100001+4096
def width (H : ℕ) : ℕ := widthCoefficient*(H+1)

theorem large (H : ℕ) : 1024*100001*(H+1)≤width H :=
  Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega)

theorem copy_profile (H W : ℕ) (hh : 1024*100001*(H+1)≤W) : 1+2*(100000*(H+1))≤W := by
  nlinarith only [hh]

theorem copy_width (H : ℕ) : 1+2*(100000*(H+1))≤width H := copy_profile H (width H) (large H)

theorem raw_cost (model : RationalCostModel) (difference : Bool) (a b : Data) (H : ℕ)
    (ha : HasHeight a H) (hb : HasHeight b H) (hH : 1≤H) (hal : a.length≤3) (hbl : b.length≤3) :
    price model (raw difference a b).2≤375000*model.rat (40*H+64) := by
  cases difference
  · exact (PlayerSpecificDenseOperationCost.fixed_degree_price model H) ▸
      (PlayerSpecificDenseOperationCost.add_cost model a b H 4 ha hb (by omega) (by omega))
  · exact (PlayerSpecificDenseOperationCost.fixed_degree_price model H) ▸
      (PlayerSpecificDenseOperationCost.subtract_cost model a b H 4 ha hb hH (by omega) (by omega))

theorem run_cost (model : RationalCostModel) (difference : Bool) (m a b : Data)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4)
    (H : ℕ) (hmH : HasHeight m H) (haH : HasHeight a H) (hbH : HasHeight b H)
    (hH : 1≤H) (hal : a.length≤3) (hbl : b.length≤3) :
    price model (run difference m a b).2≤200000000*model.rat (width H) := by
  have hw:=large H
  have hr:=raw_bounds difference a b H haH hbH hal hbl
  have hc:=raw_cost model difference a b H haH hbH hH hal hbl
  have hcp:=hc.trans (Nat.mul_le_mul_left 375000 (model.monotone (by omega : 40*H+64≤width H)))
  have hd:=PlayerSpecificDivisionTraceCost.run_cost model (raw difference a b).1 m (2*H+1) hr.1
    (mono hmH (by omega)) (by omega) hr.2 hml
  have hdw : 2*1000000^6*(2*H+1+1)≤width H := by unfold width widthCoefficient; omega
  have hdp:=hd.trans (Nat.mul_le_mul_left 100000000 (model.monotone hdw))
  have hres:=bounds difference m a b H hmH haH hbH hml hal hbl
  have hlen : (run difference m a b).1.length≤3 := by
    have hl:=(reduced difference m a b hm hm0).2
    omega
  have hpost : H≤100000*(H+1) := by omega
  have hHW:=copy_width H
  have hW : 32≤width H := by omega
  have hmp:=PlayerSpecificExtendedCopyCost.row_cost model m _ (width H) (mono hmH hpost) (by omega) hHW hW
  have hap:=PlayerSpecificExtendedCopyCost.row_cost model a _ (width H) (mono haH hpost) (by omega) hHW hW
  have hbp:=PlayerSpecificExtendedCopyCost.row_cost model b _ (width H) (mono hbH hpost) (by omega) hHW hW
  have hop:=PlayerSpecificExtendedCopyCost.row_cost model (run difference m a b).1 _ (width H) hres (by omega) hHW hW
  have hctrl:=event_price model (width H) (by omega) (.control 3) ((control_width 3).trans (by omega))
  change price model [.control 3]≤3*model.rat (width H) at hctrl
  rw [run]
  dsimp only [run] at hop
  dsimp only
  simp only [price_append]
  nlinarith only [hcp,hdp,hmp,hap,hbp,hop,hctrl]

end Blotto.PlayerSpecificFieldCombinationCost
