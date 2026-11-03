import Blotto.PlayerSpecificCellTestConstruction

/-! Complete cell and returned-test copies at their actual coefficient
sizes, with every optional boundary tag included. -/
namespace Blotto.PlayerSpecificCellTestCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalTrace PlayerSpecificCellTestConstruction
set_option autoImplicit false
set_option maxHeartbeats 2000000

def width (H : ℕ) : ℕ := 128*(H+1)

theorem control (model : RationalCostModel) (H n : ℕ) (hn : n≤5) : price model [.control n]≤3*model.rat (width H) := by
  exact event_price model (width H) (by unfold width; omega) (.control n)
    ((PlayerSpecificRationalTrace.control_width n).trans (by unfold width; omega))

theorem cell_cost (model : RationalCostModel) (c : Cell) (H : ℕ) (hc : CellHeight c H) :
    price model (copyCell c)≤135*model.rat (width H) := by
  have hrow : HasHeight [c.state.coefficients.A1,c.state.coefficients.A2,c.state.coefficients.B1,c.state.coefficients.B2,
      c.state.prefixMax,c.lower,c.suffixMax] H :=
    cons_height hc.1.1 (cons_height hc.1.2.1 (cons_height hc.1.2.2.1 (cons_height hc.1.2.2.2.1
      (cons_height hc.1.2.2.2.2 (cons_height hc.2.1 (cons_height hc.2.2.2 (nil_height H)))))))
  have hupper : HasHeight c.upper.toList H := by
    cases hu : c.upper with
    | none => exact nil_height H
    | some q => exact cons_height (hc.2.2.1 q (by rw [hu]; exact Option.mem_some_self _)) (nil_height H)
  have hp:=PlayerSpecificExtendedCopyCost.row_cost model _ H (width H) hrow (by simp) (by unfold width; omega) (by unfold width; omega)
  have hu:=PlayerSpecificExtendedCopyCost.row_cost model _ H (width H) hupper
    (by cases c.upper <;> simp) (by unfold width; omega) (by unfold width; omega)
  have hm:=control model H 1 (by decide)
  simp only [copyCell,price_append]
  nlinarith only [hp,hu,hm]

theorem result_cost (model : RationalCostModel) (c : Cell) (H : ℕ) (hc : CellHeight c H) (hH : 1≤H) :
    price model (copyResult (run c).1)≤333*model.rat (width H) := by
  have hv:=values c
  have ht:=PlayerSpecificCellPolynomialHeights.tests c H hc hH
  have hHW : 1+2*(4*H+4)≤width H := by unfold width; omega
  have hW : 32≤width H := by unfold width; omega
  have hp:=PlayerSpecificExtendedCopyCost.row_cost model (run c).1.positive (4*H+4) (width H)
    (by rw [hv.1]; exact ht.1) (by rw [hv.1]; decide) hHW hW
  have hl:=PlayerSpecificExtendedCopyCost.row_cost model (run c).1.lower (4*H+4) (width H)
    (by rw [hv.2.1]; exact ht.2.1) (by rw [hv.2.1]; simp [PlayerSpecificAlgebraicCellTests.lower]) hHW hW
  have hf:=PlayerSpecificExtendedCopyCost.row_cost model (run c).1.first (4*H+4) (width H)
    (by rw [hv.2.2.2.1]; exact ht.2.2.2.1) (by rw [hv.2.2.2.1]; simp [PlayerSpecificAlgebraicCellTests.firstGate]) hHW hW
  have hs:=PlayerSpecificExtendedCopyCost.row_cost model (run c).1.second (4*H+4) (width H)
    (by rw [hv.2.2.2.2]; exact ht.2.2.2.2) (by rw [hv.2.2.2.2]; simp [PlayerSpecificAlgebraicCellTests.secondGate]) hHW hW
  have hu : price model (match (run c).1.upper with | none => [.control 0] | some row => copyRow row++[.control 1])≤69*model.rat (width H) := by
    rw [hv.2.2.1]
    cases he : c.upper with
    | none => exact (control model H 0 (by decide)).trans (Nat.mul_le_mul_right _ (by decide : 3≤69))
    | some q =>
      have hq:=ht.2.2.1 q (by rw [he]; exact Option.mem_some_self _)
      have hp:=PlayerSpecificExtendedCopyCost.row_cost model (PlayerSpecificAlgebraicCellTests.upper q) (4*H+4) (width H) hq
        (by simp [PlayerSpecificAlgebraicCellTests.upper]) hHW hW
      have hm:=control model H 1 (by decide)
      simp only [Option.map_some,price_append]
      omega
  simp only [copyResult,price_append]
  calc
    _ ≤ 66*model.rat (width H)+66*model.rat (width H)+66*model.rat (width H)+
        66*model.rat (width H)+69*model.rat (width H) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp hl) hf) hs) hu
    _ = _ := by ring

end Blotto.PlayerSpecificCellTestCopyCost
