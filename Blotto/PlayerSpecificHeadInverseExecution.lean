import Blotto.PlayerSpecificSquarefreeTraceCost

/-! An actual head/default read followed by rational inversion. Scanned row
copies, the returned head, control words and arithmetic are all charged. -/
namespace Blotto.PlayerSpecificHeadInverseExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def run (p : Data) : ℚ×Trace :=
  let head := p.headD 0
  let inverted := scalar .divide 1 head
  (inverted.1,copyRow p++[.copy head,.control p.length]++inverted.2)

theorem value (p : Data) : (run p).1=(p.headD 0)⁻¹ := by
  simp only [run,scalar,Arithmetic.apply,one_div]

theorem height (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) : RationalHeight (run p).1 H := by
  rw [value]
  exact (PlayerSpecificSquarefreeHeights.headD_height p H hp hH).inv

def width (H N : ℕ) : ℕ := 2*H+N+8

theorem run_cost (model : RationalCostModel) (p : Data) (H N : ℕ)
    (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤N) :
    price model (run p).2≤3*(N+8)*model.rat (width H N) := by
  have hh:=PlayerSpecificSquarefreeHeights.headD_height p H hp hH
  have hw : 1+2*H≤width H N := by unfold width; omega
  have hr := copyRow_fits (width H N) p
    (fun q hq => (rationalWordWidth_of_height (hp q hq)).trans hw) (by unfold width; omega)
  have hf : Fits (width H N) [.copy (p.headD 0),.control p.length] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact (rationalWordWidth_of_height hh).trans hw
    · exact (control_width _).trans (by unfold width; omega)
  have hiH : RationalHeight (Arithmetic.divide.apply 1 (p.headD 0)) H := by
    simpa only [Arithmetic.apply,one_div] using hh.inv
  have hi := scalar_fits (width H N) .divide 1 (p.headD 0)
    ((rationalWordWidth_of_height (one_height.mono hH)).trans hw)
    ((rationalWordWidth_of_height hh).trans hw) ((rationalWordWidth_of_height hiH).trans hw) (by unfold width; omega)
  have hall : Fits (width H N) (run p).2 := by
    simpa only [run,fits_append] using And.intro (And.intro hr hf) hi
  have hc := price_bound model (width H N) (by unfold width; omega) _ hall
  have hl : (run p).2.length≤N+8 := by
    simp only [run,List.length_append,copyRow_length,scalar_length,List.length_cons,List.length_nil]
    omega
  exact hc.trans (Nat.mul_le_mul_right (model.rat (width H N)) (Nat.mul_le_mul_left 3 hl))

end Blotto.PlayerSpecificHeadInverseExecution
