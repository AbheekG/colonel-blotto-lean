import Blotto.PlayerSpecificCandidateTestExecution

/-! Original cell and selected-root heights give uniform widths for all
five actual raw-polynomial sign calls and the enclosing acceptance trace. -/
namespace Blotto.PlayerSpecificCandidateTestBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 2000000

def operandHeight (H T : ℕ) : ℕ := T+4*H+5
def size (H T : ℕ) : ℕ := operandHeight H T+1
def widthCoefficient : ℕ := 33*PlayerSpecificPolynomialSignBudget.widthCoefficient+128
def width (H T : ℕ) : ℕ := widthCoefficient*size H T
def signWorkCoefficient : ℕ := 33*PlayerSpecificPolynomialSignCost.workCoefficient
def workCoefficient : ℕ := 5*signWorkCoefficient+2000

theorem encoded_input (m p : Data) (node : Interval) (G : ℕ) (hm : HasHeight m G)
    (hp : HasHeight p G) (he : HasHeight [node.lo,node.hi] G) (hml : m.length≤4) (hpl : p.length≤4) :
    PlayerSpecificPolynomialSignBudget.inputHeight m p node≤32*(G+1) := by
  have hmi:=inputHeight_le hm
  have hpi:=inputHeight_le hp
  have hei:=inputHeight_le he
  have hmc:=Nat.mul_le_mul_right (1+2*G) hml
  have hpc:=Nat.mul_le_mul_right (1+2*G) hpl
  simp only [List.length_cons,List.length_nil] at hei
  unfold PlayerSpecificPolynomialSignBudget.inputHeight PlayerSpecificSignLinearSizes.inputHeight
    PlayerSpecificSignEnclosure.endpointHeight
  omega

theorem width_large (H T : ℕ) :
    128*(H+1)≤width H T ∧ 1+2*operandHeight H T≤width H T ∧ 32≤width H T := by
  have hm:=Nat.mul_le_mul_right (size H T) (show 128≤widthCoefficient by unfold widthCoefficient; omega)
  unfold width size operandHeight at *
  omega

theorem sign_work_profile (C S G : ℕ) (hS : S≤32*(G+1)) : C*(S+1)≤(33*C)*(G+1) := by
  have hh : S+1≤33*(G+1) := by omega
  calc
    _ ≤ C*(33*(G+1)) := Nat.mul_le_mul_left C hh
    _ = _ := by ring

theorem sign_width (H T S : ℕ) (hS : S≤32*size H T) :
    PlayerSpecificPolynomialSignBudget.width S≤width H T := by
  have hp:=sign_work_profile PlayerSpecificPolynomialSignBudget.widthCoefficient S (operandHeight H T) hS
  have hm:=Nat.mul_le_mul_right (size H T)
    (show 33*PlayerSpecificPolynomialSignBudget.widthCoefficient≤widthCoefficient by unfold widthCoefficient; omega)
  exact hp.trans hm

def Bounded (p : Data) (G : ℕ) : Prop := HasHeight p G ∧ p.length≤4

theorem tests_bounds (c : PlayerSpecificRationalCells.Cell) (H : ℕ)
    (hc : PlayerSpecificRationalCellHeights.CellHeight c H) (hH : 1≤H) :
    let tests:=(PlayerSpecificCellTestConstruction.run c).1
    Bounded tests.positive (4*H+4) ∧ Bounded tests.lower (4*H+4) ∧
      (∀ p∈tests.upper,Bounded p (4*H+4)) ∧
      Bounded tests.first (4*H+4) ∧ Bounded tests.second (4*H+4) := by
  have hv:=PlayerSpecificCellTestConstruction.values c
  have ht:=PlayerSpecificCellPolynomialHeights.tests c H hc hH
  dsimp only
  rw [hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2]
  refine ⟨⟨ht.1,by decide⟩,⟨ht.2.1,by simp [PlayerSpecificAlgebraicCellTests.lower]⟩,?_,
    ⟨ht.2.2.2.1,by simp [PlayerSpecificAlgebraicCellTests.firstGate]⟩,
    ⟨ht.2.2.2.2,by simp [PlayerSpecificAlgebraicCellTests.secondGate]⟩⟩
  intro p hp
  cases hu : c.upper with
  | none => simp only [hu,Option.map_none,Option.not_mem_none] at hp
  | some q =>
    have he : PlayerSpecificAlgebraicCellTests.upper q=p := by
      simpa only [hu,Option.map_some,Option.mem_def,Option.some.injEq] using hp
    rw [←he]
    exact ⟨ht.2.2.1 q (by rw [hu]; exact Option.mem_some_self _),by simp [PlayerSpecificAlgebraicCellTests.upper]⟩

end Blotto.PlayerSpecificCandidateTestBudget
