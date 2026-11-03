import Blotto.PlayerSpecificTerminalPreparationSourceCost

/-! A complete terminal preparation bound in the original row height.
All intermediate total heights are derived inside the execution proof. -/
namespace Blotto.PlayerSpecificTerminalPreparationPolynomial
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def size (N T : ℕ) : ℕ := (N+2)*(T+1)+N+10
def coefficient : ℕ := PlayerSpecificTerminalPreparationSourceCost.polynomialCoefficient*16^3

theorem lower (N T : ℕ) : N+1≤size N T ∧ T≤size N T ∧ (N+1)*(T+1)≤size N T := by
  dsimp [size]
  constructor
  · nlinarith only [Nat.zero_le (N*T),Nat.zero_le T]
  constructor <;> nlinarith only [Nat.zero_le (N*T),Nat.zero_le N]

theorem size_bound (N T : ℕ) : size N T+1≤16*(N+1)*(T+1) := by
  dsimp [size]
  nlinarith only [Nat.zero_le (N*T),Nat.zero_le N,Nat.zero_le T]

theorem transfer (C N T S : ℕ) (hS : S+1≤16*(N+1)*(T+1)) :
    (N+1)*(C*(S+1)^3)≤(C*16^3)*(N+1)^4*(T+1)^3 := by
  calc
    _≤(N+1)*(C*(16*(N+1)*(T+1))^3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS 3))
    _=_ := by ring

theorem cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ) (T : ℕ)
    (hm : Normalized p.parameters.root.polynomial) (hm0 : p.parameters.root.polynomial≠[])
    (hml : p.parameters.root.polynomial.length≤4) (hmT : HasHeight p.parameters.root.polynomial T)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,B] T)
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi)
    (hl : ∀ j,Reduced p.parameters.root.polynomial (p.rows.read j).length ∧ HasHeight (p.rows.read j).length T)
    (hs : ∀ j,Reduced p.parameters.root.polynomial (s.data.read j) ∧ HasHeight (s.data.read j) T)
    (ha : s.active.length≤N) :
    (PlayerSpecificTerminalPreparationExecution.run RationalCostModel.schoolbook p s B).2≤coefficient*(N+1)^4*(T+1)^3 := by
  let S:=size N T
  have hlow:=lower N T
  have hc:=PlayerSpecificTerminalPreparationSourceCost.cost RationalCostModel.schoolbook p s B T S hm hm0 hml
    (mono hmT hlow.2.1) (mono he hlow.2.1) hv hlow.1 hl (fun j => ⟨(hs j).1,mono (hs j).2 hlow.2.1⟩) ha hlow.2.2
  exact (hc.trans (Nat.mul_le_mul_left (N+1) (PlayerSpecificTerminalPreparationSourceCost.work_polynomial S))).trans
    (transfer _ N T S (size_bound N T))

end Blotto.PlayerSpecificTerminalPreparationPolynomial
