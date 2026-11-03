import Blotto.PlayerSpecificCancellationHeights

/-! Uniform height bounds for the actual monic long-division recursion.
The fixed-degree specialization is linear in the original coefficient
height; its constant does not govern the executing isolator's precision. -/
namespace Blotto.PlayerSpecificLongDivisionHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificCancellationHeights
open PlayerSpecificPolynomialCancellation
set_option autoImplicit false
set_option maxHeartbeats 5000000

def stepHeight (N H : ℕ) : ℕ := H+(H+H+1)*(N+1)+1

def height (N : ℕ) : ℕ → ℕ → ℕ
  | 0,H => H+1
  | fuel+1,H => H+height N fuel (stepHeight N H)+1

theorem step_ge (N H : ℕ) : H≤stepHeight N H := by unfold stepHeight; omega

theorem height_ge (N fuel H : ℕ) : H≤height N fuel H := by cases fuel <;> simp only [height] <;> omega

theorem height_mono (N fuel : ℕ) : Monotone (height N fuel) := by
  intro H J h
  induction fuel generalizing H J with
  | zero => simpa only [height] using Nat.add_le_add_right h 1
  | succ fuel ih =>
    have hs : stepHeight N H≤stepHeight N J := by unfold stepHeight; gcongr
    exact Nat.add_le_add_right (Nat.add_le_add h (ih hs)) 1

theorem height_fuel_mono (N H : ℕ) : Monotone (fun fuel => height N fuel H) := by
  apply monotone_nat_of_le_succ
  intro fuel
  have h := height_mono N fuel (step_ge N H)
  change height N fuel H≤H+height N fuel (stepHeight N H)+1
  omega

theorem loop_height (q : Data) (fuel : ℕ) (p : Data) (N H : ℕ)
    (hq : HasHeight q H) (hp : HasHeight p H) (hN : q.length≤N) (hH : 1≤H) :
    HasHeight (PlayerSpecificMonicDivision.loop q fuel p).1 (height N fuel H) ∧
      HasHeight (PlayerSpecificMonicDivision.loop q fuel p).2 (height N fuel H) := by
  induction fuel generalizing p H with
  | zero => exact ⟨nil_height _,mono (trim_height hp) (by simp only [height]; omega)⟩
  | succ fuel ih =>
    rw [PlayerSpecificMonicDivision.loop]
    split
    · exact ⟨nil_height _,mono (trim_height hp) (height_ge _ _ _)⟩
    · have hr := remainder_height (trim p) q H H N (trim_height hp) hq hH hN
      have hs : 1≤stepHeight N H := hH.trans (step_ge N H)
      have ht := ih (remainder (trim p) q) (stepHeight N H) (mono hq (step_ge N H)) hr hs
      constructor
      · exact trim_height (add_height (term_height (trim p) q H (trim_height hp) hH) ht.1)
      · exact mono ht.2 (by simp only [height]; omega)

theorem run_height (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    HasHeight (PlayerSpecificMonicDivision.run p q).1 (height 4 4 H) ∧
      HasHeight (PlayerSpecificMonicDivision.run p q).2 (height 4 4 H) := by
  have h := loop_height q p.length p 4 H hq hp hql hH
  have hm := height_fuel_mono 4 H hpl
  exact ⟨mono h.1 hm,mono h.2 hm⟩

theorem fixed_degree_linear (H : ℕ) : height 4 4 H=16105*H+9665 := by
  simp only [height,stepHeight]
  ring

end Blotto.PlayerSpecificLongDivisionHeights
