import Blotto.PlayerSpecificMonicizeExecution

/-! Actual monic long division with cached cancellation terms and source
traces. Every returned coefficient list refines the original algorithm. -/
namespace Blotto.PlayerSpecificMonicDivisionExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def header (q : Data) (fuel : ℕ) (current : Data) : Trace :=
  copyRow q++[.control fuel,.control current.length,.control q.length]

def run (q : Data) : ℕ → Data → (Data×Data)×Trace
  | 0,p =>
    let current := PlayerSpecificDenseExecution.trim p
    (([],current.1),current.2++header q 0 current.1++copyRow []++[.control 0])
  | fuel+1,p =>
    let current := PlayerSpecificDenseExecution.trim p
    let pre := current.2++header q (fuel+1) current.1
    if current.1=[] ∨ current.1.length<q.length then
      (([],current.1),pre++copyRow []++[.control 0]) else
      let canceled := PlayerSpecificCancellationExecution.run current.1 q
      let tail := run q fuel canceled.1.2
      let added := PlayerSpecificDenseExecution.add canceled.1.1 tail.1.1
      let quotient := PlayerSpecificDenseExecution.trim added.1
      ((quotient.1,tail.1.2),pre++canceled.2++tail.2++added.2++quotient.2++copyRow tail.1.2++[.control 1])

theorem value (q : Data) (fuel : ℕ) (p : Data) : (run q fuel p).1=PlayerSpecificMonicDivision.loop q fuel p := by
  induction fuel generalizing p with
  | zero => simp only [run,PlayerSpecificDenseExecution.trim_value,PlayerSpecificMonicDivision.loop]
  | succ fuel ih =>
    rw [run,PlayerSpecificMonicDivision.loop]
    simp only [PlayerSpecificDenseExecution.trim_value]
    split
    · rfl
    · simp only [PlayerSpecificDenseExecution.add_value,
        ih,PlayerSpecificCancellationExecution.term_value,PlayerSpecificCancellationExecution.remainder_value]

theorem heights (q : Data) (fuel : ℕ) (p : Data) (H : ℕ)
    (hq : HasHeight q H) (hp : HasHeight p H) (hql : q.length≤4) (hH : 1≤H) :
    HasHeight (run q fuel p).1.1 (PlayerSpecificLongDivisionHeights.height 4 fuel H) ∧
      HasHeight (run q fuel p).1.2 (PlayerSpecificLongDivisionHeights.height 4 fuel H) := by
  rw [value]
  exact PlayerSpecificLongDivisionHeights.loop_height q fuel p 4 H hq hp hql hH

theorem lengths (q : Data) (fuel : ℕ) (p : Data) (hq : Normalized q) (hm : (semantics q).Monic) :
    (run q fuel p).1.1.length≤p.length ∧ (run q fuel p).1.2.length≤p.length := by
  rw [value]
  exact ⟨PlayerSpecificCancellationHeights.monic_quotient_length q fuel p hq hm,
    PlayerSpecificCancellationHeights.monic_remainder_length q fuel p hq hm⟩

theorem bounded_heights (q : Data) (fuel : ℕ) (p : Data) (H : ℕ)
    (hq : HasHeight q H) (hp : HasHeight p H) (hql : q.length≤4) (hH : 1≤H) (hcap : fuel≤4) :
    HasHeight (run q fuel p).1.1 (16105*H+9665) ∧ HasHeight (run q fuel p).1.2 (16105*H+9665) := by
  have h := heights q fuel p H hq hp hql hH
  have hf := PlayerSpecificLongDivisionHeights.height_fuel_mono 4 H hcap
  change PlayerSpecificLongDivisionHeights.height 4 fuel H≤PlayerSpecificLongDivisionHeights.height 4 4 H at hf
  rw [PlayerSpecificLongDivisionHeights.fixed_degree_linear] at hf
  exact ⟨mono h.1 hf,mono h.2 hf⟩

end Blotto.PlayerSpecificMonicDivisionExecution
