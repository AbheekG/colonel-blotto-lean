import Blotto.PlayerSpecificCertificateTraceCost

/-! Executed signed-remainder row preparation with cached derivatives and
complete row-list copies. Its numerical return is the checked Sturm chain. -/
namespace Blotto.PlayerSpecificSturmExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def copyRows (rows : List Data) : Trace := .control rows.length::rows.flatMap copyRow

def next (p q : Data) : Data×Trace :=
  let divided := PlayerSpecificDivisionExecution.run p q
  let negated := PlayerSpecificDenseExecution.scale (-1) divided.1.2
  let normalized := PlayerSpecificDenseExecution.trim negated.1
  (normalized.1,divided.2++negated.2++normalized.2++copyRow normalized.1++[.control 1])

theorem next_value (p q : Data) : (next p q).1=PlayerSpecificSturmSequence.next p q := by
  simp only [next,PlayerSpecificDenseExecution.trim_value,PlayerSpecificDenseExecution.scale_value,
    PlayerSpecificDivisionExecution.value,PlayerSpecificSturmSequence.next]

def chain : ℕ → Data → Data → List Data×Trace
  | 0,p,q =>
    let pre := PlayerSpecificGCDExecution.header 0 p q
    if q=[] then ([],pre++[.control 0]) else ([q],pre++copyRows [q]++[.control 1])
  | fuel+1,p,q =>
    let pre := PlayerSpecificGCDExecution.header (fuel+1) p q
    if q=[] then ([],pre++[.control 0]) else
      let successor := next p q
      let rest := chain fuel q successor.1
      let result := q::rest.1
      (result,pre++successor.2++rest.2++copyRows result++[.control 1])

theorem chain_value (fuel : ℕ) (p q : Data) : (chain fuel p q).1=PlayerSpecificSturmSequence.chain fuel p q := by
  induction fuel generalizing p q with
  | zero => rw [chain,PlayerSpecificSturmSequence.chain]; split <;> rfl
  | succ fuel ih =>
    rw [chain,PlayerSpecificSturmSequence.chain]
    split
    · rfl
    · simp only [ih,next_value]

theorem chain_length (fuel : ℕ) (p q : Data) : (chain fuel p q).1.length≤fuel+1 := by
  induction fuel generalizing p q with
  | zero => rw [chain]; split <;> simp only [List.length_nil,List.length_cons] <;> omega
  | succ fuel ih =>
    have h := ih q (next p q).1
    rw [chain]
    split <;> simp only [List.length_nil,List.length_cons] <;> omega

theorem chain_bounds (fuel : ℕ) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) (hcap : fuel≤4) :
    ∀ row∈(chain fuel p q).1,HasHeight row (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧ row.length≤4 := by
  rw [chain_value]
  intro row hr
  have h := PlayerSpecificSturmHeights.chain_bounds fuel p q H hp hq hH hpl hql row hr
  exact ⟨mono h.1 ((PlayerSpecificExtendedGCDHeights.fuel_mono H hcap).trans
    (PlayerSpecificExtendedGCDHeights.fixed_degree_linear H)),h.2⟩

def run (p : Data) : List Data×Trace :=
  let first := PlayerSpecificDenseExecution.trim p
  let differentiated := PlayerSpecificDenseExecution.derivative first.1
  let second := PlayerSpecificDenseExecution.trim differentiated.1
  let pre := first.2++differentiated.2++second.2
  if first.1=[] then ([],pre++copyRows []++[.control 0]) else
    let rest := chain second.1.length first.1 second.1
    let result := first.1::rest.1
    (result,pre++rest.2++copyRows result++[.control second.1.length])

theorem value (p : Data) : (run p).1=PlayerSpecificSturmSequence.run p := by
  rw [run,PlayerSpecificSturmSequence.run]
  simp only [PlayerSpecificDenseExecution.trim_value,PlayerSpecificDenseExecution.derivative_value]
  split
  · rfl
  · simp only [chain_value]

theorem bounds (p : Data) (H : ℕ) (hp : HasHeight p H) (hlen : p.length≤4) :
    ∀ row∈(run p).1,HasHeight row (PlayerSpecificSquarefreeHeights.gcdHeight H) ∧ row.length≤4 := by
  rw [value]
  exact PlayerSpecificSturmHeights.run_bounds p H hp hlen

end Blotto.PlayerSpecificSturmExecution
