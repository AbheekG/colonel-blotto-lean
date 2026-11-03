import Blotto.PlayerSpecificReconstructionDecode

/-! Exact acceptance of a reconstructed candidate. The actual polynomial
substitution, both half-open endpoint comparisons, zero test, branch and
complete input/output copies are traced together. -/
namespace Blotto.PlayerSpecificReconstructionFilter
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 500000

def run (p : Data) (node : Interval) (q : ℚ) : Option ℚ×Trace :=
  let evaluated:=PlayerSpecificDenseExecution.evaluate p q
  let lower:=PlayerSpecificRationalTrace.compare q node.lo
  let upper:=PlayerSpecificRationalTrace.compare q node.hi
  let zero:=equalZero evaluated.1
  let accepted:=(!lower.1 && upper.1 && zero.1)
  (if accepted then some q else none,
    copyRow p++[.copy node.lo,.copy node.hi,.copy q,.control 3]++evaluated.2++lower.2++upper.2++zero.2++
      (if accepted then [.copy q,.control 1] else [.control 0]))

theorem value (p : Data) (node : Interval) (q : ℚ) :
    (run p node q).1=if node.lo<q ∧ q≤node.hi ∧ evaluate p q=0 then some q else none := by
  by_cases hl : node.lo<q <;> by_cases hh : q≤node.hi <;> by_cases hz : evaluate p q=0 <;>
    simp_all [run,PlayerSpecificRationalTrace.compare,equalZero,PlayerSpecificDenseExecution.evaluate_value]

def width (T : ℕ) : ℕ := 64*(T+1)

theorem run_cost (model : RationalCostModel) (p : Data) (node : Interval) (q : ℚ) (T : ℕ)
    (hp : HasHeight p T) (hlen : p.length≤4) (hlo : RationalHeight node.lo T)
    (hhi : RationalHeight node.hi T) (hq : RationalHeight q T) :
    price model (run p node q).2≤1000*model.rat (width T) := by
  let W:=width T
  let evaluated:=PlayerSpecificDenseExecution.evaluate p q
  let lower:=PlayerSpecificRationalTrace.compare q node.lo
  let upper:=PlayerSpecificRationalTrace.compare q node.hi
  let zero:=equalZero evaluated.1
  have hW : 6≤W := by unfold W width; omega
  have word (a : ℚ) (ha : RationalHeight a T) : rationalWordWidth a≤W :=
    (rationalWordWidth_of_height ha).trans (by unfold W width; omega)
  have hrow:=PlayerSpecificMonicDivisionBudget.copy_cost model p T W hp hlen (by unfold W width; omega) hW
  have hpre : Fits W [.copy node.lo,.copy node.hi,.copy q,.control 3] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact word _ hlo
    · exact word _ hhi
    · exact word _ hq
    · exact (control_width 3).trans (by omega)
  have cpre:=price_bound model W (by omega) _ hpre
  simp only [List.length_cons,List.length_nil] at cpre
  have heval:=PlayerSpecificHornerTraceCost.evaluate_cost model p q T 4 hp hq hlen
  have heW : PlayerSpecificHornerTraceCost.width T 4≤W := by
    unfold PlayerSpecificHornerTraceCost.width PlayerSpecificHornerTraceCost.valueHeight W width
    omega
  have cev:=heval.trans (Nat.mul_le_mul_left (33*p.length+9) (model.monotone heW))
  have cev' : price model evaluated.2≤141*model.rat W :=
    cev.trans (Nat.mul_le_mul_right (model.rat W) (by omega))
  have cl:=price_bound model W (by omega) _ (compare_fits W q node.lo (word _ hq) (word _ hlo) (by omega))
  have ch:=price_bound model W (by omega) _ (compare_fits W q node.hi (word _ hq) (word _ hhi) (by omega))
  rw [compare_length] at cl ch
  have hval : RationalHeight evaluated.1 (8*T+5) := by
    rw [PlayerSpecificDenseExecution.evaluate_value]
    apply (evaluate_height hp hq).mono
    nlinarith
  have hwval : rationalWordWidth evaluated.1≤W := (rationalWordWidth_of_height hval).trans (by unfold W width; omega)
  have hzero : rationalWordWidth (0:ℚ)≤W := by
    have hz : rationalWordWidth (0:ℚ)=3 := by decide
    rw [hz]
    omega
  have cz:=price_bound model W (by omega) _ (equalZero_fits W evaluated.1 hwval hzero (by omega))
  rw [equalZero_length] at cz
  have someFits : Fits W [.copy q,.control 1] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact word _ hq
    · exact (control_width 1).trans (by omega)
  have cs:=price_bound model W (by omega) _ someFits
  simp only [List.length_cons,List.length_nil] at cs
  have cn:=PlayerSpecificMonicDivisionBudget.control_cost model 0 W (by omega) hW
  rw [run]
  dsimp only
  split <;> simp only [price_append]
  · nlinarith only [hrow,cpre,cev',cl,ch,cz,cs]
  · nlinarith only [hrow,cpre,cev',cl,ch,cz,cn]

end Blotto.PlayerSpecificReconstructionFilter
