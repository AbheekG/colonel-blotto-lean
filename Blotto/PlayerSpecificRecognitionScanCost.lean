import Blotto.PlayerSpecificRecognitionScanCopyCost

/-! Complete source price of every recognition scan path, from the actual
per-cell execution and full caller-frame copies. Both early acceptance and
rejection of all cells are covered. -/
namespace Blotto.PlayerSpecificRecognitionScanCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalTrace
open PlayerSpecificRecognitionScanExecution PlayerSpecificRecognitionScanBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem run_cost (model : RationalCostModel) (b : ℚ) (cells : List Cell) (N H : ℕ)
    (hb : RationalHeight b H) (hlen : cells.length≤N) (hc : ∀ c∈cells,CellHeight c H)
    (htest : ∀ c∈cells,(PlayerSpecificFiniteCellExecution.run model c b).2≤cellWork H*model.rat (width N H)) :
    (run model b cells).2≤unitWork N H*(cells.length+1)*model.rat (width N H) := by
  induction cells with
  | nil =>
    have hf:=PlayerSpecificRecognitionScanCopyCost.frame_cost model b [] N H hb hlen hc htest none (by simp)
    have hp:=frame_profile (cellWork H) (500*(N+1)) (model.rat (width N H)) _ hf
    simp only [run,List.length_nil,Nat.zero_add,Nat.mul_one]
    exact (Nat.le_add_left _ _).trans hp
  | cons c cs ih =>
    have ht:=htest c List.mem_cons_self
    have hi:=ih (by simp only [List.length_cons] at hlen; omega)
      (fun d hd => hc d (List.mem_cons_of_mem c hd))
      (fun d hd => htest d (List.mem_cons_of_mem c hd))
    cases he : (PlayerSpecificFiniteCellExecution.run model c b).1 with
    | some r =>
      have hf:=PlayerSpecificRecognitionScanCopyCost.frame_cost model b (c::cs) N H hb hlen hc htest (some (c,r)) (by
        intro d q hd
        have heq:=Option.some.inj hd
        have hcd : c=d := congrArg Prod.fst heq
        have hrq : r=q := congrArg Prod.snd heq
        subst d
        subst q
        exact ⟨List.mem_cons_self,he⟩)
      have hsum : (PlayerSpecificFiniteCellExecution.run model c b).2+
          price model (frame b (c::cs) (some (c,r)))≤unitWork N H*model.rat (width N H) :=
        (Nat.add_le_add_right ht _).trans (frame_profile _ _ _ _ hf)
      simp only [run,he]
      exact hsum.trans (by
        have hm:=Nat.mul_le_mul_right (unitWork N H*model.rat (width N H))
          (show 1≤(c::cs).length+1 by simp)
        simpa only [Nat.mul_one,Nat.one_mul,mul_assoc,mul_comm,mul_left_comm] using hm)
    | none =>
      have hf:=PlayerSpecificRecognitionScanCopyCost.frame_cost model b (c::cs) N H hb hlen hc htest (run model b cs).1 (by
        intro d r hr
        have hret:=returned model b cs d r hr
        exact ⟨List.mem_cons_of_mem c hret.1,hret.2⟩)
      have hsum : (PlayerSpecificFiniteCellExecution.run model c b).2+
          price model (frame b (c::cs) (run model b cs).1)≤unitWork N H*model.rat (width N H) :=
        (Nat.add_le_add_right ht _).trans (frame_profile _ _ _ _ hf)
      simp only [run,he]
      calc
        _ = ((PlayerSpecificFiniteCellExecution.run model c b).2+
            price model (frame b (c::cs) (run model b cs).1))+(run model b cs).2 := by omega
        _ ≤ unitWork N H*model.rat (width N H)+unitWork N H*(cs.length+1)*model.rat (width N H) := Nat.add_le_add hsum hi
        _ = _ := by simp only [List.length_cons]; ring

theorem source_cost (model : RationalCostModel) (b : ℚ) (cells : List Cell) (N H : ℕ)
    (hb : RationalHeight b H) (hH : 1≤H) (hlen : cells.length≤N) (hc : ∀ c∈cells,CellHeight c H)
    (hp : ∀ c∈cells,semantics (cubic c.state.coefficients b)≠0) :
    (run model b cells).2≤unitWork N H*(cells.length+1)*model.rat (width N H) := by
  apply run_cost model b cells N H hb hlen hc
  intro c hmem
  have ht:=PlayerSpecificFiniteCellCost.source_cost model c b H (hc c hmem) hb hH (hp c hmem)
  exact ht.trans (Nat.mul_le_mul_left _ (model.monotone (widths N H).1))

end Blotto.PlayerSpecificRecognitionScanCost
