import Blotto.PlayerSpecificMeasuredInputRowCost

/-! Actual guard assembly uses measured original input and explicitly
priced natural additions/products. No coefficient-height or fuel oracle
is an executing argument. -/
namespace Blotto.PlayerSpecificMinimumGuardExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def assemble (model : RationalCostModel) (P N L : ℕ) : ℕ×ℕ :=
  let n:=N+1
  let l:=L+1
  let product:=P*n
  let bound:=product*l
  (bound,GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) N 1+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) L 1+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) P n+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) product l+
    price model ([P,N,L,n,l,product,bound].map Event.control))

def run {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) : ℕ×ℕ :=
  let measured:=PlayerSpecificInputWidthExecution.run model (PlayerSpecificRecognitionInputHeights.row i)
  let guard:=assemble model PlayerSpecificInitialPositivePrecision.coefficient N measured.1
  (guard.1,measured.2+guard.2)

theorem value {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (run model i).1=PlayerSpecificMinimumContract.fuel i := by
  simp only [run,assemble,PlayerSpecificInputWidthExecution.value,PlayerSpecificMinimumContract.fuel]

def width (P N L : ℕ) : ℕ := 128*(P+1)*(N+1)*(L+1)+128

theorem assemble_cost (model : RationalCostModel) (P N L : ℕ) :
    (assemble model P N L).2≤64*model.rat (width P N L) := by
  let G:=(P+1)*(N+1)*(L+1)
  have hN : N+1≤(N+1)*(L+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hL : L+1≤(N+1)*(L+1) := Nat.le_mul_of_pos_left _ (by omega)
  have hS : (N+1)*(L+1)≤G := by dsimp only [G]; nlinarith only [Nat.zero_le (P*((N+1)*(L+1)))]
  have hP : P≤G := by
    have hp:=Nat.mul_le_mul_left (P+1) (show 1≤(N+1)*(L+1) by omega)
    dsimp only [G]
    nlinarith only [hp]
  have hpart : P*(N+1)≤G := by
    have h:=Nat.mul_le_mul_right (N+1) (Nat.le_succ P)
    have h':=(Nat.le_mul_of_pos_right ((P+1)*(N+1)) (by omega : 0<L+1))
    exact h.trans h'
  have hbound : P*(N+1)*(L+1)≤G := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ P))
  have word (n : ℕ) (hn : n≤G) : 1+binaryWordWidth n≤width P N L := by
    have hc:=control_width n
    unfold width
    dsimp only [G] at hn
    nlinarith only [hc,hn]
  have ha:=GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) N 1 (width P N L)
    (word _ (by omega)) (word _ (by omega)) (word _ (by omega))
  have hb:=GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) L 1 (width P N L)
    (word _ (by omega)) (word _ (by omega)) (word _ (by omega))
  have hc:=GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) P (N+1) (width P N L)
    (word _ hP) (word _ (by omega)) (word _ hpart)
  have hd:=GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) (P*(N+1)) (L+1) (width P N L)
    (word _ hpart) (word _ (by omega)) (word _ hbound)
  have ctrl (n : ℕ) (hn : n≤G) : n+1≤width P N L := by
    unfold width
    dsimp only [G] at hn
    nlinarith only [hn]
  have hfit:=PlayerSpecificDenseTraceFits.controls_fits (width P N L) [P,N,L,N+1,L+1,P*(N+1),P*(N+1)*(L+1)] (by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact ctrl _ (by omega))
  have he:=price_bound model (width P N L) (by unfold width; omega) _ hfit
  simp only [List.length_map,List.length_cons,List.length_nil] at he
  simp only [assemble]
  omega

theorem source_cost {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (run model i).2≤4096*(2*N+2)*(PlayerSpecificRecognitionInputHeights.inputHeight i+1)*
      model.rat (PlayerSpecificInputWidthExecution.width (PlayerSpecificRecognitionInputHeights.inputHeight i))+
      64*model.rat (width PlayerSpecificInitialPositivePrecision.coefficient N (PlayerSpecificRecognitionInputHeights.inputHeight i)) := by
  have hm:=PlayerSpecificMeasuredInputRowCost.source_cost model (PlayerSpecificRecognitionInputHeights.row i)
  have hg:=assemble_cost model PlayerSpecificInitialPositivePrecision.coefficient N (PlayerSpecificRecognitionInputHeights.inputHeight i)
  have hv:=PlayerSpecificInputWidthExecution.value model (PlayerSpecificRecognitionInputHeights.row i)
  simp only [PlayerSpecificRecognitionInputHeights.row,List.length_cons,List.length_append,List.length_ofFn] at hm
  simp only [run,hv]
  dsimp only [PlayerSpecificRecognitionInputHeights.inputHeight] at hg ⊢
  dsimp only [PlayerSpecificRecognitionInputHeights.row] at hg ⊢
  nlinarith only [hm,hg]

end Blotto.PlayerSpecificMinimumGuardExecution
