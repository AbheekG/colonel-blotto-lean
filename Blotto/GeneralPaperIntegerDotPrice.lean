import Blotto.GeneralPaperIntegerPrimitivePrice

/-! Actual integer dot-product loop with operand-sensitive product and
accumulator/result-write prices. Every prefix is bounded before cancellation.
Literal index-list generation, reads and loop control are charged as well.
-/
namespace Blotto.GeneralPaperIntegerDotPrice
open GeneralPaperIntegerPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 6000000

def loop {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (f g : i → ℤ) : List i → ℤ → ℕ → GeneralPaperBasisIntegerDot.Result
  | [],a,spent => ⟨a,spent+2*W⟩
  | j::rest,a,spent =>
    let product := f j*g j
    loop primitive W f g rest (a+product)
      (spent+48*W+binary primitive (fun x y => x*y) (f j) (g j)+binary primitive (fun x y => x+y) a product)

theorem loop_data {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (f g : i → ℤ) (xs : List i) (a : ℤ) (spent oldSpent : ℕ) :
    (loop primitive W f g xs a spent).value=(GeneralPaperBasisIntegerDot.loop f g xs a oldSpent).value := by
  induction xs generalizing a spent oldSpent with
  | nil => rfl
  | cons j rest ih => exact ih _ _ _

theorem loop_work {i : Type*} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W X Y M : ℕ)
    (hX : X≤M) (hY : Y≤M) (f g : i → ℤ) (xs : List i)
    (hf : ∀ j∈xs,(f j).natAbs≤X) (hg : ∀ j∈xs,(g j).natAbs≤Y) (a : ℤ) (spent : ℕ)
    (hMass : a.natAbs+xs.length*X*Y≤M) :
    (loop primitive W f g xs a spent).work≤spent+xs.length*(48*W+4*primitive (1+binaryWordWidth M))+2*W := by
  induction xs generalizing a spent with
  | nil => simp only [loop,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons j rest ih =>
    have hProduct : (f j*g j).natAbs≤X*Y := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hf j List.mem_cons_self) (hg j List.mem_cons_self)
    have hSum : (a+f j*g j).natAbs≤a.natAbs+X*Y :=
      (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left hProduct _)
    rw [List.length_cons] at hMass
    have hSplit : a.natAbs+rest.length*X*Y+X*Y≤M := by nlinarith only [hMass]
    have hA : a.natAbs≤M := by omega
    have hXY : X*Y≤M := by omega
    have hTotal : a.natAbs+X*Y≤M := by omega
    have hMul := binary_le primitive hMono (fun x y => x*y) (f j) (g j) M
      ((hf j List.mem_cons_self).trans hX) ((hg j List.mem_cons_self).trans hY) (hProduct.trans hXY)
    have hAdd := binary_le primitive hMono (fun x y => x+y) a (f j*g j) M hA (hProduct.trans hXY) (hSum.trans hTotal)
    have hr := ih (fun k hk => hf k (List.mem_cons_of_mem j hk)) (fun k hk => hg k (List.mem_cons_of_mem j hk))
      (a+f j*g j) (spent+48*W+binary primitive (fun x y => x*y) (f j) (g j)+binary primitive (fun x y => x+y) a (f j*g j))
      (by nlinarith only [hSum,hMass])
    change (loop primitive W f g rest (a+f j*g j)
      (spent+48*W+binary primitive (fun x y => x*y) (f j) (g j)+binary primitive (fun x y => x+y) a (f j*g j))).work≤_
    rw [List.length_cons]
    nlinarith only [hr,hMul,hAdd]

def run {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (f g : Fin n → ℤ) : GeneralPaperBasisIntegerDot.Result :=
  let result := loop primitive W f g (List.finRange n) 0 0
  ⟨result.value,result.work+16*(n+1)*W⟩

theorem data {n : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (f g : Fin n → ℤ) :
    (run primitive W f g).value=(GeneralPaperBasisIntegerDot.run f g).value := loop_data primitive W f g _ 0 0 0

def cap (n X Y : ℕ) : ℕ := (n+1)*(X+1)*(Y+1)

theorem cap_bounds (n X Y : ℕ) : X≤cap n X Y ∧ Y≤cap n X Y ∧ n*X*Y≤cap n X Y := by
  refine ⟨?_,?_,Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ X)) (Nat.le_succ Y)⟩
  · have hh := Nat.mul_le_mul (Nat.mul_le_mul (show 1≤n+1 by omega) (Nat.le_succ X)) (show 1≤Y+1 by omega)
    simpa only [cap,Nat.one_mul,Nat.mul_one] using hh
  · have hh := Nat.mul_le_mul (Nat.mul_le_mul (show 1≤n+1 by omega) (show 1≤X+1 by omega)) (Nat.le_succ Y)
    simpa only [cap,Nat.one_mul] using hh

theorem cap_width (n X Y : ℕ) : binaryWordWidth (cap n X Y)≤
    binaryWordWidth (n+1)+binaryWordWidth (X+1)+binaryWordWidth (Y+1) := by
  exact (binaryWordWidth_mul ((n+1)*(X+1)) (Y+1)).trans
    (Nat.add_le_add_right (binaryWordWidth_mul (n+1) (X+1)) _)

theorem work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W X Y : ℕ)
    (f g : Fin n → ℤ) (hf : ∀ j,(f j).natAbs≤X) (hg : ∀ j,(g j).natAbs≤Y) :
    (run primitive W f g).work≤128*(n+1)*(W+primitive (1+binaryWordWidth (cap n X Y))) := by
  have hc := cap_bounds n X Y
  have hh := loop_work primitive hMono W X Y (cap n X Y) hc.1 hc.2.1 f g (List.finRange n)
    (fun j _ => hf j) (fun j _ => hg j) 0 0 (by simpa only [Int.natAbs_zero,Nat.zero_add,List.length_finRange] using hc.2.2)
  simp only [List.length_finRange,Nat.zero_add] at hh
  change _+16*(n+1)*W≤_
  nlinarith only [hh,Nat.zero_le (n*W),Nat.zero_le (n*primitive (1+binaryWordWidth (cap n X Y)))]

end Blotto.GeneralPaperIntegerDotPrice
