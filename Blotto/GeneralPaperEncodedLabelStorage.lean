import Blotto.GeneralPaperActualProfitTreeStorage

/-! Typed selector labels have their intrinsic finite-index word bound.
List/array/row observers count payloads, references and descriptors. All
reserved array slots are included, even at a partially filled prefix. -/
namespace Blotto.GeneralPaperEncodedLabelStorage
open GeneralPaperEncodedFixedVector
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def listFootprint {K : ℕ} (W : ℕ) (xs : List (Fin K)) : ℕ :=
  GeneralPaperEncodedScalarStorage.listFootprint W rankBits xs

theorem list_bound {K : ℕ} (W N : ℕ) (xs : List (Fin K)) (hn : xs.length≤N) :
    listFootprint W xs≤N*(rankWord K+2*W)+32*W :=
  (GeneralPaperEncodedScalarStorage.list_bound W (rankWord K) rankBits xs (fun x _ => rank_bound x)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)

theorem list_power {K : ℕ} (W h : ℕ) (xs : List (Fin K)) (hn : xs.length≤2^h) :
    listFootprint W xs≤2^h*(rankWord K+34*W) := by
  have hb := list_bound W (2^h) xs hn
  have hp := Nat.mul_le_mul_right (32*W) (Nat.one_le_two_pow (n:=h))
  nlinarith only [hb,hp]

def arrayFootprint {K : ℕ} (W capacity : ℕ) (xs : Array (Fin K)) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W capacity rankBits xs

theorem array_bound {K : ℕ} (W capacity : ℕ) (xs : Array (Fin K)) (hn : xs.size≤capacity) :
    arrayFootprint W capacity xs≤capacity*(rankWord K+W)+64*W :=
  GeneralPaperEncodedReferenceVector.reserved_bound W (rankWord K) capacity rankBits xs hn (fun i => rank_bound xs[i.val])

def rowFootprint {m K : ℕ} (W : ℕ) (row : FixedArrayTable m (Fin K)) : ℕ := footprint W rankBits row

theorem row_bound {m K : ℕ} (W : ℕ) (row : FixedArrayTable m (Fin K)) :
    rowFootprint W row≤m*(rankWord K+W)+32*W := rank_array W row

def appendWindow {K : ℕ} (W : ℕ) (xs ys : List (Fin K)) : ℕ :=
  listFootprint W xs+listFootprint W ys+2*listFootprint W (xs++ys)+xs.length*(32*W+rankWord K)

def bufferCoefficient (W K : ℕ) : ℕ := 8*rankWord K+512*W+64

theorem append_window {K : ℕ} (W h : ℕ) (xs ys : List (Fin K))
    (hx : xs.length≤2^h) (hy : ys.length≤2^h) :
    appendWindow W xs ys≤2^(h+1)*bufferCoefficient W K := by
  have hl := list_power W h xs hx
  have hr := list_power W h ys hy
  have ha := list_power W (h+1) (xs++ys) (by rw [List.length_append,pow_succ]; omega)
  have hs := Nat.mul_le_mul_right (32*W+rankWord K) hx
  unfold appendWindow bufferCoefficient
  rw [pow_succ] at ha ⊢
  nlinarith only [hl,hr,ha,hs,Nat.zero_le (2^h*W),Nat.zero_le (2^h*rankWord K),Nat.two_pow_pos h]

theorem indexed_reserved_prefix {n K : ℕ} (index : ℕ → ℕ) (A W count : ℕ)
    (callback : Fin n → Fin K × ℕ) (hc : count≤n) :
    arrayFootprint W n (PaperIndexedArrayConstruction.fill index A callback count hc).1≤
      n*(rankWord K+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix index A W (rankWord K) rankBits callback
    (fun i => rank_bound (callback i).1) count hc

end Blotto.GeneralPaperEncodedLabelStorage
