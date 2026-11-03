import Blotto.GeneralPaperCachedProfitGridPrice

/-! One prefix traversal returns take/drop together. The suffix is borrowed.
Every counter guard/decrement, list read and copied prefix cell is priced;
the data equality permits use in the native balanced-tree split. -/
namespace Blotto.GeneralPaperPricedListSplit
set_option autoImplicit false
set_option maxHeartbeats 5000000

def control (primitive : ℕ → ℕ) (W count : ℕ) : ℕ :=
  GeneralPaperIntegerWordPrice.compare primitive count 0+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) count 1+64*W

def run {α : Type*} (primitive : ℕ → ℕ) (W : ℕ) : ℕ → List α → (List α × List α) × ℕ
  | 0,xs => (([],xs),GeneralPaperIntegerWordPrice.compare primitive 0 0+32*W)
  | count+1,[] => (([],[]),control primitive W (count+1))
  | count+1,x::xs =>
    let rest := run primitive W count xs
    ((x::rest.1.1,rest.1.2),rest.2+control primitive W (count+1))

theorem data {α : Type*} (primitive : ℕ → ℕ) (W count : ℕ) (xs : List α) :
    (run primitive W count xs).1=(xs.take count,xs.drop count) := by
  induction count generalizing xs with
  | zero => simp only [run,List.take_zero,List.drop_zero]
  | succ count ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [run,ih,List.take_succ_cons,List.drop_succ_cons]

theorem control_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W cap count : ℕ) (hCount : count≤cap) :
    control primitive W count≤4*primitive (1+binaryWordWidth (cap+1))+64*W := by
  let L := 1+binaryWordWidth (cap+1)
  have hw (a : ℕ) (ha : a≤cap+1) : 1+binaryWordWidth a≤L :=
    Nat.add_le_add_left (binaryWordWidth_mono ha) 1
  have hc := GeneralPaperIntegerWordPrice.compare_le primitive hMono count 0 L (hw _ (by omega)) (hw _ (by omega))
  have hd := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a-b) count 1 L
    (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega))
  unfold control
  change _≤4*primitive L+64*W
  omega

theorem work {α : Type*} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W cap count : ℕ)
    (xs : List α) (hCount : count≤cap) :
    (run primitive W count xs).2≤(count+1)*(4*primitive (1+binaryWordWidth (cap+1))+64*W) := by
  let C := 4*primitive (1+binaryWordWidth (cap+1))+64*W
  induction count generalizing xs with
  | zero =>
    have hc := GeneralPaperIntegerWordPrice.compare_le primitive hMono 0 0 (1+binaryWordWidth (cap+1))
      (Nat.add_le_add_left (binaryWordWidth_mono (show 0≤cap+1 by omega)) 1)
      (Nat.add_le_add_left (binaryWordWidth_mono (show 0≤cap+1 by omega)) 1)
    change GeneralPaperIntegerWordPrice.compare primitive 0 0+32*W≤_
    omega
  | succ count ih =>
    have hc := control_work primitive hMono W cap (count+1) hCount
    cases xs with
    | nil =>
      change control primitive W (count+1)≤(count+1+1)*C
      change control primitive W (count+1)≤C at hc
      nlinarith only [hc,Nat.zero_le C]
    | cons x xs =>
      have hr := ih xs (by omega)
      change (run primitive W count xs).2+control primitive W (count+1)≤(count+1+1)*C
      change (run primitive W count xs).2≤(count+1)*C at hr
      change control primitive W (count+1)≤C at hc
      nlinarith only [hr,hc]

theorem arithmetic_work {α : Type*} (count : ℕ) (xs : List α) :
    (run (fun _ => 1) 1 count xs).2≤68*(count+1) := by
  have h := work (fun _ => 1) (fun _ _ _ => Nat.le_refl _) 1 count count xs (Nat.le_refl _)
  simpa only [Nat.mul_comm] using h

end Blotto.GeneralPaperPricedListSplit
