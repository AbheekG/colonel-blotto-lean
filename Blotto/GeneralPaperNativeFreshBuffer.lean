import Blotto.GeneralPaperFairRowShiftLaw

/-! Consume each entry of one fresh fair-bit vector once, in forward
order, and write a stored buffer. The native read counter increments at
the unique fresh-bit call in each iteration. No retries or rejections. -/
namespace Blotto.GeneralPaperNativeFreshBuffer
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure State where
  data : Array Bool
  reads : ℕ
  work : ℕ

def fill {B : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (fresh : Fin B → Bool) : (k : ℕ) → k≤B → State
  | 0,_ => ⟨#[],0,32*A⟩
  | k+1,hk =>
    let previous := fill primitive A fresh k (by omega)
    let bit := fresh ⟨k,by omega⟩
    ⟨previous.data.push bit,previous.reads+1,previous.work+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) previous.reads 1+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) k 1+
      primitive (1+binaryWordWidth (k+1))+64*A+1⟩

theorem data {B : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (fresh : Fin B → Bool) (k : ℕ) (hk : k≤B) :
    (fill primitive A fresh k hk).data=Array.ofFn (fun j : Fin k => fresh ⟨j.val,by omega⟩) := by
  induction k with
  | zero => simp only [fill,Array.ofFn_zero]
  | succ k ih =>
    simp only [fill,ih (by omega),Array.ofFn_succ]
    rfl

theorem reads {B : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (fresh : Fin B → Bool) (k : ℕ) (hk : k≤B) :
    (fill primitive A fresh k hk).reads=k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun x => x+1) (ih (by omega))

def run {B : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (fresh : Fin B → Bool) :
    (FixedArrayTable B Bool×ℕ)×ℕ :=
  let filled := fill primitive A fresh B le_rfl
  ((⟨filled.data,by rw [data,Array.size_ofFn]⟩,filled.reads),filled.work+32*A)

theorem run_data {B : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (fresh : Fin B → Bool) :
    (run primitive A fresh).1.1=FixedArrayTable.ofFn fresh := by
  unfold run FixedArrayTable.ofFn
  dsimp only
  congr 1
  exact data primitive A fresh B le_rfl

theorem run_reads {B : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (fresh : Fin B → Bool) :
    (run primitive A fresh).1.2=B := reads primitive A fresh B le_rfl

theorem arithmetic_fill_work {B : ℕ} (A : ℕ) (fresh : Fin B → Bool) (k : ℕ) (hk : k≤B) :
    (fill (fun _ => 1) A fresh k hk).work≤k*(6+64*A)+32*A := by
  induction k with
  | zero => simp only [fill,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ k ih =>
    have hh := ih (by omega)
    simp only [fill,GeneralPaperNaturalPrimitivePrice.binary]
    nlinarith only [hh]

theorem arithmetic_work {B : ℕ} (A : ℕ) (fresh : Fin B → Bool) :
    (run (fun _ => 1) A fresh).2≤B*(6+64*A)+64*A := by
  have hh := arithmetic_fill_work A fresh B le_rfl
  change (fill (fun _ => 1) A fresh B le_rfl).work+32*A≤_
  omega

end Blotto.GeneralPaperNativeFreshBuffer
