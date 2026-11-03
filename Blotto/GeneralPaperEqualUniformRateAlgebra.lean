import Blotto.GeneralPaperEqualCommonReference

/-! Quasilinear fast arithmetic on the actual input domain. Operand length
appears once; its checked word bound contributes only logarithmic factors.
All constants in these bounds are uniform over the complete domain. -/
namespace Blotto.GeneralPaperEqualUniformRateAlgebra
open GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

@[fun_prop]
theorem polylog_mul {α : Type*} (f g L : α → ℕ) (hf : Polylog f L) (hg : Polylog g L) :
    Polylog (fun x => f x * g x) L := by
  change Bound _ (fun _ => 1) _
  simpa only [Nat.one_mul] using bound_mul hf hg

@[fun_prop]
theorem polylog_power {α : Type*} (f L : α → ℕ) (n : ℕ) (hf : Polylog f L) :
    Polylog (fun x => (f x) ^ n) L := by
  induction n with
  | zero => simpa only [pow_zero] using polylog_constant 1 L
  | succ n ih => simpa only [pow_succ] using polylog_mul _ _ L ih hf

@[fun_prop]
theorem polylog_sub {α : Type*} (f g L : α → ℕ) (hf : Polylog f L) :
    Polylog (fun x => f x - g x) L := dominated hf (fun _ => Nat.sub_le _ _)

@[fun_prop]
theorem polylog_max {α : Type*} (f g L : α → ℕ) (hL : ∀ x, 1 ≤ L x) (hf : Polylog f L) (hg : Polylog g L) :
    Polylog (fun x => max (f x) (g x)) L := dominated (polylog_add f g L hL hf hg) (fun _ => by omega)

@[fun_prop]
theorem polylog_bits {α : Type*} (f L : α → ℕ) (hL : ∀ x, 1 ≤ L x) (hf : Small f L) :
    Polylog (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) L :=
  polylog_of_tight (tight_bits f L hL hf)

@[fun_prop]
theorem bound_constant {α : Type*} (c : ℕ) (r L : α → ℕ) (hr : ∀ x, 1 ≤ r x) :
    Bound (fun _ => c) r L := rate_mono (polylog_constant c L) hr

@[fun_prop]
theorem bound_word {α : Type*} (f r L : α → ℕ) (hr : ∀ x, 1 ≤ r x) (hf : Small f L) :
    Bound (fun x => binaryWordWidth (f x)) r L := rate_mono (polylog_word f L hf) hr

@[fun_prop]
theorem bound_bits {α : Type*} (f r L : α → ℕ) (hL : ∀ x, 1 ≤ L x) (hr : ∀ x, 1 ≤ r x) (hf : Small f L) :
    Bound (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) r L := rate_mono (polylog_bits f L hL hf) hr

@[fun_prop]
theorem bound_sub {α : Type*} (f g r L : α → ℕ) (hf : Bound f r L) :
    Bound (fun x => f x - g x) r L := dominated hf (fun _ => Nat.sub_le _ _)

@[fun_prop]
theorem bound_max {α : Type*} (f g r L : α → ℕ) (hL : ∀ x, 1 ≤ L x) (hf : Bound f r L) (hg : Bound g r L) :
    Bound (fun x => max (f x) (g x)) r L := dominated (bound_add f g r L hL hf hg) (fun _ => by omega)

@[fun_prop]
theorem rational_bound {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (f r L : α → ℕ) (hL : ∀ x, 1 ≤ L x) (hf : Bound f r L) (hw : Small f L) :
    Bound (fun x => model.rat (f x)) r L := by
  obtain ⟨C, d, hg⟩ := hFast
  have hFactor : Polylog (fun x => GeneralPaperFastRationalModel.logFactor d (f x)) L := by
    unfold GeneralPaperFastRationalModel.logFactor
    fun_prop
  have hPrice := bound_mul_polylog _ _ r L
    (polylog_mul_bound (fun _ => C) f r L (polylog_constant C L) hf) hFactor
  exact dominated hPrice (fun x => hg (f x))

@[fun_prop]
theorem rational_polylog {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (f L : α → ℕ) (hL : ∀ x, 1 ≤ L x) (hf : Polylog f L) (hw : Small f L) :
    Polylog (fun x => model.rat (f x)) L := rational_bound model hFast f (fun _ => 1) L hL hf hw

@[fun_prop]
theorem overhead_bound {α : Type*} (n A r L : α → ℕ) (hL : ∀ x, 1 ≤ L x)
    (hn : Bound n r L) (hs : Small n L) (hA : Polylog A L) (hr : ∀ x, 1 ≤ r x) :
    Bound (fun x => PaperIndexedArrayConstruction.overhead id (A x) (n x) (n x)) r L := by
  have hMajor : Bound (fun x => (n x + 1) * (6 * A x + 10 * binaryWordWidth (n x + 1) + 28)) r L := by fun_prop
  apply dominated hMajor
  intro x
  simpa only [Nat.mul_one] using PaperIndexedArrayConstruction.overhead_bound id 1
    (fun w => by change w ≤ 1 * w; omega) (A x) (n x) (n x) le_rfl

theorem small_of_polylog {α : Type*} {f L : α → ℕ} (hL : ∀ x, 1 ≤ L x) (hf : Polylog f L) : Small f L :=
  bound_small hL hf (small_constant 1 L hL)

end Blotto.GeneralPaperEqualUniformRateAlgebra
