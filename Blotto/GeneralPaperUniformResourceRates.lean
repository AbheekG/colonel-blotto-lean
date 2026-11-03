import Blotto.GeneralPaperNativeResourceWordContract

/-! Sharp uniform resource closure on arbitrary input domains. Fast
rational prices preserve operand rates and hide only proved logarithms. -/
namespace Blotto.GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

@[fun_prop]
theorem polylog_mul {α : Type*} (f g L : α → ℕ) (hf : Polylog f L) (hg : Polylog g L) :
    Polylog (fun x => f x*g x) L := by
  change Bound _ (fun _ => 1) L
  simpa only [Nat.one_mul] using bound_mul hf hg

@[fun_prop]
theorem polylog_power {α : Type*} (f L : α → ℕ) (n : ℕ) (hf : Polylog f L) :
    Polylog (fun x => (f x)^n) L := by
  induction n with
  | zero => simpa only [pow_zero] using polylog_constant 1 L
  | succ n ih => simpa only [pow_succ] using polylog_mul _ _ L ih hf

@[fun_prop]
theorem polylog_bits {α : Type*} (f L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Small f L) :
    Polylog (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) L := by
  unfold GeneralPaperEncodedScalarStorage.natBits
  fun_prop

theorem polylog_small {α : Type*} {f L : α → ℕ} (hL : ∀ x,1≤L x) (hf : Polylog f L) : Small f L :=
  bound_small hL hf (small_constant 1 L hL)

theorem at_positive_rate {α : Type*} {f r L : α → ℕ} (hf : Polylog f L) (hr : ∀ x,1≤r x) : Bound f r L :=
  rate_mono hf hr

@[fun_prop]
theorem bound_polylog {α : Type*} (f r L : α → ℕ) (hr : ∀ x,1≤r x) (hf : Polylog f L) : Bound f r L :=
  at_positive_rate hf hr

@[fun_prop]
theorem bound_constant {α : Type*} (c : ℕ) (r L : α → ℕ) (hr : ∀ x,1≤r x) : Bound (fun _ => c) r L :=
  at_positive_rate (polylog_constant c L) hr

@[fun_prop]
theorem bound_word {α : Type*} (f r L : α → ℕ) (hr : ∀ x,1≤r x) (hf : Small f L) :
    Bound (fun x => binaryWordWidth (f x)) r L := at_positive_rate (polylog_word f L hf) hr

@[fun_prop]
theorem bound_bits {α : Type*} (f r L : α → ℕ) (hr : ∀ x,1≤r x) (hL : ∀ x,1≤L x) (hf : Small f L) :
    Bound (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) r L := at_positive_rate (polylog_bits f L hL hf) hr

@[fun_prop]
theorem polylog_factor {α : Type*} (d : ℕ) (f L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Small f L) :
    Polylog (fun x => GeneralPaperFastRationalModel.logFactor d (f x)) L := by
  unfold GeneralPaperFastRationalModel.logFactor
  fun_prop

theorem charge_bound {α : Type*} (C d : ℕ) {f r L : α → ℕ} (hL : ∀ x,1≤L x)
    (hf : Bound f r L) (hw : Small f L) : Bound (fun x => GeneralPaperFastRationalModel.charge C d (f x)) r L :=
  bound_mul_polylog _ _ _ L (polylog_mul_bound _ _ _ L (polylog_constant C L) hf) (polylog_factor d f L hL hw)

@[fun_prop]
theorem primitive_bound {α : Type*} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (f r L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Bound f r L) (hw : Small f L) :
    Bound (fun x => model.rat (f x)) r L := dominated (charge_bound C d hL hf hw) (fun x => hg (f x))

@[fun_prop]
theorem primitive_polylog {α : Type*} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (f L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Polylog f L) : Polylog (fun x => model.rat (f x)) L :=
  primitive_bound hg f _ L hL hf (polylog_small hL hf)

theorem rate_comparison {α : Type*} {f r s L : α → ℕ} (hf : Bound f r L) (C : ℕ) (h : ∀ x,r x≤C*s x) : Bound f s L := by
  obtain ⟨A,e,hA⟩ := hf
  refine ⟨A*C,e,?_⟩
  intro x
  exact (hA x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (h x))).trans_eq (by ring))

theorem pullback_bound_with_log {α : Type*} {f r : GeneralPaperSourceWordGrowth.Input → ℕ}
    (hf : GeneralPaperSourceSoftBounds.Soft r f) (source : α → GeneralPaperSourceWordGrowth.Input) (L : α → ℕ)
    (hLog : Tight (fun x => GeneralPaperSourceWordGrowth.logSize (source x)) L) :
    Bound (fun x => f (source x)) (fun x => r (source x)) L := by
  obtain ⟨C,hC⟩ := hLog
  exact pullback_source_bound_with_log hf source L C hC

@[fun_prop]
theorem array_profile_bound {α : Type*} (W n V r L : α → ℕ) (hr : ∀ x,1≤r x) (hL : ∀ x,1≤L x)
    (hW : Polylog W L) (hn : Bound n r L) (hV : Polylog V L) :
    Bound (fun x => GeneralPaperEncodedBasisStorage.arrayProfile (W x) (n x) (V x)) r L := by
  unfold GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

@[fun_prop]
theorem fill_profile_bound {α : Type*} (W P n C Q r L : α → ℕ) (hr : ∀ x,1≤r x) (hL : ∀ x,1≤L x)
    (hW : Polylog W L) (hP : Polylog P L) (hn : Bound n r L) (hns : Small n L)
    (hC : Polylog C L) (hQ : Bound Q r L) :
    Bound (fun x => GeneralPaperNativePayloadFillStorage.profile (W x) (P x) (n x) (C x) (Q x)) r L := by
  have hWs := polylog_small hL hW
  have hCs := polylog_small hL hC
  unfold GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap
  fun_prop (config := {maxSteps := 8000})

end Blotto.GeneralPaperUniformResourceGrowth
