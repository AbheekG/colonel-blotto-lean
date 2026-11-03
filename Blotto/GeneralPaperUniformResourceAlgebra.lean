import Blotto.GeneralPaperNativeResourceDomain

/-! Uniform arithmetic closure and reference scaling on the actual input
domain. Constants are chosen once for the entire domain; no source-record
family matching or per-instance asymptotic constant is used. -/
namespace Blotto.GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

@[fun_prop]
theorem small_word {α : Type*} (f L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Small f L) : Small (fun x => binaryWordWidth (f x)) L :=
  small_of_tight (word_tight f L hf) hL

@[fun_prop]
theorem small_bits {α : Type*} (f L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Small f L) :
    Small (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) L := by
  unfold GeneralPaperEncodedScalarStorage.natBits
  fun_prop

@[fun_prop]
theorem small_power {α : Type*} (f L : α → ℕ) (n : ℕ) (hL : ∀ x,1≤L x) (hf : Small f L) : Small (fun x => (f x)^n) L := by
  obtain ⟨C,hC⟩ := hf
  refine ⟨1+n*C,?_⟩
  intro x
  have hw := GeneralPaperFastRationalBounds.word_power (f x) n
  have hc := Nat.mul_le_mul_left n (hC x)
  have hl := hL x
  nlinarith only [hw,hc,hl]

@[fun_prop]
theorem power_two_small {α : Type*} (f L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Tight f L) : Small (fun x => 2^(f x)) L := by
  obtain ⟨C,hC⟩ := hf
  refine ⟨C+1,?_⟩
  intro x
  have hc := hC x
  have hl := hL x
  simp only [binaryWordWidth,Nat.log2_two_pow]
  nlinarith only [hc,hl]

@[fun_prop]
theorem small_sub {α : Type*} (f g L : α → ℕ) (hf : Small f L) : Small (fun x => f x-g x) L :=
  small_mono hf (fun _ => Nat.sub_le _ _)

@[fun_prop]
theorem small_div {α : Type*} (f g L : α → ℕ) (hf : Small f L) : Small (fun x => f x/g x) L :=
  small_mono hf (fun _ => Nat.div_le_self _ _)

@[fun_prop]
theorem small_max {α : Type*} (f g L : α → ℕ) (hf : Small f L) (hg : Small g L) : Small (fun x => max (f x) (g x)) L :=
  small_mono (small_add f g L hf hg) (fun _ => by omega)

@[fun_prop]
theorem small_min {α : Type*} (f g L : α → ℕ) (hf : Small f L) : Small (fun x => min (f x) (g x)) L :=
  small_mono hf (fun _ => Nat.min_le_left _ _)

@[fun_prop]
theorem tight_bits {α : Type*} (f L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Small f L) :
    Tight (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) L := by
  unfold GeneralPaperEncodedScalarStorage.natBits
  fun_prop

theorem tight_identity {α : Type*} (L : α → ℕ) : Tight L L := ⟨1,fun _ => by omega⟩

theorem bound_small {α : Type*} {f r L : α → ℕ} (hL : ∀ x,1≤L x) (hf : Bound f r L) (hr : Small r L) : Small f L := by
  obtain ⟨A,e,hA⟩ := hf
  have hl : Small L L := small_of_tight (tight_identity L) hL
  apply small_mono (g:=fun x => A*r x*(L x)^e) (by fun_prop)
  exact hA

@[fun_prop]
theorem primitive_small {α : Type*} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (f L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Small f L) : Small (fun x => model.rat (f x)) L := by
  apply small_mono (g:=fun x => C*(f x+3)^(d+1)) (by fun_prop)
  intro x
  exact (hg (f x)).trans (GeneralPaperFastRationalBounds.charge_polynomial C d (f x))

theorem bound_identity {α : Type*} (r L : α → ℕ) : Bound r r L := pointwise r r L 1 (fun _ => by omega)

@[fun_prop]
theorem polylog_constant {α : Type*} (c : ℕ) (L : α → ℕ) : Polylog (fun _ => c) L := pointwise _ _ _ c (fun _ => by omega)

theorem polylog_of_tight {α : Type*} {f L : α → ℕ} (h : Tight f L) : Polylog f L := by
  obtain ⟨C,hC⟩ := h
  refine ⟨C,1,?_⟩
  simpa only [Nat.mul_one,pow_one] using hC

@[fun_prop]
theorem polylog_word {α : Type*} (f L : α → ℕ) (h : Small f L) : Polylog (fun x => binaryWordWidth (f x)) L :=
  polylog_of_tight (word_tight f L h)

theorem bound_mul {α : Type*} {f g r s L : α → ℕ} (hf : Bound f r L) (hg : Bound g s L) :
    Bound (fun x => f x*g x) (fun x => r x*s x) L := by
  obtain ⟨A,e,hA⟩ := hf
  obtain ⟨B,d,hB⟩ := hg
  refine ⟨A*B,e+d,?_⟩
  intro x
  exact (Nat.mul_le_mul (hA x) (hB x)).trans_eq (by rw [pow_add];ring)

@[fun_prop]
theorem bound_mul_polylog {α : Type*} (f g r L : α → ℕ) (hf : Bound f r L) (hg : Polylog g L) :
    Bound (fun x => f x*g x) r L := by
  simpa only [Nat.mul_one] using bound_mul hf hg

@[fun_prop]
theorem polylog_mul_bound {α : Type*} (f g r L : α → ℕ) (hf : Polylog f L) (hg : Bound g r L) :
    Bound (fun x => f x*g x) r L := by
  simpa only [Nat.one_mul] using bound_mul hf hg

@[fun_prop]
theorem bound_add {α : Type*} (f g r L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Bound f r L) (hg : Bound g r L) :
    Bound (fun x => f x+g x) r L := by
  obtain ⟨A,e,hA⟩ := hf
  obtain ⟨B,d,hB⟩ := hg
  refine ⟨A+B,e+d,?_⟩
  intro x
  have he := Nat.pow_le_pow_right (hL x) (show e≤e+d by omega)
  have hd := Nat.pow_le_pow_right (hL x) (show d≤e+d by omega)
  have h1 := (hA x).trans (Nat.mul_le_mul_left (A*r x) he)
  have h2 := (hB x).trans (Nat.mul_le_mul_left (B*r x) hd)
  nlinarith only [h1,h2]

@[fun_prop]
theorem polylog_add {α : Type*} (f g L : α → ℕ) (hL : ∀ x,1≤L x) (hf : Polylog f L) (hg : Polylog g L) :
    Polylog (fun x => f x+g x) L := bound_add f g _ L hL hf hg

theorem profile_at_word {α : Type*} (P : ℕ → α → ℕ) (W r L : α → ℕ)
    (hScale : ∀ x,GeneralPaperReferenceScaling.Scale (fun w => P w x))
    (hW : ∀ x,1≤W x) (hTight : Tight W L) (hOne : Bound (P 1) r L) : Bound (fun x => P (W x) x) r L := by
  have hProduct := polylog_mul_bound W (P 1) r L (polylog_of_tight hTight) hOne
  apply dominated hProduct
  intro x
  exact GeneralPaperReferenceScaling.at_one _ (hScale x) (W x) (hW x)

theorem small_change_log {α : Type*} {f L M : α → ℕ} (hf : Small f L) (hLM : Tight L M) : Small f M := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hLM
  refine ⟨C*D,?_⟩
  intro x
  exact (hC x).trans ((Nat.mul_le_mul_left C (hD x)).trans_eq (by ring))

theorem pullback_small_with_log {α : Type*} {f : GeneralPaperSourceWordGrowth.Input → ℕ}
    (hf : GeneralPaperSourceWordGrowth.Small f) (source : α → GeneralPaperSourceWordGrowth.Input) (L : α → ℕ)
    (hLog : Tight (fun x => GeneralPaperSourceWordGrowth.logSize (source x)) L) : Small (fun x => f (source x)) L :=
  small_change_log (pullback_source_small hf source) hLog

@[fun_prop]
theorem array_profile_small {α : Type*} (W n V L : α → ℕ) (hL : ∀ x,1≤L x)
    (hW : Small W L) (hn : Small n L) (hV : Small V L) :
    Small (fun x => GeneralPaperEncodedBasisStorage.arrayProfile (W x) (n x) (V x)) L := by
  unfold GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

@[fun_prop]
theorem fill_profile_small {α : Type*} (W P n C Q L : α → ℕ) (hL : ∀ x,1≤L x)
    (hW : Small W L) (hP : Small P L) (hn : Small n L) (hC : Small C L) (hQ : Small Q L) :
    Small (fun x => GeneralPaperNativePayloadFillStorage.profile (W x) (P x) (n x) (C x) (Q x)) L := by
  unfold GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap
  fun_prop (config := {maxSteps := 4000})

end Blotto.GeneralPaperUniformResourceGrowth
