import Blotto.GeneralPaperFullPreparationProfileGrowth

/-! Uniform resource growth over the actual problem domain, rather than all
unconstrained source records. Old unconditional source bounds pull back to
that domain with the same constants. No native/source-family matching premise
is introduced. All definitions and transports are erased mathematical analysis. -/
namespace Blotto.GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

@[fun_prop]
def Small {α : Type*} (f L : α → ℕ) : Prop := ∃ C : ℕ,∀ x,binaryWordWidth (f x)≤C*L x

@[fun_prop]
def Tight {α : Type*} (f L : α → ℕ) : Prop := ∃ C : ℕ,∀ x,f x≤C*L x

@[fun_prop]
def Bound {α : Type*} (f r L : α → ℕ) : Prop := ∃ A e : ℕ,∀ x,f x≤A*r x*(L x)^e

@[fun_prop]
def Polylog {α : Type*} (f L : α → ℕ) : Prop := Bound f (fun _ => 1) L

theorem small_mono {α : Type*} {f g L : α → ℕ} (hg : Small g L) (h : ∀ x,f x≤g x) : Small f L := by
  obtain ⟨C,hC⟩ := hg
  exact ⟨C,fun x => (binaryWordWidth_mono (h x)).trans (hC x)⟩

@[fun_prop]
theorem small_constant {α : Type*} (c : ℕ) (L : α → ℕ) (hL : ∀ x,1≤L x) : Small (fun _ => c) L := by
  refine ⟨binaryWordWidth c,?_⟩
  intro x
  have h := Nat.mul_le_mul_left (binaryWordWidth c) (hL x)
  simpa only [Nat.mul_one] using h

@[fun_prop]
theorem tight_constant {α : Type*} (c : ℕ) (L : α → ℕ) (hL : ∀ x,1≤L x) : Tight (fun _ => c) L := by
  refine ⟨c,?_⟩
  intro x
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left c (hL x)

@[fun_prop]
theorem small_add {α : Type*} (f g L : α → ℕ) (hf : Small f L) (hg : Small g L) : Small (fun x => f x+g x) L := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  refine ⟨C+D,?_⟩
  intro x
  have h := GeneralPaperReferenceScaling.word_add (f x) (g x)
  have h1 := hC x
  have h2 := hD x
  nlinarith only [h,h1,h2]

@[fun_prop]
theorem small_mul {α : Type*} (f g L : α → ℕ) (hf : Small f L) (hg : Small g L) : Small (fun x => f x*g x) L := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  refine ⟨C+D,?_⟩
  intro x
  have h := binaryWordWidth_mul (f x) (g x)
  have h1 := hC x
  have h2 := hD x
  nlinarith only [h,h1,h2]

@[fun_prop]
theorem tight_add {α : Type*} (f g L : α → ℕ) (hf : Tight f L) (hg : Tight g L) : Tight (fun x => f x+g x) L := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  refine ⟨C+D,?_⟩
  intro x
  have h1 := hC x
  have h2 := hD x
  nlinarith only [h1,h2]

@[fun_prop]
theorem tight_mul_constant {α : Type*} (c : ℕ) (f L : α → ℕ) (h : Tight f L) : Tight (fun x => c*f x) L := by
  obtain ⟨C,hC⟩ := h
  refine ⟨c*C,?_⟩
  intro x
  exact (Nat.mul_le_mul_left c (hC x)).trans_eq (by ring)

theorem small_of_tight {α : Type*} {f L : α → ℕ} (h : Tight f L) (hL : ∀ x,1≤L x) : Small f L := by
  obtain ⟨C,hC⟩ := h
  refine ⟨C+1,?_⟩
  intro x
  have hw := Nat.log2_le_self (f x)
  have hc := hC x
  have hl := hL x
  unfold binaryWordWidth
  nlinarith only [hw,hc,hl]

@[fun_prop]
theorem word_tight {α : Type*} (f L : α → ℕ) (h : Small f L) : Tight (fun x => binaryWordWidth (f x)) L := h

theorem dominated {α : Type*} {f g r L : α → ℕ} (hg : Bound g r L) (h : ∀ x,f x≤g x) : Bound f r L := by
  obtain ⟨A,e,hA⟩ := hg
  exact ⟨A,e,fun x => (h x).trans (hA x)⟩

theorem rate_mono {α : Type*} {f r s L : α → ℕ} (h : Bound f r L) (hrs : ∀ x,r x≤s x) : Bound f s L := by
  obtain ⟨A,e,hA⟩ := h
  exact ⟨A,e,fun x => (hA x).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (hrs x)))⟩

theorem pointwise {α : Type*} (f r L : α → ℕ) (A : ℕ) (h : ∀ x,f x≤A*r x) : Bound f r L := by
  refine ⟨A,0,?_⟩
  simpa only [pow_zero,Nat.mul_one] using h

theorem change_log {α : Type*} {f r L M : α → ℕ} (h : Bound f r L) (C : ℕ) (hLM : ∀ x,L x≤C*M x) : Bound f r M := by
  obtain ⟨A,e,hA⟩ := h
  refine ⟨A*C^e,e,?_⟩
  intro x
  exact (hA x).trans ((Nat.mul_le_mul_left (A*r x) (Nat.pow_le_pow_left (hLM x) e)).trans_eq (by rw [mul_pow];ring))

theorem pullback_source_bound {α : Type*} {r f : GeneralPaperSourceWordGrowth.Input → ℕ}
    (h : GeneralPaperSourceSoftBounds.Soft r f) (source : α → GeneralPaperSourceWordGrowth.Input) :
    Bound (fun x => f (source x)) (fun x => r (source x)) (fun x => GeneralPaperSourceWordGrowth.logSize (source x)) := by
  obtain ⟨A,e,hA⟩ := h
  exact ⟨A,e,fun x => hA (source x)⟩

theorem pullback_source_small {α : Type*} {f : GeneralPaperSourceWordGrowth.Input → ℕ}
    (h : GeneralPaperSourceWordGrowth.Small f) (source : α → GeneralPaperSourceWordGrowth.Input) :
    Small (fun x => f (source x)) (fun x => GeneralPaperSourceWordGrowth.logSize (source x)) := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C,fun x => hC (source x)⟩

theorem pullback_source_tight {α : Type*} {f : GeneralPaperSourceWordGrowth.Input → ℕ}
    (h : GeneralPaperSourceWordGrowth.Tight f) (source : α → GeneralPaperSourceWordGrowth.Input) :
    Tight (fun x => f (source x)) (fun x => GeneralPaperSourceWordGrowth.logSize (source x)) := by
  obtain ⟨C,hC⟩ := h
  exact ⟨C,fun x => hC (source x)⟩

theorem pullback_source_bound_with_log {α : Type*} {r f : GeneralPaperSourceWordGrowth.Input → ℕ}
    (h : GeneralPaperSourceSoftBounds.Soft r f) (source : α → GeneralPaperSourceWordGrowth.Input) (L : α → ℕ)
    (C : ℕ) (hL : ∀ x,GeneralPaperSourceWordGrowth.logSize (source x)≤C*L x) :
    Bound (fun x => f (source x)) (fun x => r (source x)) L := change_log (pullback_source_bound h source) C hL

end Blotto.GeneralPaperUniformResourceGrowth
