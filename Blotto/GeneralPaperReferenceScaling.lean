import Blotto.GeneralPaperSourceScopeCoverage
import Mathlib.Tactic.FunProp

/-! Positive reference-width scaling of closed resource profiles. Constants,
reference copies, encoded metadata words, maxima and finite sums preserve
the property. The bounds are analysis of existing profiles and never execute
a memory census or add a parameter-preparation pass. -/
namespace Blotto.GeneralPaperReferenceScaling
open GeneralPaperEncodedScalarStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem word_add (a b : ℕ) : binaryWordWidth (a+b)≤binaryWordWidth a+binaryWordWidth b := by
  have ha := lt_pow_binaryWordWidth a
  have hb := lt_pow_binaryWordWidth b
  have hA : 2≤2^binaryWordWidth a := by
    have h := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 1≤binaryWordWidth a from binaryWordWidth_pos a)
    simpa only [pow_one] using h
  have hB : 2≤2^binaryWordWidth b := by
    have h := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 1≤binaryWordWidth b from binaryWordWidth_pos b)
    simpa only [pow_one] using h
  apply binaryWordWidth_le_of_lt_pow (by have := binaryWordWidth_pos a; omega)
  rw [pow_add]
  nlinarith only [ha,hb,hA,hB]

theorem word_scaled (t x : ℕ) (ht : 1≤t) : binaryWordWidth (t*x)≤t*binaryWordWidth x := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases hz : t=0
    · subst t
      simp only [Nat.zero_add,Nat.one_mul,le_refl]
    · have hp := ih (by omega)
      have hs := word_add (t*x) x
      simp only [Nat.add_mul,Nat.one_mul]
      omega

@[fun_prop]
def Scale (f : ℕ → ℕ) : Prop := Monotone f ∧ ∀ t w,1≤t → f (t*w)≤t*f w

@[fun_prop]
theorem identity : Scale (fun w : ℕ => w) := ⟨fun _ _ h => h,fun _ _ _ => Nat.le_refl _⟩

@[fun_prop]
theorem constant (c : ℕ) : Scale (fun _ : ℕ => c) :=
  ⟨fun _ _ _ => Nat.le_refl _,fun t _ ht => Nat.le_mul_of_pos_left c (by omega)⟩

@[fun_prop]
theorem successor : Scale Nat.succ := by
  refine ⟨fun _ _ h => Nat.succ_le_succ h,?_⟩
  intro t w ht
  simp only [Nat.succ_eq_add_one,Nat.mul_add,Nat.mul_one]
  omega

@[fun_prop]
theorem comp (f g : ℕ → ℕ) (hf : Scale f) (hg : Scale g) : Scale (fun w => f (g w)) :=
  ⟨hf.1.comp hg.1,fun t w ht => (hf.1 (hg.2 t w ht)).trans (hf.2 t (g w) ht)⟩

@[fun_prop]
theorem add (f g : ℕ → ℕ) (hf : Scale f) (hg : Scale g) : Scale (fun w => f w+g w) := by
  refine ⟨fun a b hab => Nat.add_le_add (hf.1 hab) (hg.1 hab),?_⟩
  intro t w ht
  simpa only [Nat.mul_add] using Nat.add_le_add (hf.2 t w ht) (hg.2 t w ht)

@[fun_prop]
theorem mul_left (c : ℕ) (f : ℕ → ℕ) (hf : Scale f) : Scale (fun w => c*f w) := by
  refine ⟨fun a b hab => Nat.mul_le_mul_left c (hf.1 hab),?_⟩
  intro t w ht
  exact (Nat.mul_le_mul_left c (hf.2 t w ht)).trans_eq (by ring)

@[fun_prop]
theorem mul_right (f : ℕ → ℕ) (c : ℕ) (hf : Scale f) : Scale (fun w => f w*c) := by
  refine ⟨fun a b hab => Nat.mul_le_mul_right c (hf.1 hab),?_⟩
  intro t w ht
  exact (Nat.mul_le_mul_right c (hf.2 t w ht)).trans_eq (by ring)

@[fun_prop]
theorem maximum (f g : ℕ → ℕ) (hf : Scale f) (hg : Scale g) : Scale (fun w => max (f w) (g w)) := by
  refine ⟨fun a b hab => max_le_max (hf.1 hab) (hg.1 hab),?_⟩
  intro t w ht
  exact (max_le_max (hf.2 t w ht) (hg.2 t w ht)).trans_eq (by rw [mul_max])

@[fun_prop]
theorem minimum (f g : ℕ → ℕ) (hf : Scale f) (hg : Scale g) : Scale (fun w => min (f w) (g w)) := by
  refine ⟨fun a b hab => min_le_min (hf.1 hab) (hg.1 hab),?_⟩
  intro t w ht
  exact (min_le_min (hf.2 t w ht) (hg.2 t w ht)).trans_eq (by rw [mul_min])

@[fun_prop]
theorem word : Scale binaryWordWidth := ⟨fun _ _ h => binaryWordWidth_mono h,word_scaled⟩

@[fun_prop]
theorem natural_bits : Scale natBits := by
  unfold natBits
  fun_prop

@[fun_prop]
theorem fields (xs : List ℕ) : Scale (fun W => GeneralPaperEncodedScalarStorage.fields W xs) := by
  unfold GeneralPaperEncodedScalarStorage.fields
  fun_prop

@[fun_prop]
theorem list_footprint {α : Type*} (encode : α → ℕ) (xs : List α) :
    Scale (fun W => GeneralPaperEncodedScalarStorage.listFootprint W encode xs) := by
  unfold GeneralPaperEncodedScalarStorage.listFootprint
  fun_prop

@[fun_prop]
theorem array_word (n : ℕ) : Scale (fun W => GeneralPaperSummaryArrayExecution.arrayWord W n) := by
  unfold GeneralPaperSummaryArrayExecution.arrayWord
  fun_prop

@[fun_prop]
theorem finset_sum {α : Type*} (s : Finset α) (f : α → ℕ → ℕ) (hf : ∀ i∈s,Scale (f i)) :
    Scale (fun w => ∑ i∈s,f i w) := by
  refine ⟨fun a b hab => Finset.sum_le_sum (fun i hi => (hf i hi).1 hab),?_⟩
  intro t w ht
  simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun i hi => (hf i hi).2 t w ht)

theorem at_one (f : ℕ → ℕ) (hf : Scale f) (W : ℕ) (hW : 1≤W) : f W≤W*f 1 := by
  simpa only [Nat.mul_one] using hf.2 W 1 hW

end Blotto.GeneralPaperReferenceScaling
