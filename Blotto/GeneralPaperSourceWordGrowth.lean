import Blotto.GeneralPaperFastClassifiedSourceContract

/-! Word-growth calculus for actual classified source inputs. The size is
logarithmic in field count, alphabet length, rounded-value denominator and
original ratio height, and linear in the accuracy index. All observers are
erased analysis. No input encoding or capacity is queried by the algorithm. -/
namespace Blotto.GeneralPaperSourceWordGrowth
open GeneralPaperCodeAlphabet
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

structure Input where
  m : ℕ
  k : ℕ
  Qv : ℕ
  B : ℕ
  b : ℚ
  hb : 0<b ∧ b<1
  hB : RationalHeight b B
  reciprocal : Bool
  weights : FixedArrayTable m ℕ
  weight_sum : ∑ j,weights.read j=Qv

def alphabet (x : Input) : Alphabet := GeneralPaperProxyParameters.alphabet x.m x.k

def logSize (x : Input) : ℕ :=
  128+x.k+binaryWordWidth (x.m+1)+binaryWordWidth ((alphabet x).lambda+1)+
    binaryWordWidth (x.Qv+1)+binaryWordWidth (x.B+1)

theorem size_positive (x : Input) : 1≤logSize x := by unfold logSize; omega

@[fun_prop]
def Small (f : Input → ℕ) : Prop := ∃ C : ℕ,∀ x,binaryWordWidth (f x)≤C*logSize x

@[fun_prop]
def Tight (f : Input → ℕ) : Prop := ∃ C : ℕ,∀ x,f x≤C*logSize x

@[fun_prop]
theorem small_constant (c : ℕ) : Small (fun _ => c) :=
  ⟨binaryWordWidth c,fun x => by have h := size_positive x; nlinarith only [h]⟩

@[fun_prop]
theorem tight_constant (c : ℕ) : Tight (fun _ => c) :=
  ⟨c,fun x => by have h := size_positive x; nlinarith only [h]⟩

theorem of_tight {f : Input → ℕ} (hf : Tight f) : Small f := by
  rcases hf with ⟨C,hC⟩
  refine ⟨C+1,?_⟩
  intro x
  have h := Nat.log2_le_self (f x)
  have hc := hC x
  have hs := size_positive x
  unfold binaryWordWidth
  nlinarith only [h,hc,hs]

theorem dominated {f g : Input → ℕ} (hg : Small g) (h : ∀ x,f x≤g x) : Small f := by
  rcases hg with ⟨C,hC⟩
  exact ⟨C,fun x => (binaryWordWidth_mono (h x)).trans (hC x)⟩

@[fun_prop]
theorem small_add (f g : Input → ℕ) (hf : Small f) (hg : Small g) : Small (fun x => f x+g x) := by
  rcases hf with ⟨C,hC⟩
  rcases hg with ⟨D,hD⟩
  exact ⟨C+D,fun x => (GeneralPaperReferenceScaling.word_add (f x) (g x)).trans (by have := hC x; have := hD x; nlinarith)⟩

@[fun_prop]
theorem tight_add (f g : Input → ℕ) (hf : Tight f) (hg : Tight g) : Tight (fun x => f x+g x) := by
  rcases hf with ⟨C,hC⟩
  rcases hg with ⟨D,hD⟩
  exact ⟨C+D,fun x => by have := hC x; have := hD x; nlinarith⟩

@[fun_prop]
theorem small_mul (f g : Input → ℕ) (hf : Small f) (hg : Small g) : Small (fun x => f x*g x) := by
  rcases hf with ⟨C,hC⟩
  rcases hg with ⟨D,hD⟩
  exact ⟨C+D,fun x => (binaryWordWidth_mul (f x) (g x)).trans (by have := hC x; have := hD x; nlinarith)⟩

@[fun_prop]
theorem tight_mul_left (c : ℕ) (f : Input → ℕ) (hf : Tight f) : Tight (fun x => c*f x) := by
  rcases hf with ⟨C,hC⟩
  exact ⟨c*C,fun x => (Nat.mul_le_mul_left c (hC x)).trans_eq (by ring)⟩

@[fun_prop]
theorem tight_mul_right (f : Input → ℕ) (c : ℕ) (hf : Tight f) : Tight (fun x => f x*c) := by
  rcases hf with ⟨C,hC⟩
  exact ⟨C*c,fun x => (Nat.mul_le_mul_right c (hC x)).trans_eq (by ring)⟩

@[fun_prop]
theorem small_sub (f g : Input → ℕ) (hf : Small f) : Small (fun x => f x-g x) :=
  dominated hf (fun _ => Nat.sub_le _ _)

@[fun_prop]
theorem small_max (f g : Input → ℕ) (hf : Small f) (hg : Small g) : Small (fun x => max (f x) (g x)) :=
  dominated (small_add f g hf hg) (fun _ => by omega)

@[fun_prop]
theorem small_min (f g : Input → ℕ) (hf : Small f) : Small (fun x => min (f x) (g x)) :=
  dominated hf (fun _ => Nat.min_le_left ..)

@[fun_prop]
theorem small_power (f : Input → ℕ) (d : ℕ) (hf : Small f) : Small (fun x => (f x)^d) := by
  rcases hf with ⟨C,hC⟩
  refine ⟨1+d*C,?_⟩
  intro x
  have hw := GeneralPaperFastRationalBounds.word_power (f x) d
  have hm := Nat.mul_le_mul_left d (hC x)
  have hs := size_positive x
  nlinarith only [hw,hm,hs]

@[fun_prop]
theorem word_tight (f : Input → ℕ) (hf : Small f) : Tight (fun x => binaryWordWidth (f x)) := hf

@[fun_prop]
theorem word_small (f : Input → ℕ) (hf : Small f) : Small (fun x => binaryWordWidth (f x)) :=
  of_tight (word_tight f hf)

@[fun_prop]
theorem pow_two (f : Input → ℕ) (hf : Tight f) : Small (fun x => 2^(f x)) := by
  rcases hf with ⟨C,hC⟩
  refine ⟨2*C+1,?_⟩
  intro x
  have hw := GeneralPaperFastRationalBounds.word_power 2 (f x)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hw
  have hc := hC x
  have hs := size_positive x
  nlinarith only [hw,hc,hs]

@[fun_prop]
theorem small_successor (f : Input → ℕ) (hf : Small f) : Small (fun x => Nat.succ (f x)) := by
  simpa only [Nat.succ_eq_add_one] using small_add f (fun _ => 1) hf (small_constant 1)

@[fun_prop]
theorem tight_successor (f : Input → ℕ) (hf : Tight f) : Tight (fun x => Nat.succ (f x)) := by
  simpa only [Nat.succ_eq_add_one] using tight_add f (fun _ => 1) hf (tight_constant 1)

@[fun_prop]
theorem m_small : Small Input.m := by
  refine ⟨1,?_⟩
  intro x
  have hw := binaryWordWidth_mono (show x.m≤x.m+1 by omega)
  dsimp only [logSize]
  omega

@[fun_prop]
theorem Qv_small : Small Input.Qv := by
  refine ⟨1,?_⟩
  intro x
  have hw := binaryWordWidth_mono (show x.Qv≤x.Qv+1 by omega)
  dsimp only [logSize]
  omega

@[fun_prop]
theorem B_small : Small Input.B := by
  refine ⟨1,?_⟩
  intro x
  have hw := binaryWordWidth_mono (show x.B≤x.B+1 by omega)
  dsimp only [logSize]
  omega

@[fun_prop]
theorem k_tight : Tight Input.k := ⟨1,fun x => by dsimp only [logSize]; omega⟩

@[fun_prop]
theorem k_small : Small Input.k := of_tight k_tight

@[fun_prop]
theorem lambda_small : Small (fun x => (alphabet x).lambda) := by
  refine ⟨1,?_⟩
  intro x
  have hw := binaryWordWidth_mono (show (alphabet x).lambda≤(alphabet x).lambda+1 by omega)
  dsimp only [logSize]
  omega

@[fun_prop]
theorem scale_word_small : Small (fun x => binaryWordWidth (alphabet x).C) :=
  dominated (small_add _ _ lambda_small (small_constant 1)) (fun _x => GeneralPaperSourceAlphabetLower.scale_width _)

@[fun_prop]
theorem denominator_word_small : Small (fun x => binaryWordWidth (alphabet x).D) :=
  dominated scale_word_small (fun _x => binaryWordWidth_mono (GeneralPaperSourceAlphabetLower.order_le_scale _))

@[fun_prop]
theorem measure_tight : Tight (fun x => GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv) := by
  refine ⟨1,?_⟩
  intro x
  dsimp only [GeneralPaperSourcePreparationSizes.measure,logSize]
  omega

@[fun_prop]
theorem measure_small : Small (fun x => GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv) :=
  of_tight measure_tight

end Blotto.GeneralPaperSourceWordGrowth
