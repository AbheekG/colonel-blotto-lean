import Blotto.GeneralPaperNativeRepresentativeSort

/-! The actual native stable sort supplies the mathematical sorting
permutation used by circle reconstruction. Equal values agree pointwise,
so neither ties nor the fixed names of deviation coordinates are changed. -/
namespace Blotto.GeneralPaperRepresentativeSortLaw
open GeneralPaperNativeRepresentativeSort
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem bijective {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) :
    Function.Bijective (run price index A values).1.read := by
  rw [data]
  exact ⟨GeneralPaperRowSort.order_injective values,GeneralPaperRowSort.order_surjective values⟩

noncomputable def permutation {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) : Equiv.Perm (Fin R) :=
  Equiv.ofBijective _ (bijective price index A values)

theorem monotone {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) :
    Monotone (fun a => values.read ((run price index A values).1.read a)) := by
  rw [data]
  exact GeneralPaperRowSort.order_value_mono values

theorem real_monotone {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) :
    Monotone (fun a => (values.read ((run price index A values).1.read a):ℝ)) := by
  intro a b hab
  have h := monotone price index A values hab
  dsimp only at h ⊢
  exact_mod_cast h

theorem real_sorted {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) (a : Fin R) :
    (values.read ((run price index A values).1.read a):ℝ)=
      GeneralPaperCircleSortedComparison.sorted (fun j => (values.read j:ℝ)) a := by
  have hm : Monotone ((fun j => (values.read j:ℝ)) ∘ permutation price index A values) :=
    real_monotone price index A values
  have he := (Tuple.comp_sort_eq_comp_iff_monotone (f:=fun j => (values.read j:ℝ))
    (σ:=permutation price index A values)).mpr hm
  exact congrFun he a

end Blotto.GeneralPaperRepresentativeSortLaw
