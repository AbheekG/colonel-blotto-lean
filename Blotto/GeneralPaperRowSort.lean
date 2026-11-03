import Blotto.GeneralPaperComputedThreshold
import Blotto.CumulativeGuideSorting

/-! Deterministic merge sorting of row references by one rational coordinate,
with original row index as tie breaker. The inverse permutation is built by
one indexed scatter pass; no search for each original row is executed.
-/
namespace Blotto.GeneralPaperRowSort
set_option autoImplicit false
set_option maxHeartbeats 1500000

def Before {T : ℕ} (value : Fin T → ℚ) (a b : Fin T) : Prop :=
  value a<value b ∨ (value a=value b ∧ a≤b)

instance {T : ℕ} (value : Fin T → ℚ) (a b : Fin T) : Decidable (Before value a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem before_trans {T : ℕ} (value : Fin T → ℚ) (a b c : Fin T)
    (hab : Before value a b) (hbc : Before value b c) : Before value a c := by
  rcases hab with hab | ⟨hab,ha⟩ <;> rcases hbc with hbc | ⟨hbc,hb⟩
  · exact Or.inl (hab.trans hbc)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨hab.trans hbc,ha.trans hb⟩

theorem before_total {T : ℕ} (value : Fin T → ℚ) (a b : Fin T) : Before value a b ∨ Before value b a := by
  rcases lt_trichotomy (value a) (value b) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total a b with ha | hb
    · exact Or.inl (Or.inr ⟨h,ha⟩)
    · exact Or.inr (Or.inr ⟨h.symm,hb⟩)
  · exact Or.inr (Or.inl h)

def sorted {T : ℕ} (value : FixedArrayTable T ℚ) : List (Fin T) :=
  (List.finRange T).mergeSort (fun a b => decide (Before value.read a b))

theorem sorted_perm {T : ℕ} (value : FixedArrayTable T ℚ) : (sorted value).Perm (List.finRange T) :=
  List.mergeSort_perm _ _

theorem sorted_length {T : ℕ} (value : FixedArrayTable T ℚ) : (sorted value).length=T := by
  simpa only [List.length_finRange] using (sorted_perm value).length_eq

theorem sorted_nodup {T : ℕ} (value : FixedArrayTable T ℚ) : (sorted value).Nodup :=
  (sorted_perm value).nodup_iff.mpr (List.nodup_finRange T)

theorem sorted_order {T : ℕ} (value : FixedArrayTable T ℚ) : (sorted value).Pairwise (Before value.read) := by
  have h := List.pairwise_mergeSort
    (le := fun a b : Fin T => decide (Before value.read a b))
    (fun a b c hab hbc => decide_eq_true (before_trans value.read a b c
      (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (fun a b => by
      rcases before_total value.read a b with h | h
      · simp only [decide_eq_true h,Bool.true_or]
      · simp only [decide_eq_true h,Bool.or_true]) (List.finRange T)
  simpa only [sorted,decide_eq_true_eq] using h

def order {T : ℕ} (value : FixedArrayTable T ℚ) : FixedArrayTable T (Fin T) :=
  ⟨(sorted value).toArray,by simp only [List.size_toArray,sorted_length]⟩

theorem order_read {T : ℕ} (value : FixedArrayTable T ℚ) (r : Fin T) :
    (order value).read r=(sorted value).get ⟨r.val,by rw [sorted_length]; exact r.isLt⟩ := by
  simp only [order,FixedArrayTable.read,List.getElem_toArray,List.get_eq_getElem]

theorem order_injective {T : ℕ} (value : FixedArrayTable T ℚ) : Function.Injective (order value).read := by
  intro a b hab
  rw [order_read,order_read] at hab
  have h := (sorted_nodup value).injective_get hab
  exact Fin.ext (congrArg (fun r : Fin (sorted value).length => r.val) h)

theorem order_surjective {T : ℕ} (value : FixedArrayTable T ℚ) : Function.Surjective (order value).read :=
  (Finite.injective_iff_surjective).mp (order_injective value)

theorem order_value_mono {T : ℕ} (value : FixedArrayTable T ℚ) :
    Monotone (fun r => value.read ((order value).read r)) := by
  intro a b hab
  rcases lt_or_eq_of_le hab with hlt | heq
  · have h := (List.pairwise_iff_get.mp (sorted_order value))
      ⟨a.val,by rw [sorted_length]; exact a.isLt⟩
      ⟨b.val,by rw [sorted_length]; exact b.isLt⟩ hlt
    rw [← order_read,← order_read] at h
    exact h.elim le_of_lt (fun he => he.1.le)
  · rw [heq]

def assignments {T : ℕ} (permutation : FixedArrayTable T (Fin T)) : List (Fin T × Fin T) :=
  List.ofFn (fun r => (permutation.read r,r))

def scatterInverse {T : ℕ} (hT : 0<T) (permutation : FixedArrayTable T (Fin T)) : FixedArrayTable T (Fin T) :=
  (FixedArrayTable.ofFn (fun _ => (⟨0,hT⟩ : Fin T))).patch (assignments permutation)

theorem scatter_at {T : ℕ} (hT : 0<T) (permutation : FixedArrayTable T (Fin T))
    (hInjective : Function.Injective permutation.read) (r : Fin T) :
    (scatterInverse hT permutation).read (permutation.read r)=r := by
  apply FixedArrayTable.read_patch_at
  · intro e he hKey
    obtain ⟨s,rfl⟩ := List.mem_ofFn.mp he
    exact hInjective hKey
  · simp only [assignments,List.map_ofFn,List.mem_ofFn]
    exact ⟨r,rfl⟩

structure Sorted (T : ℕ) (value : FixedArrayTable T ℚ) where
  forward : FixedArrayTable T (Fin T)
  inverse : FixedArrayTable T (Fin T)
  inverse_forward : ∀ r,inverse.read (forward.read r)=r
  forward_inverse : ∀ i,forward.read (inverse.read i)=i
  ordered : Monotone (fun r => value.read (forward.read r))

def build {T : ℕ} (hT : 0<T) (value : FixedArrayTable T ℚ) : Sorted T value :=
  let forward := order value
  let inverse := scatterInverse hT forward
  have hi : ∀ r,inverse.read (forward.read r)=r := scatter_at hT forward (order_injective value)
  have hf : ∀ i,forward.read (inverse.read i)=i := by
    intro i
    obtain ⟨r,rfl⟩ := order_surjective value i
    rw [hi]
  ⟨forward,inverse,hi,hf,order_value_mono value⟩

theorem Sorted.inverse_injective {T : ℕ} {value : FixedArrayTable T ℚ} (p : Sorted T value) :
    Function.Injective p.inverse.read := by
  intro a b h
  have he := congrArg p.forward.read h
  simpa only [p.forward_inverse] using he

theorem Sorted.inverse_surjective {T : ℕ} {value : FixedArrayTable T ℚ} (p : Sorted T value) :
    Function.Surjective p.inverse.read := fun r => ⟨p.forward.read r,p.inverse_forward r⟩

theorem build_tie_order {T : ℕ} (hT : 0<T) (value : FixedArrayTable T ℚ) (a b : Fin T)
    (hab : a<b) (hEqual : value.read ((build hT value).forward.read a)=value.read ((build hT value).forward.read b)) :
    (build hT value).forward.read a ≤ (build hT value).forward.read b := by
  have h := (List.pairwise_iff_get.mp (sorted_order value))
    ⟨a.val,by rw [sorted_length]; exact a.isLt⟩
    ⟨b.val,by rw [sorted_length]; exact b.isLt⟩ hab
  rw [← order_read,← order_read] at h
  change value.read ((order value).read a)=value.read ((order value).read b) at hEqual
  exact h.elim (fun hh => (ne_of_lt hh hEqual).elim) (fun hh => hh.2)

end Blotto.GeneralPaperRowSort
