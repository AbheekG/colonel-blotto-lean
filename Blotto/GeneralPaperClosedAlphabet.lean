import Blotto.GeneralPaperCatalogueCanonicalGap
import Blotto.GeneralPaperCodeCoverage

/-! The finite closed bid alphabet used only to prove response completeness.
Its elements are exactly valid closed codes of the actual decoder. The
source does not enumerate this proof-only set.
-/
namespace Blotto.GeneralPaperClosedAlphabet
open scoped BigOperators Classical
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode
set_option autoImplicit false
set_option maxHeartbeats 3500000

def Closed (a : Alphabet) := {i : Fin (2^a.lambda) // Valid a false i.val}

noncomputable instance (a : Alphabet) : Fintype (Closed a) := inferInstanceAs (Fintype {i : Fin (2^a.lambda) // Valid a false i.val})

noncomputable def choice (a : Alphabet) (i : Closed a) : Choice :=
  Classical.choose ((GeneralPaperCodeDecodeComplete.valid_iff_decode a false i.val.val).mp i.property)

theorem decoded (a : Alphabet) (i : Closed a) : (decode a false i.val.val).choice=some (choice a i) :=
  Classical.choose_spec ((GeneralPaperCodeDecodeComplete.valid_iff_decode a false i.val.val).mp i.property)

def zero (a : Alphabet) : Closed a :=
  ⟨⟨0,Nat.two_pow_pos _⟩,by simpa only [Nat.mul_zero] using valid_grid a false 0 (Nat.zero_le _)⟩

noncomputable def value (a : Alphabet) (i : Closed a) : ℚ := (choice a i).threshold.value

theorem closed (a : Alphabet) (i : Closed a) : (choice a i).opened=false :=
  GeneralPaperCodeDecodeSound.candidate_closed a i.val.val (choice a i) (decoded a i)

theorem denominator (a : Alphabet) (i : Closed a) : (choice a i).threshold.den≤a.C :=
  (GeneralPaperCodeDecodeSound.decode_sound a false i.val.val (choice a i) (decoded a i)).2

theorem value_nonnegative (a : Alphabet) (i : Closed a) : 0≤value a i :=
  GeneralPaperCodeOrder.decoded_threshold_nonnegative a false i.val.val (choice a i) (decoded a i)

theorem value_le_one (a : Alphabet) (i : Closed a) : value a i≤1 :=
  GeneralPaperCodeOrder.decoded_threshold_le_one a false i.val.val (choice a i) (decoded a i)

theorem zero_value (a : Alphabet) : value a (zero a)=0 := by
  have he := (decoded a (zero a)).symm.trans (GeneralPaperCodeDecodeSound.decode_zero a false)
  have hc : choice a (zero a)=⟨grid a 0,false⟩ := Option.some.inj he
  unfold value
  rw [hc]
  exact grid_zero a

theorem affordable_exists (a : Alphabet) (y : ℝ) (hy : 0≤y) :
    ∃ i : Closed a, (value a i:ℝ)≤y ∧ ∀ j, (value a j:ℝ)≤y → value a j≤value a i := by
  let eligible := Finset.univ.filter (fun i : Closed a => (value a i:ℝ)≤y)
  have hz : zero a∈eligible := by simp only [eligible,Finset.mem_filter,Finset.mem_univ,true_and,zero_value,Rat.cast_zero]; exact hy
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image eligible (value a) ⟨zero a,hz⟩
  refine ⟨i,(Finset.mem_filter.mp hi).2,?_⟩
  intro j hj
  exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)

noncomputable def lower (a : Alphabet) (y : ℝ) (hy : 0≤y) : Closed a := Classical.choose (affordable_exists a y hy)

theorem lower_le (a : Alphabet) (y : ℝ) (hy : 0≤y) : (value a (lower a y hy):ℝ)≤y :=
  (Classical.choose_spec (affordable_exists a y hy)).1

theorem lower_greatest (a : Alphabet) (y : ℝ) (hy : 0≤y) (j : Closed a) (hj : (value a j:ℝ)≤y) :
    value a j≤value a (lower a y hy) := (Classical.choose_spec (affordable_exists a y hy)).2 j hj

theorem threshold_gap (a : Alphabet) (i j : Closed a) (m qbar : ℕ) (hm : 0<m) (hQ : 0<qbar)
    (hij : value a i<value a j) : value a i+GeneralPaperTagBudgetTransfer.shift m qbar a.C<value a j := by
  have hs := GeneralPaperCodePhysicalOrder.shift_lt_threshold_gap a m qbar hm hQ
  have hg := Farey.bounded_separation a.C (denominator a i) (denominator a j) hij
  dsimp only [value] at *
  linarith only [hs,hg]

end Blotto.GeneralPaperClosedAlphabet
