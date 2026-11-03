import Blotto.FiniteAnchorTransport
import Mathlib.Data.Finset.Max

/-! Exact continuous-response transport between finite real catalogues.
A greatest affordable source label is constructed by a finite maximum.
Every open target option uses a positive bump derived from all target gaps
and the actual total budget slack. Field orders and tuple-budget signs are
the only hypotheses; the signed order cell supplies them separately. -/

namespace Blotto.FiniteAnchorResponseTransport
open scoped BigOperators Classical

structure Catalogue {m K : ℕ} (old target : Fin m → Fin K → ℝ) (budget : ℝ) : Prop where
  zero : ∀ field, ∃ label, old field label = 0 ∧ target field label = 0
  target_nonnegative : ∀ field label, 0 ≤ target field label
  order : ∀ field left right, old field left < old field right ↔ target field left < target field right
  equal : ∀ field left right, old field left = old field right ↔ target field left = target field right
  sum_lt : ∀ labels : Fin m → Fin K, (∑ field, old field (labels field)) < budget ↔
    (∑ field, target field (labels field)) < budget
  sum_eq : ∀ labels : Fin m → Fin K, (∑ field, old field (labels field)) = budget ↔
    (∑ field, target field (labels field)) = budget

theorem Catalogue.reverse {m K : ℕ} {old target : Fin m → Fin K → ℝ} {budget : ℝ}
    (h : Catalogue old target budget) (hOld : ∀ field label, 0 ≤ old field label) :
    Catalogue target old budget := by
  refine ⟨?_,hOld,(fun j i k => (h.order j i k).symm),
    (fun j i k => (h.equal j i k).symm),(fun labels => (h.sum_lt labels).symm),
    (fun labels => (h.sum_eq labels).symm)⟩
  intro field
  obtain ⟨label,ho,ht⟩ := h.zero field
  exact ⟨label,ht,ho⟩

theorem affordable_maximum {K : ℕ} (old : Fin K → ℝ)
    (hZero : ∃ label, old label = 0) (y : ℝ) (hy : 0 ≤ y) :
    ∃ label, old label ≤ y ∧ ∀ i, old i ≤ y → old i ≤ old label := by
  let eligible := Finset.univ.filter (fun label : Fin K => old label ≤ y)
  obtain ⟨zero,hzero⟩ := hZero
  have hz : zero ∈ eligible := by simp [eligible,hzero,hy]
  obtain ⟨label,hl,hm⟩ := Finset.exists_max_image eligible old ⟨zero,hz⟩
  exact ⟨label,(Finset.mem_filter.mp hl).2,
    fun i hi => hm i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)⟩

noncomputable def gaps {m K : ℕ} (target : Fin m → Fin K → ℝ) : Finset ℝ :=
  insert 1 (Finset.univ.image (fun p : Fin m × (Fin K × Fin K) =>
    if target p.1 p.2.1 < target p.1 p.2.2 then target p.1 p.2.2 - target p.1 p.2.1 else 1))

noncomputable def gap {m K : ℕ} (target : Fin m → Fin K → ℝ) : ℝ :=
  (gaps target).inf' (Finset.insert_nonempty _ _) id

theorem gap_positive {m K : ℕ} (target : Fin m → Fin K → ℝ) : 0 < gap target := by
  apply (Finset.lt_inf'_iff _).mpr
  intro value hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · norm_num
  · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hv
    split_ifs with hp
    · exact sub_pos.mpr hp
    · norm_num

theorem gap_le {m K : ℕ} (target : Fin m → Fin K → ℝ) (field : Fin m) (left right : Fin K)
    (h : target field left < target field right) :
    gap target ≤ target field right - target field left := by
  apply Finset.inf'_le
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(field,left,right),Finset.mem_univ _,by simp [h]⟩

theorem scalar_share {K : ℕ} (old target : Fin K → ℝ) (label : Fin K) (y bump : ℝ)
    (hBelow : old label ≤ y) (hGreatest : ∀ i, old i ≤ y → old i ≤ old label)
    (hOrder : ∀ i j, old i < old j ↔ target i < target j)
    (hEqual : ∀ i j, old i = old j ↔ target i = target j)
    (hBump : 0 < bump) (hGap : ∀ i, target label < target i → target label + bump < target i) :
    ∀ i, share y (old i) =
      share (target label + if old label = y then 0 else bump) (target i) := by
  intro i
  rcases lt_trichotomy (old i) (old label) with hi | hi | hi
  · have ho : old i < y := hi.trans_le hBelow
    have ht := (hOrder i label).mp hi
    have hb : target i < target label + if old label = y then 0 else bump := by
      split_ifs <;> linarith
    simp [share,ho,hb]
  · have ht := (hEqual i label).mp hi
    by_cases hc : old label = y
    · simp [share,hi,ht,hc]
    · have ho : old i < y := by rw [hi]; exact lt_of_le_of_ne hBelow hc
      simp [share,ho,ht,hc,hBump]
  · have ho : y < old i := lt_of_not_ge (fun h => (not_le_of_gt hi) (hGreatest i h))
    have ht := (hOrder label i).mp hi
    have hb : target label + (if old label = y then 0 else bump) < target i := by
      split_ifs
      · simpa using ht
      · exact hGap i ht
    simp [share,not_lt_of_gt ho,ne_of_lt ho,not_lt_of_gt hb,ne_of_lt hb]

/-- Every actual feasible real response has a feasible target response with
exact shares against ALL labels. Open coordinates use one finite-gap/slack
bump; no response selection or perturbation oracle is assumed. -/
theorem response_exists {m K : ℕ} (old target : Fin m → Fin K → ℝ) (budget : ℝ)
    (h : Catalogue old target budget) (y : Allocation m) (hy : Feasible budget y) :
    ∃ z : Allocation m, Feasible budget z ∧
      ∀ field label, share (y field) (old field label) = share (z field) (target field label) := by
  have hm : ∀ field, ∃ label, old field label ≤ y field ∧
      ∀ i, old field i ≤ y field → old field i ≤ old field label :=
    fun field => affordable_maximum _ (by obtain ⟨label,ho,_⟩ := h.zero field; exact ⟨label,ho⟩) _ (hy.1 field)
  choose labels hBelow hGreatest using hm
  have hBase : (∑ field, old field (labels field)) ≤ budget :=
    (Finset.sum_le_sum (fun field _ => hBelow field)).trans hy.2
  have htBase : (∑ field, target field (labels field)) ≤ budget := by
    rcases lt_or_eq_of_le hBase with hs | he
    · exact ((h.sum_lt labels).mp hs).le
    · exact ((h.sum_eq labels).mp he).le
  by_cases hClosed : ∀ field, old field (labels field) = y field
  · refine ⟨fun field => target field (labels field),⟨fun field => h.target_nonnegative field _,htBase⟩,?_⟩
    intro field label
    have he := scalar_share (old field) (target field) (labels field) (y field) (gap target / 2)
      (hBelow field) (hGreatest field) (h.order field) (h.equal field)
      (by positivity [gap_positive target]) ?_ label
    · simpa [hClosed field] using he
    · intro i hi
      have hp := gap_positive target
      have hg := gap_le target field (labels field) i hi
      linarith
  · have hs : (∑ field, old field (labels field)) < budget := by
      have hn : ∃ field, old field (labels field) < y field := by
        push Not at hClosed
        obtain ⟨field,hne⟩ := hClosed
        exact ⟨field,lt_of_le_of_ne (hBelow field) hne⟩
      exact (Finset.sum_lt_sum (fun field _ => hBelow field)
        (by obtain ⟨field,hf⟩ := hn; exact ⟨field,Finset.mem_univ _,hf⟩)).trans_le hy.2
    have hSlack := (h.sum_lt labels).mp hs
    let bump := min (gap target / 2) ((budget - ∑ field, target field (labels field)) / (m + 1))
    have hBump : 0 < bump := lt_min (by positivity [gap_positive target]) (by positivity)
    have hGap : bump ≤ gap target / 2 := min_le_left _ _
    have hBudgetBump : (m : ℝ) * bump ≤ budget - ∑ field, target field (labels field) := by
      have hb := min_le_right (gap target / 2) ((budget - ∑ field, target field (labels field)) / (m + 1))
      have hd : (0 : ℝ) < m + 1 := by positivity
      have hv : bump * (m + 1) ≤ budget - ∑ field, target field (labels field) :=
        (le_div_iff₀ hd).mp hb
      nlinarith
    let z : Allocation m := fun field => target field (labels field) +
      if old field (labels field) = y field then 0 else bump
    refine ⟨z,⟨?_,?_⟩,?_⟩
    · intro field
      dsimp [z]
      split_ifs <;> linarith [h.target_nonnegative field (labels field)]
    · change (∑ field, (target field (labels field) + if old field (labels field) = y field then 0 else bump)) ≤ budget
      rw [Finset.sum_add_distrib]
      have hb : (∑ field : Fin m, if old field (labels field) = y field then 0 else bump) ≤ (m : ℝ) * bump := by
        calc
          _ ≤ ∑ _field : Fin m, bump := Finset.sum_le_sum (fun field _ => by split_ifs <;> linarith)
          _ = (m : ℝ) * bump := by simp
      linarith
    · intro field label
      apply scalar_share (old field) (target field) (labels field) (y field) bump
        (hBelow field) (hGreatest field) (h.order field) (h.equal field) hBump ?_ label
      intro i hi
      have hp := gap_positive target
      have hg := gap_le target field (labels field) i hi
      linarith

end Blotto.FiniteAnchorResponseTransport
