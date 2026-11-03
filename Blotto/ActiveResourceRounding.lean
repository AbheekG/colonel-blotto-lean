import Blotto.ActiveResourceList

/-! Resource rounding with head-pair selection and tail reuse. The finite
tree gives the conditional law; the direct trace below follows only one path.
Neither definition rescans the tail to select or retain fractional indices. -/

namespace Blotto
open scoped BigOperators

noncomputable def roundActiveResources {n : ℕ} {L : Allocation n} :
    ℕ → ActiveResourceList L → RoundingTree n
  | 0, s => .leaf s.resource
  | fuel + 1, s =>
    match he : s.active with
    | [] => .leaf s.resource
    | [_] => .leaf s.resource
    | a :: b :: tail =>
      let hp := s.selected_fractional he
      let p := resourcePair L s.resource a b hp.1 hp.2
      .fork p.probability ⟨le_of_lt p.probability_pos, le_of_lt p.probability_lt_one⟩
        (roundActiveResources fuel (s.update a b tail he p.upper))
        (roundActiveResources fuel (s.update a b tail he p.lower))

theorem roundActiveResources_height {n : ℕ} {L : Allocation n} (fuel : ℕ) (s : ActiveResourceList L) :
    (roundActiveResources fuel s).height ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [roundActiveResources, RoundingTree.height]
  | succ fuel ih =>
    unfold roundActiveResources
    split
    · simp [RoundingTree.height]
    · simp [RoundingTree.height]
    · change 1 + max (roundActiveResources fuel _).height (roundActiveResources fuel _).height ≤ fuel + 1
      exact (Nat.add_le_add_left (max_le (ih _) (ih _)) 1).trans (by omega)

theorem roundActiveResources_average {n : ℕ} {L : Allocation n} (fuel : ℕ) (s : ActiveResourceList L) :
    (roundActiveResources fuel s).average = s.resource := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    unfold roundActiveResources
    split
    · rfl
    · rfl
    · rename_i a b tail he
      simp only [RoundingTree.average, ih]
      funext j
      exact updatePair_expectation L s.resource (s.selected_distinct he)
        (s.selected_fractional he).1 (s.selected_fractional he).2 j

theorem roundActiveResources_leaves {n : ℕ} {L : Allocation n} (fuel : ℕ) (s : ActiveResourceList L)
    (hbox : InBox L s.resource) (hlen : s.active.length ≤ fuel + 1) :
    (roundActiveResources fuel s).ForLeaves (fun r =>
      InBox L r ∧ (∑ j, r j) = (∑ j, s.resource j) ∧ (fractionalSet L r).card ≤ 1) := by
  induction fuel generalizing s with
  | zero => exact ⟨hbox, rfl, by simpa only [s.length_eq_card] using hlen⟩
  | succ fuel ih =>
    unfold roundActiveResources
    split
    · rename_i he
      exact ⟨hbox, rfl, by rw [← s.length_eq_card, he]; simp⟩
    · rename_i a he
      exact ⟨hbox, rfl, by rw [← s.length_eq_card, he]; simp⟩
    · rename_i a b tail he
      let hp := s.selected_fractional he
      let p := resourcePair L s.resource a b hp.1 hp.2
      have hu : p.upper = p.lower ∨ p.upper = p.upper := Or.inr rfl
      have hl : p.lower = p.lower ∨ p.lower = p.upper := Or.inl rfl
      have hub := updatePair_inBox (s.selected_distinct he) hbox hp.1 hp.2 hu
      have hlb := updatePair_inBox (s.selected_distinct he) hbox hp.1 hp.2 hl
      have hun := s.update_length_lt a b tail he hu
      have hln := s.update_length_lt a b tail he hl
      have hU := ih (s.update a b tail he p.upper) hub (by omega)
      have hD := ih (s.update a b tail he p.lower) hlb (by omega)
      constructor
      · exact (roundActiveResources fuel (s.update a b tail he p.upper)).forLeaves_mono
          (fun r hr => ⟨hr.1, hr.2.1.trans (updatePair_sum s.resource (s.selected_distinct he) p.upper), hr.2.2⟩) hU
      · exact (roundActiveResources fuel (s.update a b tail he p.lower)).forLeaves_mono
          (fun r hr => ⟨hr.1, hr.2.1.trans (updatePair_sum s.resource (s.selected_distinct he) p.lower), hr.2.2⟩) hD

noncomputable def activeResourceTree {n : ℕ} (L r : Allocation n) : RoundingTree n :=
  roundActiveResources (n - 1) (ActiveResourceList.initial L r)

theorem activeResourceTree_contract {n : ℕ} (L r : Allocation n) (hbox : InBox L r) :
    (activeResourceTree L r).height ≤ n - 1 ∧ (activeResourceTree L r).average = r ∧
      (activeResourceTree L r).ForLeaves (fun q =>
        InBox L q ∧ (∑ j, q j) = (∑ j, r j) ∧ (fractionalSet L q).card ≤ 1) := by
  refine ⟨roundActiveResources_height _ _, roundActiveResources_average _ _, ?_⟩
  exact roundActiveResources_leaves (n - 1) (ActiveResourceList.initial L r) hbox (by
    have hl := ActiveResourceList.initial_length_le L r
    omega)

/-- Direct trace: no unused branch is evaluated, and the result includes the
number of pair updates actually performed. -/
noncomputable def runActiveResources {n : ℕ} {L : Allocation n} :
    ℕ → ActiveResourceList L → (ℕ → Bool) → ActiveResourceList L × ℕ
  | 0, s, _ => (s, 0)
  | fuel + 1, s, choice =>
    match he : s.active with
    | [] => (s, 0)
    | [_] => (s, 0)
    | a :: b :: tail =>
      let hp := s.selected_fractional he
      let p := resourcePair L s.resource a b hp.1 hp.2
      let z := if choice 0 then p.upper else p.lower
      let result := runActiveResources fuel (s.update a b tail he z) (fun k => choice (k + 1))
      (result.1, result.2 + 1)

theorem runActiveResources_updates {n : ℕ} {L : Allocation n} (fuel : ℕ)
    (s : ActiveResourceList L) (choice : ℕ → Bool) : (runActiveResources fuel s choice).2 ≤ fuel := by
  induction fuel generalizing s choice with
  | zero => simp [runActiveResources]
  | succ fuel ih =>
    unfold runActiveResources
    split
    · simp
    · simp
    · exact Nat.succ_le_succ (ih _ _)

theorem runActiveResources_eq_trace {n : ℕ} {L : Allocation n} (fuel : ℕ)
    (s : ActiveResourceList L) (choice : ℕ → Bool) :
    (runActiveResources fuel s choice).1.resource = (roundActiveResources fuel s).traceLeaf choice := by
  induction fuel generalizing s choice with
  | zero => rfl
  | succ fuel ih =>
    unfold runActiveResources roundActiveResources
    split
    · rfl
    · rfl
    · simp only [RoundingTree.traceLeaf]
      split_ifs <;> exact ih _ _

end Blotto
