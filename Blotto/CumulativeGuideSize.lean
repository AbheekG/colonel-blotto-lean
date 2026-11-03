import Blotto.CumulativeGuidePruning

/-! Geometric retained-height bounds for the actual cumulative lower-guide
scan. The first positive retained mass is explicit; no minimum-mass oracle or
logarithmic dynamic-range bound is assumed for free. -/

namespace Blotto
open scoped Classical

namespace CumulativeGuidePruning

def totalMass (atoms : List Atom) : ℚ := (atoms.map Prod.snd).sum

def heightTrace (gamma : ℚ) : List Atom → ℚ → ℚ → List ℚ
  | [], _, _ => []
  | atom :: rest, cumulative, retained =>
      let next := cumulative + atom.2
      if gamma * retained < next then next :: heightTrace gamma rest next next
      else heightTrace gamma rest next retained

def cumulativeHeights : List Atom → ℚ → List ℚ
  | [], _ => []
  | atom :: rest, base =>
      let next := base + atom.2
      next :: cumulativeHeights rest next

theorem totalMass_nonnegative (atoms : List Atom) (h : Nonnegative atoms) : 0 ≤ totalMass atoms := by
  apply List.sum_nonneg
  intro q hq
  rcases List.mem_map.mp hq with ⟨atom, ha, rfl⟩
  exact h atom ha

theorem heightTrace_eq_cumulativeHeights (atoms : List Atom) (gamma cumulative retained : ℚ) :
    heightTrace gamma atoms cumulative retained = cumulativeHeights (scan gamma atoms cumulative retained) retained := by
  induction atoms generalizing cumulative retained with
  | nil => rfl
  | cons atom rest ih =>
    dsimp only [heightTrace, scan]
    split_ifs with hkeep
    · change (cumulative + atom.2) :: heightTrace gamma rest (cumulative + atom.2) (cumulative + atom.2) =
        (retained + (cumulative + atom.2 - retained)) ::
          cumulativeHeights (scan gamma rest (cumulative + atom.2) (cumulative + atom.2))
            (retained + (cumulative + atom.2 - retained))
      have he : retained + (cumulative + atom.2 - retained) = cumulative + atom.2 := by ring
      rw [he, ih]
    · exact ih _ _

theorem cumulativeHeights_length (atoms : List Atom) (base : ℚ) :
    (cumulativeHeights atoms base).length = atoms.length := by
  induction atoms generalizing base with
  | nil => rfl
  | cons atom rest ih => simp only [cumulativeHeights, List.length_cons, ih]

theorem heightTrace_length (atoms : List Atom) (gamma cumulative retained : ℚ) :
    (heightTrace gamma atoms cumulative retained).length = (scan gamma atoms cumulative retained).length := by
  rw [heightTrace_eq_cumulativeHeights, cumulativeHeights_length]

theorem heightTrace_above_retained (atoms : List Atom) (gamma cumulative retained : ℚ)
    (hg : 1 ≤ gamma) (hh : 0 ≤ retained) :
    ∀ height ∈ heightTrace gamma atoms cumulative retained, gamma * retained < height := by
  induction atoms generalizing cumulative retained with
  | nil => intro h hm; simp [heightTrace] at hm
  | cons atom rest ih =>
    dsimp only [heightTrace]
    split_ifs with hkeep
    · intro height hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hkeep
      · have hg0 : 0 ≤ gamma := le_trans (by norm_num) hg
        have hret : retained ≤ cumulative + atom.2 := by nlinarith
        have hnext0 : 0 ≤ cumulative + atom.2 := by nlinarith
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hret hg0) (ih _ _ hnext0 height hm)
    · exact ih _ _ hh

theorem heightTrace_geometric (atoms : List Atom) (gamma cumulative retained : ℚ)
    (hg : 1 ≤ gamma) (hh : 0 ≤ retained) :
    (heightTrace gamma atoms cumulative retained).Pairwise (fun a b => gamma * a < b) := by
  induction atoms generalizing cumulative retained with
  | nil => simp [heightTrace]
  | cons atom rest ih =>
    dsimp only [heightTrace]
    split_ifs with hkeep
    · have hn : 0 ≤ cumulative + atom.2 := by nlinarith
      exact List.pairwise_cons.mpr ⟨heightTrace_above_retained rest gamma _ _ hg hn, ih _ _ hn⟩
    · exact ih _ _ hh

theorem heightTrace_total_bound (atoms : List Atom) (gamma cumulative retained : ℚ)
    (h : Nonnegative atoms) :
    ∀ height ∈ heightTrace gamma atoms cumulative retained, height ≤ cumulative + totalMass atoms := by
  induction atoms generalizing cumulative retained with
  | nil => intro height hm; simp [heightTrace] at hm
  | cons atom rest ih =>
    have ht : Nonnegative rest := fun a ha => h a (by simp [ha])
    dsimp only [heightTrace]
    split_ifs
    · intro height hm
      rcases List.mem_cons.mp hm with rfl | hm
      · have hn := totalMass_nonnegative rest ht
        simp only [totalMass, List.map_cons, List.sum_cons]
        change cumulative + atom.2 ≤ cumulative + (atom.2 + totalMass rest)
        linarith
      · have he := ih _ _ ht height hm
        simpa only [totalMass, List.map_cons, List.sum_cons, add_assoc] using he
    · intro height hm
      have he := ih _ _ ht height hm
      simpa only [totalMass, List.map_cons, List.sum_cons, add_assoc] using he

theorem scan_total_envelope (atoms : List Atom) (gamma cumulative retained : ℚ)
    (hg : 1 ≤ gamma) (h : Nonnegative atoms) (hc : 0 ≤ cumulative) (hh : 0 ≤ retained)
    (hl : retained ≤ cumulative) (hu : cumulative ≤ gamma * retained) :
    retained + totalMass (scan gamma atoms cumulative retained) ≤ cumulative + totalMass atoms ∧
      cumulative + totalMass atoms ≤ gamma * (retained + totalMass (scan gamma atoms cumulative retained)) := by
  induction atoms generalizing cumulative retained with
  | nil => simpa only [scan, totalMass, List.map_nil, List.sum_nil, add_zero] using And.intro hl hu
  | cons atom rest ih =>
    have ha := h atom (by simp)
    have ht : Nonnegative rest := fun a ha => h a (by simp [ha])
    have hn : 0 ≤ cumulative + atom.2 := add_nonneg hc ha
    have hr : retained ≤ cumulative + atom.2 := le_trans hl (le_add_of_nonneg_right ha)
    dsimp only [scan]
    by_cases hkeep : gamma * retained < cumulative + atom.2
    · rw [ite_eq_left hkeep]
      have huNext : cumulative + atom.2 ≤ gamma * (cumulative + atom.2) := by nlinarith
      have he := ih _ _ ht hn hn le_rfl huNext
      change retained + ((cumulative + atom.2 - retained) +
          totalMass (scan gamma rest (cumulative + atom.2) (cumulative + atom.2))) ≤
          cumulative + (atom.2 + totalMass rest) ∧
        cumulative + (atom.2 + totalMass rest) ≤ gamma *
          (retained + ((cumulative + atom.2 - retained) +
            totalMass (scan gamma rest (cumulative + atom.2) (cumulative + atom.2))))
      constructor <;> linarith [he.1, he.2]
    · rw [ite_eq_right hkeep]
      have he := ih _ _ ht hn hh hr (le_of_not_gt hkeep)
      simpa only [totalMass, List.map_cons, List.sum_cons, add_assoc] using he

theorem prune_nonempty_of_positive_total (atoms : List Atom) (gamma : ℚ) (hg : 1 ≤ gamma)
    (h : Nonnegative atoms) (ht : 0 < totalMass atoms) : prune gamma atoms ≠ [] := by
  intro hz
  have he := scan_total_envelope atoms gamma 0 0 hg h le_rfl le_rfl le_rfl (by simp)
  simp only [zero_add] at he
  change totalMass (prune gamma atoms) ≤ totalMass atoms ∧
    totalMass atoms ≤ gamma * totalMass (prune gamma atoms) at he
  rw [hz] at he
  simp only [totalMass, List.map_nil, List.sum_nil, mul_zero] at he
  unfold totalMass at ht
  linarith [he.2]

theorem prune_heights_positive (atoms : List Atom) (gamma : ℚ) (hg : 1 ≤ gamma) :
    ∀ height ∈ cumulativeHeights (prune gamma atoms) 0, 0 < height := by
  unfold prune
  rw [← heightTrace_eq_cumulativeHeights]
  have he := heightTrace_above_retained atoms gamma 0 0 hg le_rfl
  simpa only [mul_zero] using he

theorem prune_heights_geometric (atoms : List Atom) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (cumulativeHeights (prune gamma atoms) 0).Pairwise (fun a b => gamma * a < b) := by
  unfold prune
  rw [← heightTrace_eq_cumulativeHeights]
  exact heightTrace_geometric atoms gamma 0 0 hg le_rfl

theorem prune_heights_total_bound (atoms : List Atom) (gamma : ℚ) (h : Nonnegative atoms) :
    ∀ height ∈ cumulativeHeights (prune gamma atoms) 0, height ≤ totalMass atoms := by
  unfold prune
  rw [← heightTrace_eq_cumulativeHeights]
  simpa only [zero_add] using heightTrace_total_bound atoms gamma 0 0 h

theorem geometric_list_power_bound (heights : List ℚ) (gamma first : ℚ)
    (hg : 0 ≤ gamma) (hfirst : ∀ height ∈ heights, gamma * first ≤ height)
    (hgeom : heights.Pairwise (fun a b => gamma * a ≤ b))
    (index : ℕ) (hi : index < heights.length) :
    gamma ^ (index + 1) * first ≤ heights[index] := by
  induction heights generalizing first index with
  | nil => simp at hi
  | cons head rest ih =>
    cases index with
    | zero => simpa only [Nat.zero_add, pow_one, List.getElem_cons_zero] using hfirst head (by simp)
    | succ index =>
      have ht : ∀ height ∈ rest, gamma * head ≤ height := (List.pairwise_cons.mp hgeom).1
      have hs := (List.pairwise_cons.mp hgeom).2
      have hiTail : index < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      have he := ih head ht hs index hiTail
      have hh := hfirst head (by simp)
      have hpow : 0 ≤ gamma ^ (index + 1) := pow_nonneg hg _
      have hb := mul_le_mul_of_nonneg_left hh hpow
      calc
        gamma ^ (index + 1 + 1) * first = gamma ^ (index + 1) * (gamma * first) := by
          rw [pow_succ]
          ring
        _ ≤ gamma ^ (index + 1) * head := hb
        _ ≤ rest[index] := he

theorem positive_geometric_list_power (first : ℚ) (rest : List ℚ) (gamma : ℚ)
    (hg : 0 ≤ gamma) (hgeom : (first :: rest).Pairwise (fun a b => gamma * a ≤ b))
    (index : ℕ) (hi : index < (first :: rest).length) :
    gamma ^ index * first ≤ (first :: rest)[index] := by
  cases index with
  | zero => simp only [pow_zero, one_mul, List.getElem_cons_zero, le_refl]
  | succ index =>
    exact geometric_list_power_bound rest gamma first hg (List.pairwise_cons.mp hgeom).1
      (List.pairwise_cons.mp hgeom).2 index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)

theorem prune_size_power_bound (atoms : List Atom) (gamma : ℚ) (hg : 1 ≤ gamma)
    (h : Nonnegative atoms) (first : ℚ) (rest : List ℚ)
    (heights : cumulativeHeights (prune gamma atoms) 0 = first :: rest) :
    0 < first ∧ gamma ^ ((prune gamma atoms).length - 1) * first ≤ totalMass atoms := by
  have hp := prune_heights_positive atoms gamma hg
  rw [heights] at hp
  have hgeom := prune_heights_geometric atoms gamma hg
  rw [heights] at hgeom
  have hgeomWeak : (first :: rest).Pairwise (fun a b => gamma * a ≤ b) :=
    hgeom.imp (fun he => he.le)
  have hlen : (prune gamma atoms).length = rest.length + 1 := by
    have he := cumulativeHeights_length (prune gamma atoms) 0
    rw [heights, List.length_cons] at he
    exact he.symm
  have hindex : rest.length < (first :: rest).length := by simp
  have he := positive_geometric_list_power first rest gamma
    (le_trans (by norm_num) hg) hgeomWeak rest.length hindex
  have ht := prune_heights_total_bound atoms gamma h ((first :: rest)[rest.length])
    (by rw [heights]; exact List.getElem_mem hindex)
  refine ⟨hp first (by simp), ?_⟩
  rw [hlen, Nat.add_sub_cancel]
  exact he.trans ht

theorem prune_positive_total_size (atoms : List Atom) (gamma : ℚ) (hg : 1 ≤ gamma)
    (h : Nonnegative atoms) (ht : 0 < totalMass atoms) :
    ∃ first : ℚ, ∃ rest : List ℚ,
      cumulativeHeights (prune gamma atoms) 0 = first :: rest ∧
        0 < first ∧ gamma ^ ((prune gamma atoms).length - 1) * first ≤ totalMass atoms := by
  cases he : prune gamma atoms with
  | nil => exact False.elim (prune_nonempty_of_positive_total atoms gamma hg h ht he)
  | cons atom rest =>
    refine ⟨atom.2, cumulativeHeights rest atom.2, ?_, ?_⟩
    · simp only [cumulativeHeights, zero_add]
    · have hp := prune_size_power_bound atoms gamma hg h atom.2 (cumulativeHeights rest atom.2)
        (by simp only [he, cumulativeHeights, zero_add])
      simpa only [he] using hp

theorem prune_leading_zero {atom : Atom} (rest : List Atom) (gamma : ℚ) (hz : atom.2 = 0) :
    prune gamma (atom :: rest) = prune gamma rest := by
  unfold prune
  simp only [scan, hz, add_zero, mul_zero, lt_self_iff_false, ite_false]

theorem prune_first_positive {atom : Atom} (rest : List Atom) (gamma : ℚ) (hp : 0 < atom.2) :
    prune gamma (atom :: rest) = (atom.1, atom.2) :: scan gamma rest atom.2 atom.2 := by
  unfold prune
  simp only [scan, zero_add, mul_zero, hp, ite_true, sub_zero]

theorem bernoulli_power_lower (delta : ℚ) (hd : 0 ≤ delta) (n : ℕ) :
    1 + (n : ℚ) * delta ≤ (1 + delta) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n : ℚ) := by positivity
    have hrem : 0 ≤ (n : ℚ) * delta ^ 2 := mul_nonneg hn (sq_nonneg delta)
    have hprod := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1 + delta)
    rw [pow_succ]
    push_cast
    nlinarith

theorem prune_delta_count_bound (atoms : List Atom) (delta : ℚ) (hd : 0 ≤ delta)
    (h : Nonnegative atoms) (first : ℚ) (rest : List ℚ)
    (heights : cumulativeHeights (prune (1 + delta) atoms) 0 = first :: rest) :
    (1 + (((prune (1 + delta) atoms).length - 1 : ℕ) : ℚ) * delta) * first ≤ totalMass atoms := by
  have he := prune_size_power_bound atoms (1 + delta) (by linarith) h first rest heights
  have hb := mul_le_mul_of_nonneg_right
    (bernoulli_power_lower delta hd ((prune (1 + delta) atoms).length - 1)) he.1.le
  exact hb.trans he.2

end CumulativeGuidePruning
end Blotto
