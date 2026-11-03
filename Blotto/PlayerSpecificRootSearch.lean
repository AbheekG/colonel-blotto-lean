import Blotto.PlayerSpecificCellCandidates

/-! First passing candidate, rather than first positive root. Scalar tests
are executed by the stated arithmetic/comparison real-RAM operations. The
fixed charges cover the bounded-size root list, filtering, field accesses,
and control. Root acquisition itself is the degree-three primitive. -/
namespace Blotto.PlayerSpecificRootSearch
open PlayerSpecificCubic PlayerSpecificCells PlayerSpecificCellCandidates
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable def test (c : Cell) (b : ℝ) : List ℝ → Option ℝ×ℕ
  | [] => (none,4)
  | gamma::rest =>
    if Passes c b gamma then (some gamma,48) else
      let tail := test c b rest
      (tail.1,tail.2+48)

theorem test_work (c : Cell) (b : ℝ) (xs : List ℝ) : (test c b xs).2≤48*xs.length+4 := by
  induction xs with
  | nil => exact le_rfl
  | cons gamma rest ih =>
    rw [test]
    split <;> simp only [List.length_cons]
    · omega
    · omega

theorem test_sound (c : Cell) (b : ℝ) (xs : List ℝ) (gamma : ℝ)
    (h : (test c b xs).1=some gamma) : gamma∈xs ∧ Passes c b gamma := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    rw [test] at h
    split at h
    · rename_i hp
      have he : x=gamma := Option.some.inj h
      subst gamma
      exact ⟨List.mem_cons_self,hp⟩
    · have ht := ih h
      exact ⟨List.mem_cons_of_mem _ ht.1,ht.2⟩

theorem test_complete (c : Cell) (b : ℝ) (xs : List ℝ) (gamma : ℝ)
    (hm : gamma∈xs) (hp : Passes c b gamma) : ∃ chosen,(test c b xs).1=some chosen := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at hm
  | cons x xs ih =>
    rw [test]
    split
    · exact ⟨x,rfl⟩
    · rename_i hn
      have ht : gamma∈xs := by
        rcases List.mem_cons.mp hm with he | ht
        · subst gamma
          exact False.elim (hn hp)
        · exact ht
      exact ih ht

noncomputable def run (b : ℝ) : List Cell → Option (Cell×ℝ)×ℕ
  | [] => (none,8)
  | c::rest =>
    let tested := test c b (candidates c b)
    match tested.1 with
    | some gamma => (some (c,gamma),tested.2+256)
    | none =>
      let tail := run b rest
      (tail.1,tested.2+256+tail.2)

theorem work (b : ℝ) (cells : List Cell) : (run b cells).2≤512*cells.length+8 := by
  induction cells with
  | nil => exact le_rfl
  | cons c cells ih =>
    have ht := test_work c b (candidates c b)
    have hc := PlayerSpecificCellCandidates.count c b
    rw [run]
    split <;> simp only [List.length_cons]
    · omega
    · change (test c b (candidates c b)).2+256+(run b cells).2≤_
      omega

theorem sound (b : ℝ) (cells : List Cell) (c : Cell) (gamma : ℝ)
    (h : (run b cells).1=some (c,gamma)) :
    c∈cells ∧ gamma∈candidates c b ∧ Passes c b gamma := by
  induction cells with
  | nil => cases h
  | cons first rest ih =>
    rw [run] at h
    split at h
    · rename_i chosen hc
      have he := Option.some.inj h
      have hfirst : first=c := congrArg Prod.fst he
      have hgamma : chosen=gamma := congrArg Prod.snd he
      subst c
      subst gamma
      have ht := test_sound first b (candidates first b) chosen hc
      exact ⟨List.mem_cons_self,ht⟩
    · have ht := ih h
      exact ⟨List.mem_cons_of_mem _ ht.1,ht.2⟩

theorem complete (b : ℝ) (cells : List Cell) (c : Cell) (gamma : ℝ)
    (hm : c∈cells) (hg : gamma∈candidates c b) (hp : Passes c b gamma) :
    ∃ chosen,(run b cells).1=some chosen := by
  induction cells with
  | nil => simp only [List.not_mem_nil] at hm
  | cons first rest ih =>
    rw [run]
    split
    · rename_i chosen _
      exact ⟨(first,chosen),rfl⟩
    · rename_i hn
      have ht : c∈rest := by
        rcases List.mem_cons.mp hm with he | ht
        · subst c
          rcases test_complete first b (candidates first b) gamma hg hp with ⟨chosen,hchosen⟩
          rw [hn] at hchosen
          cases hchosen
        · exact ht
      exact ih ht

end Blotto.PlayerSpecificRootSearch
