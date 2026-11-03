import Blotto.PlayerSpecificSweepIndexed

/-! A single sweep builds the interval records used by root recognition.
Equal adjacent ratios give an empty open interval; they still cost only
constant work per field. Every breakpoint is retained for its separate test.
The records carry four updated sums and two cached endpoint bounds. -/
namespace Blotto.PlayerSpecificCells
open PlayerSpecificCubic PlayerSpecificSweep PlayerSpecificSweepBounds
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Cell where
  state : State ℝ
  lower : ℝ
  upper : Option ℝ
  suffixMax : ℝ

noncomputable def build (s : State ℝ) (lower : ℝ) : List ((ℝ×ℝ)×ℝ) → List Cell×ℕ
  | [] => ([⟨s,lower,none,0⟩],8)
  | (x,m)::xs =>
    let tail := build (move s x.1 x.2) (x.1/x.2) xs
    (⟨s,lower,some (x.1/x.2),m⟩::tail.1,tail.2+40)

theorem count (s : State ℝ) (lower : ℝ) (xs : List ((ℝ×ℝ)×ℝ)) :
    (build s lower xs).1.length=xs.length+1 := by
  induction xs generalizing s lower with
  | nil => rfl
  | cons x xs ih => simp only [build,List.length_cons,ih]

theorem work (s : State ℝ) (lower : ℝ) (xs : List ((ℝ×ℝ)×ℝ)) :
    (build s lower xs).2=40*xs.length+8 := by
  induction xs generalizing s lower with
  | nil => rfl
  | cons x xs ih => simp only [build,List.length_cons,ih]; omega

theorem maximum_map {α : Type*} (v w : α → ℝ) (xs : List α) :
    maximum Prod.fst (xs.map (fun j => (v j,w j)))=maximum v xs ∧
      maximum Prod.snd (xs.map (fun j => (v j,w j)))=maximum w xs := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih => simp only [List.map_cons,maximum,ih.1,ih.2,and_self]

def Fits {n : ℕ} (v w : Fin n → ℝ) (low high : List (Fin n)) (c : Cell) : Prop :=
  FullInvariant c.state (low.map (fun j => (v j,w j))) (high.map (fun j => (v j,w j))) ∧
  c.suffixMax=maximum w high ∧
  (∀ j∈low,v j/w j≤c.lower) ∧
  match high with
  | [] => c.upper=none
  | j::_ => c.upper=some (v j/w j) ∧ ∀ k∈high,v j/w j≤v k/w k

theorem fits_all {n : ℕ} (v w : Fin n → ℝ) (low high : List (Fin n))
    (s : State ℝ) (lower : ℝ) (hp : (low++high).Perm (List.finRange n))
    (hi : FullInvariant s (low.map (fun j => (v j,w j))) (high.map (fun j => (v j,w j))))
    (hl : ∀ j∈low,v j/w j≤lower) (hh : ∀ j∈high,lower≤v j/w j)
    (hs : high.Pairwise (fun j k => v j/w j≤v k/w k)) :
    ∀ c∈(build s lower (suffixes (high.map (fun j => (v j,w j)))).2.1).1,
      ∃ lo ho,(lo++ho).Perm (List.finRange n) ∧ Fits v w lo ho c := by
  induction high generalizing low s lower with
  | nil =>
    intro c hc
    simp only [List.map_nil,suffixes,build,List.mem_singleton] at hc
    subst c
    exact ⟨low,[],hp,hi,rfl,hl,rfl⟩
  | cons j high ih =>
    have horder := List.pairwise_cons.mp hs
    have hi' := move_full s (low.map (fun j => (v j,w j)))
      (high.map (fun j => (v j,w j))) (v j) (w j) hi
    have hmap : (low++[j]).map (fun j => (v j,w j))=
        low.map (fun j => (v j,w j))++[(v j,w j)] := by simp only [List.map_append,List.map_cons,List.map_nil]
    rw [← hmap] at hi'
    have hp' : ((low++[j])++high).Perm (List.finRange n) := by
      simpa only [List.append_assoc,List.singleton_append] using hp
    have hl' : ∀ k∈low++[j],v k/w k≤v j/w j := by
      intro k hk
      rcases List.mem_append.mp hk with hk | hk
      · exact (hl k hk).trans (hh j (by simp only [List.mem_cons_self]))
      · simp only [List.mem_singleton] at hk
        subst k
        exact le_rfl
    have htail := ih (low++[j]) (move s (v j) (w j)) (v j/w j) hp' hi' hl' horder.1 horder.2
    intro c hc
    rw [List.map_cons,suffixes_cons] at hc
    simp only [build,List.mem_cons] at hc
    rcases hc with rfl | hc
    · refine ⟨low,j::high,hp,hi,?_,hl,rfl,?_⟩
      · exact (maximum_map v w (j::high)).2
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact le_rfl
        · exact horder.1 k hk
    · exact htail c hc

def ClosedRange (c : Cell) (gamma : ℝ) : Prop :=
  0<gamma ∧ c.lower≤gamma ∧ ∀ upper∈c.upper,gamma≤upper

/-- Coverage chooses the first next ratio at least the target, so the
target is strictly above the chosen lower endpoint even at a breakpoint. -/
theorem covers (s : State ℝ) (lower gamma : ℝ) (fields : List (ℝ×ℝ))
    (hg : 0<gamma) (hl : lower<gamma) :
    ∃ c∈(build s lower (suffixes fields).2.1).1,ClosedRange c gamma ∧ c.lower<gamma := by
  induction fields generalizing s lower with
  | nil =>
    refine ⟨⟨s,lower,none,0⟩,by simp only [suffixes,build,List.mem_singleton],?_,hl⟩
    exact ⟨hg,hl.le,by simp⟩
  | cons x xs ih =>
    rw [suffixes_cons]
    by_cases hx : gamma≤x.1/x.2
    · refine ⟨⟨s,lower,some (x.1/x.2),maximum Prod.snd (x::xs)⟩,
        List.mem_cons_self,⟨hg,hl.le,?_⟩,hl⟩
      intro upper hu
      have he : x.1/x.2=upper := by simpa only [Option.mem_def,Option.some.injEq] using hu
      rw [← he]
      exact hx
    · rcases ih (move s x.1 x.2) (x.1/x.2) (lt_of_not_ge hx) with ⟨c,hc,hr,hlc⟩
      exact ⟨c,List.mem_cons_of_mem _ hc,hr,hlc⟩

theorem fits_respects {n : ℕ} (v w : Fin n → ℝ) (low high : List (Fin n))
    (hp : (low++high).Perm (List.finRange n)) (c : Cell) (hf : Fits v w low high c)
    (gamma : ℝ) (hr : ClosedRange c gamma) (hw : ∀ j,0<w j) :
    Respects v w (PlayerSpecificSweepIndexed.highMask high) gamma := by
  apply PlayerSpecificSweepIndexed.respects v w low high hp gamma
  · intro j hj
    exact (div_le_iff₀ (hw j)).mp ((hf.2.2.1 j hj).trans hr.2.1)
  · intro j hj
    cases high with
    | nil => simp only [List.not_mem_nil] at hj
    | cons k high =>
      have hgamma := hr.2.2 (v k/w k) (by rw [hf.2.2.2.1]; exact Option.mem_some_self _)
      exact (le_div_iff₀ (hw j)).mp (hgamma.trans (hf.2.2.2.2 j hj))

end Blotto.PlayerSpecificCells
