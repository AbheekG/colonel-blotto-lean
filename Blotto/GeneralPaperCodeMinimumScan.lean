import Blotto.GeneralPaperCodeDecodeWork

/-! A fixed-list native code scan with exact minimum-code selection and
payload retention. Range checks and actual decoder calls are executed. This
will inspect only five codes, not the code alphabet or the Farey universe.
-/
namespace Blotto.GeneralPaperCodeMinimumScan
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode
open GeneralPaperOrderedMinimum (Best)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 2048

abbrev Entry := GeneralPaperOrderedMinimum.Selection ℕ Choice

structure Result where
  selected : Option Entry
  work : ℕ

def Possible (a : Alphabet) (response : Bool) (lo hi : ℕ) (entry : Entry) : Prop :=
  lo≤entry.cost ∧ entry.cost≤hi ∧ (decode a response entry.cost).choice=some entry.predecessor

def evaluate (a : Alphabet) (response : Bool) (lo hi code : ℕ) : Result :=
  if lo≤code ∧ code≤hi then
    let found := decode a response code
    ⟨found.choice.map (fun choice => ⟨code,choice⟩),found.work+24⟩
  else ⟨none,16⟩

def scan (a : Alphabet) (response : Bool) (lo hi : ℕ) : List ℕ → Result
  | [] => ⟨none,8⟩
  | code::rest =>
    let tested := evaluate a response lo hi code
    let later := scan a response lo hi rest
    ⟨GeneralPaperOrderedMinimum.pick tested.selected later.selected,tested.work+later.work+24⟩

def Listed (a : Alphabet) (response : Bool) (lo hi : ℕ) (codes : List ℕ) (entry : Entry) : Prop :=
  ∃ code∈codes, (evaluate a response lo hi code).selected=some entry

theorem evaluate_iff (a : Alphabet) (response : Bool) (lo hi code : ℕ) (entry : Entry) :
    (evaluate a response lo hi code).selected=some entry ↔ entry.cost=code ∧ Possible a response lo hi entry := by
  dsimp only [evaluate]
  split
  · rename_i hRange
    constructor
    · intro hSome
      cases hd : (decode a response code).choice with
      | none => simp only [hd,Option.map_none,reduceCtorEq] at hSome
      | some choice =>
        have he : (⟨code,choice⟩:Entry)=entry := by simpa only [hd,Option.map_some,Option.some.injEq] using hSome
        subst entry
        exact ⟨rfl,hRange.1,hRange.2,hd⟩
    · rintro ⟨hCost,hPossible⟩
      have hd : (decode a response code).choice=some entry.predecessor := by rw [←hCost]; exact hPossible.2.2
      rw [hd,Option.map_some]
      congr 1
      cases entry with
      | mk cost choice =>
        dsimp only at hCost ⊢
        subst cost
        rfl
  · rename_i hRange
    constructor
    · intro hSome
      cases hSome
    · rintro ⟨hCost,hLo,hHi,_⟩
      exact (hRange (by rw [←hCost]; exact ⟨hLo,hHi⟩)).elim

theorem singleton_best (value : Option Entry) : Best (fun entry => value=some entry) value := by
  cases value with
  | none => intro entry he; cases he
  | some chosen =>
    exact ⟨rfl,fun entry he => by have hx := Option.some.inj he; subst entry; exact le_rfl⟩

theorem best_congr (P Q : Entry → Prop) (value : Option Entry) (h : ∀ entry, P entry↔Q entry) (hBest : Best P value) :
    Best Q value := by
  cases value with
  | none => exact fun entry he => hBest entry ((h entry).mpr he)
  | some chosen => exact ⟨(h chosen).mp hBest.1,fun entry he => hBest.2 entry ((h entry).mpr he)⟩

theorem scan_best (a : Alphabet) (response : Bool) (lo hi : ℕ) (codes : List ℕ) :
    Best (Listed a response lo hi codes) (scan a response lo hi codes).selected := by
  induction codes with
  | nil => simp [scan,Listed,Best]
  | cons code rest ih =>
    exact best_congr _ _ _
      (by intro entry; simp only [Listed,List.mem_cons,or_and_right,exists_or,exists_eq_left])
      (GeneralPaperOrderedMinimum.pick_best _ _ _ _ (singleton_best (evaluate a response lo hi code).selected) ih)

theorem listed_possible (a : Alphabet) (response : Bool) (lo hi : ℕ) (codes : List ℕ) (entry : Entry)
    (h : Listed a response lo hi codes entry) : Possible a response lo hi entry := by
  obtain ⟨code,_,he⟩ := h
  exact ((evaluate_iff a response lo hi code entry).mp he).2

theorem evaluate_work (a : Alphabet) (response : Bool) (lo hi code : ℕ) :
    (evaluate a response lo hi code).work≤184*a.lambda+500 := by
  dsimp only [evaluate]
  split
  · have he := GeneralPaperCodeDecodeWork.decode_work a response code
    dsimp only
    omega
  · dsimp only
    omega

theorem scan_work (a : Alphabet) (response : Bool) (lo hi : ℕ) (codes : List ℕ) :
    (scan a response lo hi codes).work≤codes.length*(184*a.lambda+524)+8 := by
  induction codes with
  | nil => simp only [scan,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons code rest ih =>
    have he := evaluate_work a response lo hi code
    change (evaluate a response lo hi code).work+(scan a response lo hi rest).work+24≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end Blotto.GeneralPaperCodeMinimumScan
