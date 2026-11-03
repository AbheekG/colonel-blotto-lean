import Blotto.GeneralPaperRayMinimum

/-! The exact static row list for one basis ray: two bounds per nonzero
anchor, one adjacent order per nonzero anchor, and every retained whole-row
budget. It has 3d+T entries and contains no high-score tuple enumeration.
-/
namespace Blotto.GeneralPaperStaticRayRows
open RationalOrderCell GeneralPaperAffineConstraintRows
set_option autoImplicit false
set_option maxHeartbeats 2500000

abbrev StaticIndex (T m K : ℕ) := (Variable m K × Bool) ⊕ ((Fin m × Fin (K-1)) ⊕ Fin T)

def embed {T m K : ℕ} {scores : Fin m → Fin K → ℕ} {h : ℕ} : StaticIndex T m K → Index T m K scores h
  | .inl v => .inl v
  | .inr (.inl v) => .inr (.inl v)
  | .inr (.inr i) => .inr (.inr (.inl i))

def variableList (m K : ℕ) : List (Variable m K) :=
  (List.finRange m).flatMap (fun j => (List.finRange (K-1)).map (fun l => (j,l)))

def boxes (T m K : ℕ) : List (StaticIndex T m K) :=
  (variableList m K).flatMap (fun v => [.inl (v,false),.inl (v,true)])

def orders (T m K : ℕ) : List (StaticIndex T m K) := (variableList m K).map (fun v => .inr (.inl v))

def budgets (T m K : ℕ) : List (StaticIndex T m K) := (List.finRange T).map (fun i => .inr (.inr i))

def enumerate (T m K : ℕ) : List (StaticIndex T m K) := boxes T m K++orders T m K++budgets T m K

def row {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (i : StaticIndex T m K) : Row (Variable m K) :=
  constraints labels (fun _ _ => 0) 0 (embed i)

theorem row_eq {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (i : StaticIndex T m K) : row labels i=constraints labels scores h (embed i) := by
  rcases i with v|v|i <;> rfl

theorem variableList_mem (m K : ℕ) (v : Variable m K) : v∈variableList m K :=
  List.mem_flatMap.mpr ⟨v.1,List.mem_finRange _,List.mem_map.mpr ⟨v.2,List.mem_finRange _,rfl⟩⟩

theorem variableList_length (m K : ℕ) : (variableList m K).length=m*(K-1) := by
  simp [variableList,List.length_flatMap]

theorem enumerate_mem {T m K : ℕ} (i : StaticIndex T m K) : i∈enumerate T m K := by
  rcases i with ⟨v,b⟩|v|i
  · apply List.mem_append_left
    apply List.mem_append_left
    unfold boxes
    apply List.mem_flatMap.mpr
    refine ⟨v,variableList_mem m K v,?_⟩
    cases b <;> simp
  · apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨v,variableList_mem m K v,rfl⟩
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩

theorem enumerate_length (T m K : ℕ) : (enumerate T m K).length=3*(m*(K-1))+T := by
  simp [enumerate,boxes,orders,budgets,List.length_flatMap,variableList_length]
  omega

end Blotto.GeneralPaperStaticRayRows
