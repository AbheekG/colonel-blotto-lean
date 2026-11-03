import Blotto.GeneralPaperBalancedProfitDP

/-! Every retained state decodes through its actual predecessor indices to
one complete tuple with exactly the stored resource tag and at least its
represented profit. This is the soundness direction, not yet the relative
dominance/optimizer approximation theorem.
-/
namespace Blotto.GeneralPaperBalancedProfitSound
open GeneralPaperProfitGridPoints GeneralPaperProfitGridPrepare GeneralPaperResourceMinimum GeneralPaperBalancedProfitDP
set_option autoImplicit false
set_option maxHeartbeats 3500000

def Realizes {K : ℕ} : {h : ℕ} → Tree K h → List (Fin K) → ℚ → ℕ → Prop
  | _,.leaf field,labels,cost,profit => ∃ a, labels=[a] ∧ cost=(field.read a).2 ∧ profit=(field.read a).1
  | _,.node left right,labels,cost,profit =>
    ∃ ll lc lp rr rc rp, Realizes left ll lc lp ∧ Realizes right rr rc rp ∧
      labels=ll++rr ∧ cost=lc+rc ∧ profit=lp+rp

theorem realizes_length {K h : ℕ} (tree : Tree K h) (labels : List (Fin K)) (cost : ℚ) (profit : ℕ)
    (hRealizes : Realizes tree labels cost profit) : labels.length=2^h := by
  induction tree generalizing labels cost profit with
  | leaf field =>
    obtain ⟨a,rfl,_,_⟩ := hRealizes
    rfl
  | @node h left right ihl ihr =>
    obtain ⟨ll,lc,lp,rr,rc,rp,hl,hr,rfl,_,_⟩ := hRealizes
    rw [List.length_append,ihl ll lc lp hl,ihr rr rc rp hr,pow_succ]
    omega

theorem state_sound {K h q w B : ℕ} (tree : Tree K h) (label : Fin (prepare q w B).size)
    (chosen : Selection (Trace K (prepare q w B).size h))
    (hRead : (run (prepare q w B) tree).table.read label=some chosen) :
    ∃ labels profit, decode (run (prepare q w B) tree) label=some labels ∧
      Realizes tree labels chosen.cost profit ∧ q*(prepare q w B).numerators.read label≤profit*denominator w B := by
  induction tree generalizing label with
  | leaf field =>
    change (leafTable (prepare q w B) field).read label=some chosen at hRead
    obtain ⟨a,hChosen,hLabel⟩ := leaf_description (prepare q w B) field label chosen hRead
    subst chosen
    refine ⟨[a],(field.read a).1,?_,⟨a,rfl,rfl,rfl⟩,?_⟩
    · change ((leafTable (prepare q w B) field).read label).map (fun x => [x.predecessor])=some [a]
      rw [hRead]
      rfl
    · rw [←hLabel]
      exact GeneralPaperProfitGridRound.leaf_down q w B (field.read a).1
  | @node h left right ihl ihr =>
    change (mergeTable (prepare q w B) (run (prepare q w B) left).table (run (prepare q w B) right).table).read label=some chosen at hRead
    obtain ⟨i,j,a,b,hl,hr,hChosen,hLabel⟩ := merge_description (prepare q w B)
      (run (prepare q w B) left).table (run (prepare q w B) right).table label chosen hRead
    obtain ⟨ll,lp,hdl,hlr,hlp⟩ := ihl i a hl
    obtain ⟨rr,rp,hdr,hrr,hrp⟩ := ihr j b hr
    subst chosen
    refine ⟨ll++rr,lp+rp,?_,⟨ll,a.cost,lp,rr,b.cost,rp,hlr,hrr,rfl,rfl,rfl⟩,?_⟩
    · change decode (.node (run (prepare q w B) left) (run (prepare q w B) right)
        (mergeTable (prepare q w B) (run (prepare q w B) left).table (run (prepare q w B) right).table)) label=some (ll++rr)
      rw [decode,hRead]
      change ((decode (run (prepare q w B) left) i).bind (fun ls =>
        (decode (run (prepare q w B) right) j).bind (fun rs => some (ls++rs))))=some (ll++rr)
      simp only [hdl,hdr,Option.bind_some]
    · have hd := GeneralPaperProfitGridRound.merge_down q w B
        ((prepare q w B).numerators.read i+(prepare q w B).numerators.read j)
      rw [hLabel] at hd
      have hm := Nat.mul_le_mul_left q hd
      nlinarith only [hm,hlp,hrp]

theorem decoded_length {K h q w B : ℕ} (tree : Tree K h) (label : Fin (prepare q w B).size)
    (chosen : Selection (Trace K (prepare q w B).size h))
    (hRead : (run (prepare q w B) tree).table.read label=some chosen) :
    ∃ labels, decode (run (prepare q w B) tree) label=some labels ∧ labels.length=2^h := by
  obtain ⟨labels,profit,hd,hr,_⟩ := state_sound tree label chosen hRead
  exact ⟨labels,hd,realizes_length tree labels chosen.cost profit hr⟩

end Blotto.GeneralPaperBalancedProfitSound
