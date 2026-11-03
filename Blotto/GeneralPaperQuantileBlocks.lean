import Blotto.GeneralPaperRowSort

/-! Equal-size occurrence blocks. These are row-occurrence counts, not
counts of distinct bid values, so repeated bids and zero anchors are retained.
-/
namespace Blotto.GeneralPaperQuantileBlocks
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Classical

def block {K B : ℕ} (hB : 0<B) (r : Fin (K*B)) : Fin K :=
  ⟨r.val/B,(Nat.div_lt_iff_lt_mul hB).mpr r.isLt⟩

def position {K B : ℕ} (hB : 0<B) (l : Fin K) (b : Fin B) : Fin (K*B) :=
  ⟨l.val*B+b.val,by
    have h := Nat.mul_le_mul_right B (Nat.succ_le_of_lt l.isLt)
    nlinarith only [h,b.isLt]⟩

theorem block_position {K B : ℕ} (hB : 0<B) (l : Fin K) (b : Fin B) :
    block hB (position hB l b)=l := by
  apply Fin.ext
  change (l.val*B+b.val)/B=l.val
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ hB,Nat.div_eq_of_lt b.isLt,Nat.zero_add]

theorem block_card {K B : ℕ} (hB : 0<B) (l : Fin K) :
    (Finset.univ.filter (fun r : Fin (K*B) => block hB r=l)).card=B := by
  calc
    _ = (Finset.univ : Finset (Fin B)).card := by
      symm
      apply Finset.card_bij (fun b _ => position hB l b)
      · intro b _
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,block_position]
      · intro a _ b _ h
        apply Fin.ext
        have he := congrArg (fun r : Fin (K*B) => r.val) h
        change l.val*B+a.val=l.val*B+b.val at he
        omega
      · intro r hr
        have he := congrArg Fin.val (Finset.mem_filter.mp hr).2
        change r.val/B=l.val at he
        refine ⟨⟨r.val%B,Nat.mod_lt _ hB⟩,Finset.mem_univ _,?_⟩
        apply Fin.ext
        have hMod := Nat.mod_add_div r.val B
        change l.val*B+r.val%B=r.val
        rw [he] at hMod
        nlinarith only [hMod]
    _ = B := Finset.card_fin B

theorem permuted_block_card {K B : ℕ} (hB : 0<B) (permutation : Fin (K*B) → Fin (K*B))
    (hInjective : Function.Injective permutation) (hSurjective : Function.Surjective permutation) (l : Fin K) :
    (Finset.univ.filter (fun i => block hB (permutation i)=l)).card=B := by
  calc
    _ = (Finset.univ.filter (fun r : Fin (K*B) => block hB r=l)).card := by
      apply Finset.card_bij (fun i _ => permutation i)
      · intro i hi
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      · intro a _ b _ h
        exact hInjective h
      · intro r hr
        obtain ⟨i,rfl⟩ := hSurjective r
        exact ⟨i,by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hr,rfl⟩
    _ = B := block_card hB l

theorem permutation_filter_card {T : ℕ} (permutation : Fin T → Fin T)
    (hInjective : Function.Injective permutation) (hSurjective : Function.Surjective permutation)
    (P : Fin T → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (permutation i))).card=(Finset.univ.filter P).card := by
  apply Finset.card_bij (fun i _ => permutation i)
  · intro i hi
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
  · intro a _ b _ h
    exact hInjective h
  · intro r hr
    obtain ⟨i,rfl⟩ := hSurjective r
    exact ⟨i,by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hr,rfl⟩

end Blotto.GeneralPaperQuantileBlocks
