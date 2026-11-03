import Blotto.GeneralPaperStaticMinimumPrice

/-! The native left-to-right static minimum loop, with actual residual,
positive-slope candidate, earlier-row tie comparison and control prices.
The row-dependent sum preserves sparse family sizes rather than using m
as a uniform multiplier for every row.
-/
namespace Blotto.GeneralPaperStaticMinimumScanPrice
open GeneralPaperRayAffine GeneralPaperRayMinimum GeneralPaperStaticMinimumPrice
set_option autoImplicit false
set_option maxHeartbeats 5000000

def loop {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (evaluate : i → Affine × ℕ) :
    List i → Option (Choice i) → ℕ → Result i
  | [],current,spent => ⟨current,spent+2*W⟩
  | j::rest,current,spent =>
    let a := evaluate j
    let fresh := GeneralPaperStaticMinimumPrice.candidate primitive W j a.1
    let selected := GeneralPaperStaticMinimumPrice.pick primitive W current fresh.1
    loop primitive W evaluate rest selected.1 (spent+a.2+fresh.2+selected.2+16*W)

theorem loop_data {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (evaluate original : i → Affine × ℕ)
    (hData : ∀ j,(evaluate j).1=(original j).1) (rows : List i) (current : Option (Choice i)) (spent oldSpent : ℕ) :
    (loop primitive W evaluate rows current spent).choice=(GeneralPaperRayMinimum.loop original rows current oldSpent).choice := by
  induction rows generalizing current spent oldSpent with
  | nil => rfl
  | cons j rest ih =>
    rw [loop,GeneralPaperRayMinimum.loop]
    have hh := ih (GeneralPaperRayMinimum.pick current (GeneralPaperRayMinimum.candidate j (original j).1))
      (spent+(evaluate j).2+(GeneralPaperStaticMinimumPrice.candidate primitive W j (evaluate j).1).2+
        (GeneralPaperStaticMinimumPrice.pick primitive W current
          (GeneralPaperStaticMinimumPrice.candidate primitive W j (evaluate j).1).1).2+16*W)
      (oldSpent+(original j).2+32)
    simpa only [GeneralPaperStaticMinimumPrice.pick_data,GeneralPaperStaticMinimumPrice.candidate_data,hData] using hh

theorem loop_work {i : Type*} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E A B R : ℕ) (hD : 0<D) (hE : 0<E) (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R)
    (evaluate : i → Affine × ℕ) (rows : List i)
    (hBound : ∀ j∈rows,GeneralPaperRayAffineBound.Bounded D E A B (evaluate j).1)
    (current : Option (Choice i)) (hCurrent : Height R current) (spent : ℕ) :
    (loop primitive W evaluate rows current spent).work≤
      spent+(rows.map (fun j => (evaluate j).2+56*W+6*primitive (1+2*R))).sum+2*W := by
  induction rows generalizing current spent with
  | nil => simp only [loop,List.map_nil,List.sum_nil,Nat.add_zero,le_refl]
  | cons j rest ih =>
    have hFresh := GeneralPaperStaticMinimumPrice.candidate_height primitive W D E A B R hD hE hR j (evaluate j).1 (hBound j List.mem_cons_self)
    have hSelected := GeneralPaperStaticMinimumPrice.pick_height primitive W R current
      (GeneralPaperStaticMinimumPrice.candidate primitive W j (evaluate j).1).1 hCurrent hFresh
    have hCandidate := GeneralPaperStaticMinimumPrice.candidate_work primitive hMono W D E A B R hD hE hR
      j (evaluate j).1 (hBound j List.mem_cons_self)
    have hPick := GeneralPaperStaticMinimumPrice.pick_work primitive hMono W R current
      (GeneralPaperStaticMinimumPrice.candidate primitive W j (evaluate j).1).1 hCurrent hFresh
    have hr := ih (fun k hk => hBound k (List.mem_cons_of_mem _ hk))
      (GeneralPaperStaticMinimumPrice.pick primitive W current (GeneralPaperStaticMinimumPrice.candidate primitive W j (evaluate j).1).1).1
      hSelected (spent+(evaluate j).2+(GeneralPaperStaticMinimumPrice.candidate primitive W j (evaluate j).1).2+
        (GeneralPaperStaticMinimumPrice.pick primitive W current (GeneralPaperStaticMinimumPrice.candidate primitive W j (evaluate j).1).1).2+16*W)
    rw [loop]
    simp only [List.map_cons,List.sum_cons]
    nlinarith only [hr,hCandidate,hPick]

def scan {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (evaluate : i → Affine × ℕ) (rows : List i) : Result i :=
  loop primitive W evaluate rows none 0

theorem data {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (evaluate original : i → Affine × ℕ)
    (hData : ∀ j,(evaluate j).1=(original j).1) (rows : List i) :
    (scan primitive W evaluate rows).choice=(GeneralPaperRayMinimum.scan original rows).choice :=
  loop_data primitive W evaluate original hData rows none 0 0

theorem work {i : Type*} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E A B R : ℕ) (hD : 0<D) (hE : 0<E) (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R)
    (evaluate : i → Affine × ℕ) (rows : List i)
    (hBound : ∀ j∈rows,GeneralPaperRayAffineBound.Bounded D E A B (evaluate j).1) :
    (scan primitive W evaluate rows).work≤(rows.map (fun j => (evaluate j).2+56*W+6*primitive (1+2*R))).sum+2*W := by
  have hh := loop_work primitive hMono W D E A B R hD hE hR evaluate rows hBound none (by intro c hc; cases hc) 0
  simpa only [scan,Nat.zero_add] using hh

end Blotto.GeneralPaperStaticMinimumScanPrice
