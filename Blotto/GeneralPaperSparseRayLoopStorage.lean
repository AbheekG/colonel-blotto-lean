import Blotto.GeneralPaperSparseRayStepStorage

/-! Native sparse-loop frames and returned accumulators. Every structural
frame has explicit scalar/primitive reservations. A proof-only total work
cap bounds encoded counters; the final zero-start theorem derives it. -/
namespace Blotto.GeneralPaperSparseRayLoopStorage
open RationalOrderCell GeneralPaperRayRationalBound GeneralPaperRaySparseEvaluation
open GeneralPaperEncodedScalarStorage GeneralPaperSparseRayStepStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem spent_le {v : Type*} (model : RationalCostModel) (W : ℕ) (x w : v → ℚ) (terms : List (v×ℤ)) (a b : ℚ) (spent : ℕ) :
    spent≤(GeneralPaperSparseRayPrice.loop model.rat W x w terms a b spent).work := by
  induction terms generalizing a b spent with
  | nil => simp only [GeneralPaperSparseRayPrice.loop]; omega
  | cons term rest ih =>
    exact (Nat.le_add_right spent _).trans (ih _ _ _)

theorem returned {v : Type*} (model : RationalCostModel) (W D E X V A B : ℕ) (x w : v → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (terms : List (v×ℤ))
    (hc : ∀ t∈terms,t.2.natAbs≤1) (a b : ℚ) (spent : ℕ) (ha : Bounded D A a) (hb : Bounded E B b) :
    Bounded D (A+terms.length*X) (GeneralPaperSparseRayPrice.loop model.rat W x w terms a b spent).point ∧
      Bounded E (B+terms.length*V) (GeneralPaperSparseRayPrice.loop model.rat W x w terms a b spent).velocity := by
  have hd := GeneralPaperSparseRayPrice.loop_data model.rat W x w terms a b spent
  rw [hd.1,hd.2]
  exact ⟨ha.add (Bounded.list_sum D X _ terms (fun t ht => GeneralPaperRaySparseSize.term D X x hx t (hc t ht))),
    hb.add (Bounded.list_sum E V _ terms (fun t ht => GeneralPaperRaySparseSize.term E V w hw t (hc t ht)))⟩

def stepPrice (model : RationalCostModel) (W R : ℕ) : ℕ := 48*W+9*model.rat (1+2*R)
def metadataCap (model : RationalCostModel) (W R N C : ℕ) : ℕ := N+1+2*C+stepPrice model W R+2*W

def frame {v : Type*} (model : RationalCostModel) (W : ℕ) (x w : v → ℚ) (terms : List (v×ℤ)) (a b : ℚ) (spent : ℕ) : ℕ :=
  let result := GeneralPaperSparseRayPrice.loop model.rat W x w terms a b spent
  rationalWordWidth a+rationalWordWidth b+rationalWordWidth result.point+rationalWordWidth result.velocity+
    match terms with
    | [] => fields W [0,spent,result.work,2*W,spent+2*W]+128*W
    | term::_ =>
      let current := GeneralPaperSparseRayPrice.step model.rat W x w term a b
      GeneralPaperSparseRayStepStorage.window model W x w term a b+
        fields W [terms.length,spent,result.work,current.work,spent+current.work]+128*W

def frameProfile (model : RationalCostModel) (W R N C : ℕ) : ℕ :=
  4*(1+2*R)+GeneralPaperSparseRayStepStorage.profile model W R+5*(natBits (metadataCap model W R N C)+W)+160*W

theorem frame_bound {v : Type*} (model : RationalCostModel) (W D E X V U Z R N C A B : ℕ)
    (hD : 0<D) (hE : 0<E) (hU : 1≤U) (hX : X≤U) (hV : V≤Z)
    (hR : GeneralPaperRayAffineBound.rootWidth D E U Z≤R) (x w : v → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (terms : List (v×ℤ)) (hLen : terms.length≤N)
    (hc : ∀ t∈terms,t.2.natAbs≤1) (a b : ℚ) (spent : ℕ) (ha : Bounded D A a) (hb : Bounded E B b)
    (hA : A+terms.length*X≤U) (hB : B+terms.length*V≤Z)
    (hC : (GeneralPaperSparseRayPrice.loop model.rat W x w terms a b spent).work≤C) :
    frame model W x w terms a b spent≤frameProfile model W R N C := by
  let result := GeneralPaperSparseRayPrice.loop model.rat W x w terms a b spent
  have hReturned := returned model W D E X V A B x w hx hw terms hc a b spent ha hb
  have h1 := rationalWordWidth_of_height (point_height hD hR ha (by omega))
  have h2 := rationalWordWidth_of_height (velocity_height hE hR hb (by omega))
  have h3 : rationalWordWidth result.point≤1+2*R := rationalWordWidth_of_height (point_height hD hR hReturned.1 hA)
  have h4 : rationalWordWidth result.velocity≤1+2*R := rationalWordWidth_of_height (velocity_height hE hR hReturned.2 hB)
  have hSpent := (spent_le model W x w terms a b spent).trans hC
  change result.work≤C at hC
  cases terms with
  | nil =>
    have hFields := fields_bound W (natBits (metadataCap model W R N C)) [0,spent,result.work,2*W,spent+2*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (metadataCap model W R N C)+W)+32*W at hFields
    change rationalWordWidth a+rationalWordWidth b+rationalWordWidth result.point+rationalWordWidth result.velocity+
      (GeneralPaperEncodedScalarStorage.fields W [0,spent,result.work,2*W,spent+2*W]+128*W)≤_
    unfold frameProfile
    omega
  | cons term rest =>
    let current := GeneralPaperSparseRayPrice.step model.rat W x w term a b
    have hAX : A+X≤U := by simp only [List.length_cons] at hA; nlinarith
    have hBV : B+V≤Z := by simp only [List.length_cons] at hB; nlinarith
    have hStep := GeneralPaperSparseRayStepStorage.bounded model W D E X V U Z R A B hD hE hU hX hV hR x w hx hw term
      (hc term List.mem_cons_self) a b ha hb hAX hBV
    have hWork := GeneralPaperSparseRayPrice.step_work model.rat model.monotone W D E X V U Z R A B hD hE hU hX hV hR x w hx hw term
      (hc term List.mem_cons_self) a b ha hb hAX hBV
    change current.work≤stepPrice model W R at hWork
    have hFields := fields_bound W (natBits (metadataCap model W R N C)) [(term::rest).length,spent,result.work,current.work,spent+current.work] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (metadataCap model W R N C)+W)+32*W at hFields
    change rationalWordWidth a+rationalWordWidth b+rationalWordWidth result.point+rationalWordWidth result.velocity+
      (GeneralPaperSparseRayStepStorage.window model W x w term a b+
        GeneralPaperEncodedScalarStorage.fields W [(term::rest).length,spent,result.work,current.work,spent+current.work]+128*W)≤_
    unfold frameProfile
    omega

def frames {v : Type*} (model : RationalCostModel) (W : ℕ) (x w : v → ℚ) : List (v×ℤ) → ℚ → ℚ → ℕ → ℕ
  | [],a,b,spent => frame model W x w [] a b spent
  | term::rest,a,b,spent =>
    let current := GeneralPaperSparseRayPrice.step model.rat W x w term a b
    frame model W x w (term::rest) a b spent+frames model W x w rest current.point current.velocity (spent+current.work)

theorem frames_bound {v : Type*} (model : RationalCostModel) (W D E X V U Z R N C A B : ℕ)
    (hD : 0<D) (hE : 0<E) (hU : 1≤U) (hX : X≤U) (hV : V≤Z)
    (hR : GeneralPaperRayAffineBound.rootWidth D E U Z≤R) (x w : v → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (terms : List (v×ℤ)) (hLen : terms.length≤N)
    (hc : ∀ t∈terms,t.2.natAbs≤1) (a b : ℚ) (spent : ℕ) (ha : Bounded D A a) (hb : Bounded E B b)
    (hA : A+terms.length*X≤U) (hB : B+terms.length*V≤Z)
    (hC : (GeneralPaperSparseRayPrice.loop model.rat W x w terms a b spent).work≤C) :
    frames model W x w terms a b spent≤(terms.length+1)*frameProfile model W R N C := by
  induction terms generalizing A B a b spent with
  | nil => simpa only [frames,List.length_nil,Nat.zero_add,Nat.one_mul] using
      frame_bound model W D E X V U Z R N C A B hD hE hU hX hV hR x w hx hw [] hLen hc a b spent ha hb hA hB hC
  | cons term rest ih =>
    have hFrame := frame_bound model W D E X V U Z R N C A B hD hE hU hX hV hR x w hx hw (term::rest) hLen hc a b spent ha hb hA hB hC
    have hNextA := ha.add (GeneralPaperRaySparseSize.term D X x hx term (hc term List.mem_cons_self))
    have hNextB := hb.add (GeneralPaperRaySparseSize.term E V w hw term (hc term List.mem_cons_self))
    have hRest := ih (A+X) (B+V) (by simp only [List.length_cons] at hLen; omega) (fun t ht => hc t (List.mem_cons_of_mem _ ht))
      _ _ _ hNextA hNextB
      (by simp only [List.length_cons] at hA; nlinarith) (by simp only [List.length_cons] at hB; nlinarith) hC
    exact (Nat.add_le_add hFrame hRest).trans_eq (by simp only [List.length_cons]; ring)

def zeroPrice (model : RationalCostModel) (W R N : ℕ) : ℕ := N*stepPrice model W R+2*W

theorem zero_start {v : Type*} (model : RationalCostModel) (W D E X V U Z R N : ℕ)
    (hD : 0<D) (hE : 0<E) (hU : 1≤U) (hX : X≤U) (hV : V≤Z)
    (hR : GeneralPaperRayAffineBound.rootWidth D E U Z≤R) (x w : v → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (terms : List (v×ℤ)) (hLen : terms.length≤N)
    (hc : ∀ t∈terms,t.2.natAbs≤1) (hA : terms.length*X≤U) (hB : terms.length*V≤Z) :
    frames model W x w terms 0 0 0≤(N+1)*frameProfile model W R N (zeroPrice model W R N) := by
  have hWork := GeneralPaperSparseRayPrice.loop_work model.rat model.monotone W D E X V U Z R hD hE hU hX hV hR x w hx hw terms hc
    0 0 0 0 0 (Bounded.zero D) (Bounded.zero E) (by simpa only [Nat.zero_add] using hA) (by simpa only [Nat.zero_add] using hB)
  have hC : (GeneralPaperSparseRayPrice.loop model.rat W x w terms 0 0 0).work≤zeroPrice model W R N := by
    simp only [Nat.zero_add] at hWork
    exact hWork.trans (by unfold zeroPrice stepPrice; gcongr)
  exact (frames_bound model W D E X V U Z R N _ 0 0 hD hE hU hX hV hR x w hx hw terms hLen hc 0 0 0
    (Bounded.zero D) (Bounded.zero E) (by simpa only [Nat.zero_add] using hA) (by simpa only [Nat.zero_add] using hB) hC).trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right hLen 1))

end Blotto.GeneralPaperSparseRayLoopStorage
