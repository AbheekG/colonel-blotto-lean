import Blotto.GeneralPaperHighSearchWork

/-! Operand-priced sparse ray evaluation. Both accumulators retain their
original common lattices at every prefix; no denominator-depth factor is
introduced by the actual tail-recursive sequence of additions.
-/
namespace Blotto.GeneralPaperSparseRayPrice
open GeneralPaperRayRationalBound GeneralPaperRaySparseEvaluation GeneralPaperRationalPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 6000000

def step {v : Type*} (primitive : ℕ → ℕ) (W : ℕ) (x w : v → ℚ) (term : v × ℤ) (a b : ℚ) : Sums :=
  let c := (term.2:ℚ)
  let point := c*x term.1
  let velocity := c*w term.1
  ⟨a+point,b+velocity,48*W+primitive (rationalWordWidth c)+
    binary primitive (·*·) c (x term.1)+binary primitive (·*·) c (w term.1)+
    binary primitive (·+·) a point+binary primitive (·+·) b velocity⟩

theorem step_work {v : Type*} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E X V U Z R A B : ℕ) (hD : 0<D) (hE : 0<E) (hU : 1≤U) (hX : X≤U) (hV : V≤Z)
    (hR : GeneralPaperRayAffineBound.rootWidth D E U Z≤R) (x w : v → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j))
    (term : v × ℤ) (hc : term.2.natAbs≤1) (a b : ℚ) (ha : Bounded D A a) (hb : Bounded E B b)
    (hA : A+X≤U) (hB : B+V≤Z) :
    (step primitive W x w term a b).work≤48*W+9*primitive (1+2*R) := by
  have hPoint (q : ℚ) {M : ℕ} (hq : Bounded D M q) (hM : M≤U) : rationalWordWidth q≤1+2*R := by
    apply rationalWordWidth_of_height
    apply ((hq.mono hM).height hD).mono
    unfold GeneralPaperRayAffineBound.rootWidth at hR
    omega
  have hVelocity (q : ℚ) {M : ℕ} (hq : Bounded E M q) (hM : M≤Z) : rationalWordWidth q≤1+2*R := by
    apply rationalWordWidth_of_height
    apply ((hq.mono hM).height hE).mono
    unfold GeneralPaperRayAffineBound.rootWidth at hR
    omega
  have hC := (Bounded.intCast D term.2).mono (hc.trans hU)
  have hCW := hPoint _ hC le_rfl
  have hPX := GeneralPaperRaySparseSize.term D X x hx term hc
  have hPV := GeneralPaperRaySparseSize.term E V w hw term hc
  have hNextA := ha.add hPX
  have hNextB := hb.add hPV
  have hCast := hMono hCW
  have hmX := binary_le primitive hMono (·*·) (term.2:ℚ) (x term.1) (1+2*R)
    hCW (hPoint _ (hx _) hX) (hPoint _ hPX hX)
  have hmV := binary_le primitive hMono (·*·) (term.2:ℚ) (w term.1) (1+2*R)
    hCW (hVelocity _ (hw _) hV) (hVelocity _ hPV hV)
  have ha' := binary_le primitive hMono (·+·) a ((term.2:ℚ)*x term.1) (1+2*R)
    (hPoint _ ha (by omega)) (hPoint _ hPX hX) (hPoint _ hNextA hA)
  have hb' := binary_le primitive hMono (·+·) b ((term.2:ℚ)*w term.1) (1+2*R)
    (hVelocity _ hb (by omega)) (hVelocity _ hPV hV) (hVelocity _ hNextB hB)
  change 48*W+primitive (rationalWordWidth (term.2:ℚ))+
    binary primitive (·*·) (term.2:ℚ) (x term.1)+binary primitive (·*·) (term.2:ℚ) (w term.1)+
    binary primitive (·+·) a ((term.2:ℚ)*x term.1)+binary primitive (·+·) b ((term.2:ℚ)*w term.1)≤_
  omega

def loop {v : Type*} (primitive : ℕ → ℕ) (W : ℕ) (x w : v → ℚ) : List (v × ℤ) → ℚ → ℚ → ℕ → Sums
  | [],a,b,spent => ⟨a,b,spent+2*W⟩
  | term::rest,a,b,spent =>
    let current := step primitive W x w term a b
    loop primitive W x w rest current.point current.velocity (spent+current.work)

theorem loop_data {v : Type*} (primitive : ℕ → ℕ) (W : ℕ) (x w : v → ℚ) (terms : List (v × ℤ))
    (a b : ℚ) (spent : ℕ) :
    (loop primitive W x w terms a b spent).point=a+(terms.map (fun t => (t.2:ℚ)*x t.1)).sum ∧
    (loop primitive W x w terms a b spent).velocity=b+(terms.map (fun t => (t.2:ℚ)*w t.1)).sum := by
  induction terms generalizing a b spent with
  | nil => simp only [loop,List.map_nil,List.sum_nil,add_zero,and_self]
  | cons term rest ih =>
    rw [loop]
    have hh := ih (a+(term.2:ℚ)*x term.1) (b+(term.2:ℚ)*w term.1)
      (spent+(step primitive W x w term a b).work)
    simp only [step,List.map_cons,List.sum_cons] at hh ⊢
    exact ⟨by rw [hh.1]; ring,by rw [hh.2]; ring⟩

theorem loop_work {v : Type*} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E X V U Z R : ℕ) (hD : 0<D) (hE : 0<E) (hU : 1≤U) (hX : X≤U) (hV : V≤Z)
    (hR : GeneralPaperRayAffineBound.rootWidth D E U Z≤R) (x w : v → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (terms : List (v × ℤ))
    (hc : ∀ t∈terms,t.2.natAbs≤1) (A B : ℕ) (a b : ℚ) (spent : ℕ)
    (ha : Bounded D A a) (hb : Bounded E B b) (hA : A+terms.length*X≤U) (hB : B+terms.length*V≤Z) :
    (loop primitive W x w terms a b spent).work≤spent+terms.length*(48*W+9*primitive (1+2*R))+2*W := by
  induction terms generalizing A B a b spent with
  | nil => simp only [loop,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons term rest ih =>
    have hCoef := hc term List.mem_cons_self
    have hPX := GeneralPaperRaySparseSize.term D X x hx term hCoef
    have hPV := GeneralPaperRaySparseSize.term E V w hw term hCoef
    have hNextA := ha.add hPX
    have hNextB := hb.add hPV
    have hStep := step_work primitive hMono W D E X V U Z R A B hD hE hU hX hV hR
      x w hx hw term hCoef a b ha hb (by simp only [List.length_cons] at hA; nlinarith)
      (by simp only [List.length_cons] at hB; nlinarith)
    have hr := ih (fun t ht => hc t (List.mem_cons_of_mem _ ht)) (A+X) (B+V)
      (a+(term.2:ℚ)*x term.1) (b+(term.2:ℚ)*w term.1) (spent+(step primitive W x w term a b).work)
      hNextA hNextB (by simp only [List.length_cons] at hA; nlinarith)
      (by simp only [List.length_cons] at hB; nlinarith)
    rw [loop]
    change (loop primitive W x w rest (a+(term.2:ℚ)*x term.1) (b+(term.2:ℚ)*w term.1)
      (spent+(step primitive W x w term a b).work)).work≤_
    simp only [List.length_cons]
    nlinarith only [hr,hStep]

end Blotto.GeneralPaperSparseRayPrice
