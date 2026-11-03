import Blotto.GeneralPaperSelectionPointsPrice

/-! Exact seven-branch rational implementation of the native original-
budget selection. Reuse prepared cell points/components and one root value.
All native proxy, modification, endpoint and work fields are preserved.
-/
namespace Blotto.GeneralPaperSelectionPrepared
open GeneralPaperProxySelection
set_option autoImplicit false
set_option maxHeartbeats 4000000

def rootValue (root : Option Farey.Fraction) : ℚ := match root with | none => 0 | some f => f.value

def choose (Q j : ℕ) (hQ : 0<Q) (p : GeneralPaperSelectionPoints.Points)
    (hp : p=GeneralPaperSelectionPoints.prepare Q j) (b : ℚ) (root : Option Farey.Fraction) : Selected :=
  let value := rootValue root
  if b=p.lower then ⟨⟨j,Q,hQ⟩,none,0,24⟩ else
  match root with
  | some f =>
    if b=value then ⟨f,none,0,32⟩ else
    if b<value then ⟨⟨j,Q,hQ⟩,some .rich,value,40⟩
    else ⟨⟨p.upperNum,Q,hQ⟩,some .poor,value,40⟩
  | none =>
    let fraction : Farey.Fraction := ⟨p.midNum,p.midDen,by rw [hp]; change 0<2*Q; omega⟩
    if b=p.middle then ⟨fraction,none,0,40⟩ else
    if p.middle<b then ⟨fraction,some .rich,p.upper,48⟩
    else ⟨fraction,some .poor,p.lower,48⟩

theorem data (Q j : ℕ) (hQ : 0<Q) (p : GeneralPaperSelectionPoints.Points)
    (hp : p=GeneralPaperSelectionPoints.prepare Q j) (b : ℚ) (root : Option Farey.Fraction) :
    choose Q j hQ p hp b root=GeneralPaperProxySelection.select Q j hQ (b:ℝ) root := by
  subst p
  cases root
  all_goals simp only [choose,rootValue,GeneralPaperSelectionPoints.prepare,GeneralPaperProxySelection.select,
    GeneralPaperBucketGeometry.lower,GeneralPaperBucketGeometry.upper,GeneralPaperBucketGeometry.midpoint,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,Rat.cast_inj,Rat.cast_lt]

end Blotto.GeneralPaperSelectionPrepared
