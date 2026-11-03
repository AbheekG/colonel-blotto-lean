import Blotto.GeneralPaperSourceStorageRates

/-! Structural composition of checked source rates. Each arithmetic child is
proved first and its three degrees are normalized before its parent is built.
Only opaque native parameter facts use function-property inference. Every
result is an ordinary proof term checked by the kernel. -/
namespace Blotto.GeneralPaperSourceSpaceTactic

open Lean Meta Elab Tactic in
elab "source_space" : tactic => withMainContext do
  let main ← getMainGoal
  let target ← instantiateMVars (← main.getType)
  unless target.isAppOf ``GeneralPaperSourceRateAlgebra.Rated do
    throwError "source_space expects a Rated goal"
  let fn := target.getAppArgs[0]!
  lambdaTelescope fn fun xs body => do
    unless xs.size == 1 do throwError "source_space expects one source input"
    let x := xs[0]!
    let close := fun e => mkLambdaFVars #[x] e
    let leaf := fun e => do
      let f ← close e
      let a ← mkFreshExprMVar (mkConst ``Nat)
      let b ← mkFreshExprMVar (mkConst ``Nat)
      let c ← mkFreshExprMVar (mkConst ``Nat)
      let ty ← mkAppM ``GeneralPaperSourceRateAlgebra.Rated #[f,a,b,c]
      let g ← mkFreshExprMVar ty
      let old ← getGoals
      setGoals [g.mvarId!]
      try
        evalTactic (← `(tactic| first
          | assumption
          | (apply GeneralPaperSourceRateAlgebra.word; fun_prop (config := {maxSteps := 2500}))
          | fun_prop (config := {maxSteps := 2500})))
        unless (← getGoals).isEmpty do throwError "unclosed native storage atom: {e}"
        let some av ← getNatValue? (← whnf (← instantiateMVars a)) | throwError "nonliteral field degree for {e}"
        let some bv ← getNatValue? (← whnf (← instantiateMVars b)) | throwError "nonliteral alphabet degree for {e}"
        let some cv ← getNatValue? (← whnf (← instantiateMVars c)) | throwError "nonliteral accuracy degree for {e}"
        return (av,bv,cv,← instantiateMVars g)
      catch err =>
        throwError "source_space native atom {e}:\n{err.toMessageData}"
      finally
        setGoals old
    let small := fun f => do
      let ty ← mkAppM ``GeneralPaperSourceWordGrowth.Small #[f]
      let g ← mkFreshExprMVar ty
      let old ← getGoals
      setGoals [g.mvarId!]
      try
        evalTactic (← `(tactic| fun_prop (config := {maxSteps := 2500})))
        unless (← getGoals).isEmpty do throwError "unclosed operand word bound: {f}"
        return ← instantiateMVars g
      finally
        setGoals old
    let memo ← IO.mkRef ({} : Std.HashMap Expr (Nat × Nat × Nat × Expr))
    let rec build : Nat → Expr → TacticM (Nat × Nat × Nat × Expr)
      | 0,e => throwError "source storage structural depth exceeded at {e}"
      | fuel+1,e => do
        let e ← instantiateMVars e
        if let some result := (← memo.get)[e]? then return result
        let calculate : TacticM (Nat × Nat × Nat × Expr) := do
          if !e.containsFVar x.fvarId! then
            return (0,0,0,← mkAppM ``GeneralPaperSourceRateAlgebra.constant #[e])
          let name := e.getAppFn.constName?
          let args := e.getAppArgs
          if name == some ``GeneralPaperFastRationalModel.charge && args.size == 3 then
            let w := args[2]!
            let (a,b,c,p) ← build fuel w
            let wf ← close w
            let hw ← small wf
            return (a,b,c,← mkAppM ``GeneralPaperSourceRateAlgebra.charge
              #[args[0]!,args[1]!,wf,mkNatLit a,mkNatLit b,mkNatLit c,p,hw])
          if name == some ``HSub.hSub || name == some ``Nat.sub || name == some ``Min.min then
            let u := args[args.size-2]!
            let v := args.back!
            let (a,b,c,p) ← build fuel u
            let rule := if name == some ``Min.min then
              ``GeneralPaperSourceRateAlgebra.minimum else ``GeneralPaperSourceRateAlgebra.sub
            return (a,b,c,← mkAppM rule #[← close u,← close v,mkNatLit a,mkNatLit b,mkNatLit c,p])
          if name == some ``HAdd.hAdd || name == some ``Nat.add || name == some ``HMul.hMul ||
              name == some ``Nat.mul || name == some ``Max.max then
            let u := args[args.size-2]!
            let v := args.back!
            let (a,b,c,p) ← build fuel u
            let (a',b',c',q) ← build fuel v
            let isMul := name == some ``HMul.hMul || name == some ``Nat.mul
            let rule := if isMul then ``GeneralPaperSourceRateAlgebra.mul else
              if name == some ``Max.max then ``GeneralPaperSourceRateAlgebra.maximum else ``GeneralPaperSourceRateAlgebra.add
            let proof ← mkAppM rule #[← close u,← close v,mkNatLit a,mkNatLit b,mkNatLit c,
              mkNatLit a',mkNatLit b',mkNatLit c',p,q]
            return (if isMul then a+a' else max a a',if isMul then b+b' else max b b',
              if isMul then c+c' else max c c',proof)
          if name == some ``HPow.hPow || name == some ``Nat.pow then
            let exponent := args.back!
            if let some n ← getNatValue? exponent then
              let u := args[args.size-2]!
              let (a,b,c,p) ← build fuel u
              return (a*n,b*n,c*n,← mkAppM ``GeneralPaperSourceRateAlgebra.power
                #[← close u,mkNatLit n,mkNatLit a,mkNatLit b,mkNatLit c,p])
          if name == some ``binaryWordWidth then
            let u := args.back!
            let ax ← mkAppM ``GeneralPaperSourceWordGrowth.alphabet #[x]
            let cx ← mkAppM ``GeneralPaperCodeAlphabet.Alphabet.C #[ax]
            let dx ← mkAppM ``GeneralPaperCodeAlphabet.Alphabet.D #[ax]
            if ← withReducible (isDefEq u cx) then
              return (0,1,0,mkConst ``GeneralPaperSourceRateAlgebra.scale_word)
            if ← withReducible (isDefEq u dx) then
              return (0,1,0,mkConst ``GeneralPaperSourceStorageRates.denominator_word)
            let un := u.getAppFn.constName?
            let ua := u.getAppArgs
            if un == some ``HAdd.hAdd || un == some ``Nat.add || un == some ``HMul.hMul ||
                un == some ``Nat.mul || un == some ``Max.max then
              let v := ua[ua.size-2]!
              let w := ua.back!
              let (a,b,c,p) ← build fuel (← mkAppM ``binaryWordWidth #[v])
              let (a',b',c',q) ← build fuel (← mkAppM ``binaryWordWidth #[w])
              let rule := if un == some ``HMul.hMul || un == some ``Nat.mul then
                ``GeneralPaperSourceRateAlgebra.word_mul else if un == some ``Max.max then
                ``GeneralPaperSourceRateAlgebra.word_maximum else ``GeneralPaperSourceRateAlgebra.word_add
              return (max a a',max b b',max c c',← mkAppM rule
                #[← close v,← close w,mkNatLit a,mkNatLit b,mkNatLit c,mkNatLit a',mkNatLit b',mkNatLit c',p,q])
            if un == some ``HPow.hPow || un == some ``Nat.pow then
              let base := ua[ua.size-2]!
              if (← getNatValue? base) == some 2 then
                let v := ua.back!
                let (a,b,c,p) ← build fuel v
                return (a,b,c,← mkAppM ``GeneralPaperSourceStorageRates.dyadic_word
                  #[← close v,mkNatLit a,mkNatLit b,mkNatLit c,p])
          return ← leaf e
        let result ← calculate
        memo.modify (·.insert e result)
        return result
    let (_,_,_,proof) ← build 4096 body
    unless ← isDefEq target (← inferType proof) do
      throwError "source_space composed degrees do not fit the requested bound"
    main.assign proof
    replaceMainGoal []

end Blotto.GeneralPaperSourceSpaceTactic
