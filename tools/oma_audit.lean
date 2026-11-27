-- Appended by tools/check.sh after a submission that answers a value question (data/placeholders.json).
-- Same report as `#print axioms`, except that the value of the listed placeholders (defined as `sorry` upstream)
-- is not looked at; their type is. Any other sorry, axiom or use of the upstream theorem still shows up.
open Lean Elab Command in
/-- Axioms a constant depends on, like `#print axioms`, except that the value of each constant after `skipping`
(a problem's answer placeholder, defined as `sorry` upstream) is not looked at; its type still is. -/
private partial def omaCollect (skip : NameSet) (c : Name) : StateT (NameSet × Array Name) CoreM Unit := do
  if (← get).1.contains c then return
  modify fun (v, a) => (v.insert c, a)
  let env ← getEnv
  let go (e : Expr) : StateT (NameSet × Array Name) CoreM Unit := e.getUsedConstants.forM (omaCollect skip)
  match env.find? c with
  | some (.axiomInfo _) => modify fun (v, a) => (v, a.push c)
  | some (.defnInfo d) => go d.type; unless skip.contains c do go d.value
  | some (.thmInfo t) => go t.type; unless skip.contains c do go t.value
  | some (.opaqueInfo o) => go o.type; unless skip.contains c do go o.value
  | some (.quotInfo _) => pure ()
  | some (.ctorInfo ct) => go ct.type
  | some (.recInfo r) => go r.type
  | some (.inductInfo i) => go i.type; i.ctors.forM (omaCollect skip)
  | none => pure ()

open Lean Elab Command in
elab "#oma_axioms " c:ident " skipping " ss:ident* : command => do
  let cn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
  let mut skip : NameSet := {}
  for s in ss do skip := skip.insert (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s)
  let ((), (_, axs)) ← liftCoreM <| (omaCollect skip cn).run ({}, #[])
  let axs := axs.qsort Name.lt
  if axs.isEmpty then logInfo m!"'{cn}' does not depend on any axioms"
  else logInfo m!"'{cn}' depends on axioms: {axs.toList}"
