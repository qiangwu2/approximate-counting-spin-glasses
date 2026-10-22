import Manuscript
import Lean.Util.CollectAxioms

/- Read-only evidence extraction; this file defines no mathematical theorem. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots : Array Name := #[
    ``Manuscript.theorem_1_1_higher_primitive,
    ``Manuscript.theorem_1_1_sk_primitive,
    ``Manuscript.proposition_5_2_higher_primitive,
    ``Manuscript.proposition_5_2_sk_primitive,
    ``Manuscript.HigherOrderCorollaries.relative_counting,
    ``Manuscript.HigherOrderCorollaries.polynomial_confidence,
    ``Manuscript.SKCorollaries.relative_counting,
    ``Manuscript.SKCorollaries.polynomial_confidence]
  for root in roots do
    let mut pending := #[root]
    let mut seen : NameSet := {}
    let mut axioms : Array Name := #[]
    let mut unsafeNames : Array Name := #[]
    let mut missing : Array Name := #[]
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      match env.find? name with
      | none => missing := missing.push name
      | some ci =>
        if ci.isAxiom then axioms := axioms.push name
        match ci with
        | .defnInfo v => if v.safety == .unsafe then unsafeNames := unsafeNames.push name
        | .opaqueInfo v => if v.isUnsafe then unsafeNames := unsafeNames.push name
        | _ => pure ()
        let direct := ci.type.getUsedConstants ++
          ((ci.value? true).map Expr.getUsedConstants).getD #[]
        pending := pending ++ direct
        if ci.isInductive then pending := pending ++ ci.inductiveVal!.ctors.toArray
        let userName := (privateToUserName? name).getD name
        if (`Manuscript).isPrefixOf userName || (`SpinGlass).isPrefixOf userName then
          logInfo m!"LOCAL_DEP {root}; {name}; {direct.toList}"
    let localNames := seen.toArray.filter fun n =>
      let u := (privateToUserName? n).getD n
      (`Manuscript).isPrefixOf u || (`SpinGlass).isPrefixOf u
    logInfo m!"CLOSURE {root}; total={seen.size}; local={localNames.size}; axioms={axioms.toList}; unsafe={unsafeNames.toList}; missing={missing.toList}"
    unless unsafeNames.isEmpty && missing.isEmpty do
      throwError "Unsafe or missing dependencies in {root}"
    let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in closure of {root}"
    let audited ← collectAxioms root
    logInfo m!"CACHED_AXIOMS {root}; {audited.toList}"
    let some ci := env.find? root | throwError "missing endpoint {root}"
    logInfo m!"ENDPOINT_TYPE {root}: {ci.type}"
