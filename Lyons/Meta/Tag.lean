/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lean

/-!
# The `lyons_tag` attribute

A declaration attribute carrying a string label, written `@[lyons_tag "TAG"]` above a declaration.
The label is stored as a parametric attribute value, so it can be read back off the environment for
any declaration that carries it.
-/

open Lean

namespace Lyons

/-- Attribute syntax: `@[lyons_tag "TAG"]`. The trailing space in the atom is deliberate: without
it the whitespace style linter demands `@[lyons_tag"TAG"]`. -/
syntax (name := lyonsTag) "lyons_tag " str : attr

initialize lyonsTagAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `lyonsTag
    descr := "entity tag realized by this declaration"
    getParam := fun _ stx => match stx with
      | `(attr| lyons_tag $s:str) => return s.getString
      | _ => throwError "invalid `lyons_tag` attribute: expected a string literal"
  }

end Lyons
