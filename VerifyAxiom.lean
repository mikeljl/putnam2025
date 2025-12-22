import Putnam2025

open Lean Meta in
macro "#check_axioms" thm:ident : command => do
  let thmName := thm.getId
  `(command|
    #eval do
      let allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
      let axioms ← collectAxioms $(quote thmName)
      let forbidden := axioms.filter (· ∉ allowedAxioms)
      let thmNameStr := $(quote thmName).toString
      if forbidden.isEmpty then
        logInfo s!"✓ Theorem '{thmNameStr}' uses only allowed axioms: {axioms.toList}"
      else
        throwError s!"✗ Theorem '{thmNameStr}' uses forbidden axioms: {forbidden.toList}"
  )

#check_axioms Putnam2025A6.putnam_2025_a6
#check_axioms Putnam2025B3.putnam_2025_b3
#check_axioms Putnam2025B6.putnam_2025_b6
#check_axioms Putnam2025B2.putnam_2025_b2
#check_axioms Putnam2025A1.putnam_2025_a1
#check_axioms Putnam2025B4.putnam_2025_b4
#check_axioms Putnam2025A3.putnam_2025_a3
#check_axioms Putnam2025A4.putnam_2025_a4
#check_axioms Putnam2025A2.putnam_2025_a2
#check_axioms Putnam2025B1.putnam_2025_b1
#check_axioms Putnam2025B5.putnam_2025_b5
