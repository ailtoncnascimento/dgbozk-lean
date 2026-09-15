/-
# Supplementary transverse-resonance formalization

This aggregate module contains the transverse-resonance route studied
during the mathematical audit. It is intentionally separate from the
default `DGBOZK` target because the identified cleaned manuscript does
not contain `lem:resonance-transverse`.

The formerly independent longitudinal hypothesis is derived under the
explicit scale relation `N^(alpha/2) <= Cmu * mu`.
-/

import DGBOZK.ResonanceTransverseScaleConclusion

set_option autoImplicit false

namespace DGBOZK.ResonanceTransverseSupplementary

/-- Importable documentation marker for the supplementary target. -/
def documentation : Unit := ()

end DGBOZK.ResonanceTransverseSupplementary
