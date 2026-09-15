/-
# DGBOZK — targeted Lean 4 checks for the cleaned manuscript

Companion formalization for

  A. C. Nascimento, *Local well-posedness for two-sign dispersion-generalized
  Benjamin–Ono–Zakharov–Kuznetsov equations*.

See `README.md` for the scope of the claim and `DGBOZK/BlackBoxes.lean` for the
trust boundary.  This default target deliberately excludes the legacy
normal-form resonance module and the unfinished Fourier-foundation modules.
-/
import DGBOZK.BlackBoxes
import DGBOZK.Exponents
import DGBOZK.Phase
import DGBOZK.Fold
import DGBOZK.Velocity
import DGBOZK.Cancellation
import DGBOZK.TrilinearCancellationCore
import DGBOZK.TrilinearDifferentiationCore
import DGBOZK.PositiveCommutatorCore
import DGBOZK.FocusingThreshold
import DGBOZK.EnergyEnvelope
import DGBOZK.FrequencyEnvelope
import DGBOZK.FrequencyEnvelopeMaximum
import DGBOZK.FrequencyEnvelopeLimit
import DGBOZK.Bootstrap

set_option autoImplicit false
