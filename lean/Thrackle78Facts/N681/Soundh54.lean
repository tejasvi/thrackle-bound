import Thrackle78Facts.N681.Coverh54
import Thrackle78Facts.N681.Soundh12

open Thrackle78 Thrackle78Core Thrackle78.Checker

/-- The logical filter of `h54` is sound: it contains the image of the sound filter `h12` under the symmetry. -/
theorem T78Native.N681.sound_h54 : T78Native.N681.h54X.toFilt.valid lDB681.length = true ∧ FiltSound (mkE 12 lDB681) T78Native.N681.h54X.toFilt :=
  ⟨by decide, filtSound_mono (by decide) (fun s hs => mem_of_inS _ _ (List.all_eq_true.1 T78Native.N681.cover_h54 s hs))
    (filtSound_aut681 _ (by decide) T78Native.N681.sound_h12.2)⟩
