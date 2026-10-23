import Thrackle78Facts.T337.Coverc10b
import Thrackle78Facts.T337.Soundc10a

open Thrackle78 Thrackle78Core Thrackle78.Checker

/-- The logical filter of `c10b` is sound: it contains the image of the sound filter `c10a` under the automorphism. -/
theorem T78Native.T337.sound_c10b : T78Native.T337.c10bX.toFilt.valid lTH337.length = true ∧ FiltSound (mkE 12 lTH337) T78Native.T337.c10bX.toFilt :=
  ⟨by decide, filtSound_mono (by decide) (fun s hs => mem_of_inS _ _ (List.all_eq_true.1 T78Native.T337.cover_c10b s hs))
    (filtSound_aut337a _ (by decide) T78Native.T337.sound_c10a.2)⟩
