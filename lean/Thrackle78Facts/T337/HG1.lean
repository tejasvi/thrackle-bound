import Thrackle78Facts.T337.HS30
import Thrackle78Facts.T337.HS31
import Thrackle78Facts.T337.HS32
import Thrackle78Facts.T337.HS33
import Thrackle78Facts.T337.HS34
import Thrackle78Facts.T337.HS35
import Thrackle78Facts.T337.HS36
import Thrackle78Facts.T337.HS37
import Thrackle78Facts.T337.HS38
import Thrackle78Facts.T337.HS39
import Thrackle78Facts.T337.HS40
import Thrackle78Facts.T337.HS41
import Thrackle78Facts.T337.HS42
import Thrackle78Facts.T337.HS43
import Thrackle78Facts.T337.HS44
import Thrackle78Facts.T337.HS45
import Thrackle78Facts.T337.HS46
import Thrackle78Facts.T337.HS47
import Thrackle78Facts.T337.HS48
import Thrackle78Facts.T337.HS49
import Thrackle78Facts.T337.HS50
import Thrackle78Facts.T337.HS51
import Thrackle78Facts.T337.HS52
import Thrackle78Facts.T337.HS53
import Thrackle78Facts.T337.HS54
import Thrackle78Facts.T337.HS55
import Thrackle78Facts.T337.HS56
import Thrackle78Facts.T337.HS57
import Thrackle78Facts.T337.HS58
import Thrackle78Facts.T337.HS59

open Thrackle78 Thrackle78Core

theorem T78Native.T337.hgroup_ok_1 : ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * 1 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.T337.hshard_ok_30,
      T78Native.T337.hshard_ok_31,
      T78Native.T337.hshard_ok_32,
      T78Native.T337.hshard_ok_33,
      T78Native.T337.hshard_ok_34,
      T78Native.T337.hshard_ok_35,
      T78Native.T337.hshard_ok_36,
      T78Native.T337.hshard_ok_37,
      T78Native.T337.hshard_ok_38,
      T78Native.T337.hshard_ok_39,
      T78Native.T337.hshard_ok_40,
      T78Native.T337.hshard_ok_41,
      T78Native.T337.hshard_ok_42,
      T78Native.T337.hshard_ok_43,
      T78Native.T337.hshard_ok_44,
      T78Native.T337.hshard_ok_45,
      T78Native.T337.hshard_ok_46,
      T78Native.T337.hshard_ok_47,
      T78Native.T337.hshard_ok_48,
      T78Native.T337.hshard_ok_49,
      T78Native.T337.hshard_ok_50,
      T78Native.T337.hshard_ok_51,
      T78Native.T337.hshard_ok_52,
      T78Native.T337.hshard_ok_53,
      T78Native.T337.hshard_ok_54,
      T78Native.T337.hshard_ok_55,
      T78Native.T337.hshard_ok_56,
      T78Native.T337.hshard_ok_57,
      T78Native.T337.hshard_ok_58,
      T78Native.T337.hshard_ok_59]
