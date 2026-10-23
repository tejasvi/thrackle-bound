import Thrackle78Facts.T337.HS60
import Thrackle78Facts.T337.HS61
import Thrackle78Facts.T337.HS62
import Thrackle78Facts.T337.HS63
import Thrackle78Facts.T337.HS64
import Thrackle78Facts.T337.HS65
import Thrackle78Facts.T337.HS66
import Thrackle78Facts.T337.HS67
import Thrackle78Facts.T337.HS68
import Thrackle78Facts.T337.HS69
import Thrackle78Facts.T337.HS70
import Thrackle78Facts.T337.HS71
import Thrackle78Facts.T337.HS72
import Thrackle78Facts.T337.HS73
import Thrackle78Facts.T337.HS74
import Thrackle78Facts.T337.HS75
import Thrackle78Facts.T337.HS76
import Thrackle78Facts.T337.HS77
import Thrackle78Facts.T337.HS78
import Thrackle78Facts.T337.HS79
import Thrackle78Facts.T337.HS80
import Thrackle78Facts.T337.HS81
import Thrackle78Facts.T337.HS82
import Thrackle78Facts.T337.HS83
import Thrackle78Facts.T337.HS84
import Thrackle78Facts.T337.HS85
import Thrackle78Facts.T337.HS86
import Thrackle78Facts.T337.HS87
import Thrackle78Facts.T337.HS88
import Thrackle78Facts.T337.HS89

open Thrackle78 Thrackle78Core

theorem T78Native.T337.hgroup_ok_2 : ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * 2 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.T337.hshard_ok_60,
      T78Native.T337.hshard_ok_61,
      T78Native.T337.hshard_ok_62,
      T78Native.T337.hshard_ok_63,
      T78Native.T337.hshard_ok_64,
      T78Native.T337.hshard_ok_65,
      T78Native.T337.hshard_ok_66,
      T78Native.T337.hshard_ok_67,
      T78Native.T337.hshard_ok_68,
      T78Native.T337.hshard_ok_69,
      T78Native.T337.hshard_ok_70,
      T78Native.T337.hshard_ok_71,
      T78Native.T337.hshard_ok_72,
      T78Native.T337.hshard_ok_73,
      T78Native.T337.hshard_ok_74,
      T78Native.T337.hshard_ok_75,
      T78Native.T337.hshard_ok_76,
      T78Native.T337.hshard_ok_77,
      T78Native.T337.hshard_ok_78,
      T78Native.T337.hshard_ok_79,
      T78Native.T337.hshard_ok_80,
      T78Native.T337.hshard_ok_81,
      T78Native.T337.hshard_ok_82,
      T78Native.T337.hshard_ok_83,
      T78Native.T337.hshard_ok_84,
      T78Native.T337.hshard_ok_85,
      T78Native.T337.hshard_ok_86,
      T78Native.T337.hshard_ok_87,
      T78Native.T337.hshard_ok_88,
      T78Native.T337.hshard_ok_89]
