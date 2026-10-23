import Thrackle78Facts.N681.HS120
import Thrackle78Facts.N681.HS121
import Thrackle78Facts.N681.HS122
import Thrackle78Facts.N681.HS123
import Thrackle78Facts.N681.HS124
import Thrackle78Facts.N681.HS125
import Thrackle78Facts.N681.HS126
import Thrackle78Facts.N681.HS127
import Thrackle78Facts.N681.HS128
import Thrackle78Facts.N681.HS129
import Thrackle78Facts.N681.HS130
import Thrackle78Facts.N681.HS131
import Thrackle78Facts.N681.HS132
import Thrackle78Facts.N681.HS133
import Thrackle78Facts.N681.HS134
import Thrackle78Facts.N681.HS135
import Thrackle78Facts.N681.HS136
import Thrackle78Facts.N681.HS137
import Thrackle78Facts.N681.HS138
import Thrackle78Facts.N681.HS139
import Thrackle78Facts.N681.HS140
import Thrackle78Facts.N681.HS141
import Thrackle78Facts.N681.HS142
import Thrackle78Facts.N681.HS143
import Thrackle78Facts.N681.HS144
import Thrackle78Facts.N681.HS145
import Thrackle78Facts.N681.HS146
import Thrackle78Facts.N681.HS147
import Thrackle78Facts.N681.HS148
import Thrackle78Facts.N681.HS149

open Thrackle78 Thrackle78Core

theorem T78Native.N681.hgroup_ok_4 : ∀ j < 30, checkFilterXShards 12 lDB681.toArray T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF (T78Native.N681.hbatch (30 * 4 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.hshard_ok_120,
      T78Native.N681.hshard_ok_121,
      T78Native.N681.hshard_ok_122,
      T78Native.N681.hshard_ok_123,
      T78Native.N681.hshard_ok_124,
      T78Native.N681.hshard_ok_125,
      T78Native.N681.hshard_ok_126,
      T78Native.N681.hshard_ok_127,
      T78Native.N681.hshard_ok_128,
      T78Native.N681.hshard_ok_129,
      T78Native.N681.hshard_ok_130,
      T78Native.N681.hshard_ok_131,
      T78Native.N681.hshard_ok_132,
      T78Native.N681.hshard_ok_133,
      T78Native.N681.hshard_ok_134,
      T78Native.N681.hshard_ok_135,
      T78Native.N681.hshard_ok_136,
      T78Native.N681.hshard_ok_137,
      T78Native.N681.hshard_ok_138,
      T78Native.N681.hshard_ok_139,
      T78Native.N681.hshard_ok_140,
      T78Native.N681.hshard_ok_141,
      T78Native.N681.hshard_ok_142,
      T78Native.N681.hshard_ok_143,
      T78Native.N681.hshard_ok_144,
      T78Native.N681.hshard_ok_145,
      T78Native.N681.hshard_ok_146,
      T78Native.N681.hshard_ok_147,
      T78Native.N681.hshard_ok_148,
      T78Native.N681.hshard_ok_149]
