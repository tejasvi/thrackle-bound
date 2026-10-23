import Thrackle78Facts.N681.B120
import Thrackle78Facts.N681.B121
import Thrackle78Facts.N681.B122
import Thrackle78Facts.N681.B123
import Thrackle78Facts.N681.B124
import Thrackle78Facts.N681.B125
import Thrackle78Facts.N681.B126
import Thrackle78Facts.N681.B127
import Thrackle78Facts.N681.B128
import Thrackle78Facts.N681.B129
import Thrackle78Facts.N681.B130
import Thrackle78Facts.N681.B131
import Thrackle78Facts.N681.B132
import Thrackle78Facts.N681.B133
import Thrackle78Facts.N681.B134
import Thrackle78Facts.N681.B135
import Thrackle78Facts.N681.B136
import Thrackle78Facts.N681.B137
import Thrackle78Facts.N681.B138
import Thrackle78Facts.N681.B139
import Thrackle78Facts.N681.B140
import Thrackle78Facts.N681.B141
import Thrackle78Facts.N681.B142
import Thrackle78Facts.N681.B143
import Thrackle78Facts.N681.B144
import Thrackle78Facts.N681.B145
import Thrackle78Facts.N681.B146
import Thrackle78Facts.N681.B147
import Thrackle78Facts.N681.B148
import Thrackle78Facts.N681.B149
import Thrackle78Facts.N681.B150
import Thrackle78Facts.N681.B151
import Thrackle78Facts.N681.B152
import Thrackle78Facts.N681.B153
import Thrackle78Facts.N681.B154
import Thrackle78Facts.N681.B155
import Thrackle78Facts.N681.B156
import Thrackle78Facts.N681.B157
import Thrackle78Facts.N681.B158
import Thrackle78Facts.N681.B159

open Thrackle78 Thrackle78Core

theorem T78Native.N681.group_ok_3 : ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * 3 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.batch_ok_120,
      T78Native.N681.batch_ok_121,
      T78Native.N681.batch_ok_122,
      T78Native.N681.batch_ok_123,
      T78Native.N681.batch_ok_124,
      T78Native.N681.batch_ok_125,
      T78Native.N681.batch_ok_126,
      T78Native.N681.batch_ok_127,
      T78Native.N681.batch_ok_128,
      T78Native.N681.batch_ok_129,
      T78Native.N681.batch_ok_130,
      T78Native.N681.batch_ok_131,
      T78Native.N681.batch_ok_132,
      T78Native.N681.batch_ok_133,
      T78Native.N681.batch_ok_134,
      T78Native.N681.batch_ok_135,
      T78Native.N681.batch_ok_136,
      T78Native.N681.batch_ok_137,
      T78Native.N681.batch_ok_138,
      T78Native.N681.batch_ok_139,
      T78Native.N681.batch_ok_140,
      T78Native.N681.batch_ok_141,
      T78Native.N681.batch_ok_142,
      T78Native.N681.batch_ok_143,
      T78Native.N681.batch_ok_144,
      T78Native.N681.batch_ok_145,
      T78Native.N681.batch_ok_146,
      T78Native.N681.batch_ok_147,
      T78Native.N681.batch_ok_148,
      T78Native.N681.batch_ok_149,
      T78Native.N681.batch_ok_150,
      T78Native.N681.batch_ok_151,
      T78Native.N681.batch_ok_152,
      T78Native.N681.batch_ok_153,
      T78Native.N681.batch_ok_154,
      T78Native.N681.batch_ok_155,
      T78Native.N681.batch_ok_156,
      T78Native.N681.batch_ok_157,
      T78Native.N681.batch_ok_158,
      T78Native.N681.batch_ok_159]
