import Thrackle78Facts.N681.B160
import Thrackle78Facts.N681.B161
import Thrackle78Facts.N681.B162
import Thrackle78Facts.N681.B163
import Thrackle78Facts.N681.B164
import Thrackle78Facts.N681.B165
import Thrackle78Facts.N681.B166
import Thrackle78Facts.N681.B167
import Thrackle78Facts.N681.B168
import Thrackle78Facts.N681.B169
import Thrackle78Facts.N681.B170
import Thrackle78Facts.N681.B171
import Thrackle78Facts.N681.B172
import Thrackle78Facts.N681.B173
import Thrackle78Facts.N681.B174
import Thrackle78Facts.N681.B175
import Thrackle78Facts.N681.B176
import Thrackle78Facts.N681.B177
import Thrackle78Facts.N681.B178
import Thrackle78Facts.N681.B179
import Thrackle78Facts.N681.B180
import Thrackle78Facts.N681.B181
import Thrackle78Facts.N681.B182
import Thrackle78Facts.N681.B183
import Thrackle78Facts.N681.B184
import Thrackle78Facts.N681.B185
import Thrackle78Facts.N681.B186
import Thrackle78Facts.N681.B187
import Thrackle78Facts.N681.B188
import Thrackle78Facts.N681.B189
import Thrackle78Facts.N681.B190
import Thrackle78Facts.N681.B191
import Thrackle78Facts.N681.B192
import Thrackle78Facts.N681.B193
import Thrackle78Facts.N681.B194
import Thrackle78Facts.N681.B195
import Thrackle78Facts.N681.B196
import Thrackle78Facts.N681.B197
import Thrackle78Facts.N681.B198
import Thrackle78Facts.N681.B199

open Thrackle78 Thrackle78Core

theorem T78Native.N681.group_ok_4 : ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * 4 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.batch_ok_160,
      T78Native.N681.batch_ok_161,
      T78Native.N681.batch_ok_162,
      T78Native.N681.batch_ok_163,
      T78Native.N681.batch_ok_164,
      T78Native.N681.batch_ok_165,
      T78Native.N681.batch_ok_166,
      T78Native.N681.batch_ok_167,
      T78Native.N681.batch_ok_168,
      T78Native.N681.batch_ok_169,
      T78Native.N681.batch_ok_170,
      T78Native.N681.batch_ok_171,
      T78Native.N681.batch_ok_172,
      T78Native.N681.batch_ok_173,
      T78Native.N681.batch_ok_174,
      T78Native.N681.batch_ok_175,
      T78Native.N681.batch_ok_176,
      T78Native.N681.batch_ok_177,
      T78Native.N681.batch_ok_178,
      T78Native.N681.batch_ok_179,
      T78Native.N681.batch_ok_180,
      T78Native.N681.batch_ok_181,
      T78Native.N681.batch_ok_182,
      T78Native.N681.batch_ok_183,
      T78Native.N681.batch_ok_184,
      T78Native.N681.batch_ok_185,
      T78Native.N681.batch_ok_186,
      T78Native.N681.batch_ok_187,
      T78Native.N681.batch_ok_188,
      T78Native.N681.batch_ok_189,
      T78Native.N681.batch_ok_190,
      T78Native.N681.batch_ok_191,
      T78Native.N681.batch_ok_192,
      T78Native.N681.batch_ok_193,
      T78Native.N681.batch_ok_194,
      T78Native.N681.batch_ok_195,
      T78Native.N681.batch_ok_196,
      T78Native.N681.batch_ok_197,
      T78Native.N681.batch_ok_198,
      T78Native.N681.batch_ok_199]
