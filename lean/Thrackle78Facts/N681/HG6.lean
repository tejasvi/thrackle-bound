import Thrackle78Facts.N681.HS180
import Thrackle78Facts.N681.HS181
import Thrackle78Facts.N681.HS182
import Thrackle78Facts.N681.HS183
import Thrackle78Facts.N681.HS184
import Thrackle78Facts.N681.HS185
import Thrackle78Facts.N681.HS186
import Thrackle78Facts.N681.HS187
import Thrackle78Facts.N681.HS188
import Thrackle78Facts.N681.HS189
import Thrackle78Facts.N681.HS190
import Thrackle78Facts.N681.HS191
import Thrackle78Facts.N681.HS192
import Thrackle78Facts.N681.HS193
import Thrackle78Facts.N681.HS194
import Thrackle78Facts.N681.HS195
import Thrackle78Facts.N681.HS196
import Thrackle78Facts.N681.HS197
import Thrackle78Facts.N681.HS198
import Thrackle78Facts.N681.HS199
import Thrackle78Facts.N681.HS200
import Thrackle78Facts.N681.HS201
import Thrackle78Facts.N681.HS202
import Thrackle78Facts.N681.HS203
import Thrackle78Facts.N681.HS204
import Thrackle78Facts.N681.HS205
import Thrackle78Facts.N681.HS206
import Thrackle78Facts.N681.HS207
import Thrackle78Facts.N681.HS208
import Thrackle78Facts.N681.HS209

open Thrackle78 Thrackle78Core

theorem T78Native.N681.hgroup_ok_6 : ∀ j < 30, checkFilterXShards 12 lDB681.toArray T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF (T78Native.N681.hbatch (30 * 6 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.hshard_ok_180,
      T78Native.N681.hshard_ok_181,
      T78Native.N681.hshard_ok_182,
      T78Native.N681.hshard_ok_183,
      T78Native.N681.hshard_ok_184,
      T78Native.N681.hshard_ok_185,
      T78Native.N681.hshard_ok_186,
      T78Native.N681.hshard_ok_187,
      T78Native.N681.hshard_ok_188,
      T78Native.N681.hshard_ok_189,
      T78Native.N681.hshard_ok_190,
      T78Native.N681.hshard_ok_191,
      T78Native.N681.hshard_ok_192,
      T78Native.N681.hshard_ok_193,
      T78Native.N681.hshard_ok_194,
      T78Native.N681.hshard_ok_195,
      T78Native.N681.hshard_ok_196,
      T78Native.N681.hshard_ok_197,
      T78Native.N681.hshard_ok_198,
      T78Native.N681.hshard_ok_199,
      T78Native.N681.hshard_ok_200,
      T78Native.N681.hshard_ok_201,
      T78Native.N681.hshard_ok_202,
      T78Native.N681.hshard_ok_203,
      T78Native.N681.hshard_ok_204,
      T78Native.N681.hshard_ok_205,
      T78Native.N681.hshard_ok_206,
      T78Native.N681.hshard_ok_207,
      T78Native.N681.hshard_ok_208,
      T78Native.N681.hshard_ok_209]
