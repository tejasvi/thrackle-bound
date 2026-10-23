import Thrackle78Facts.N681.HS210
import Thrackle78Facts.N681.HS211
import Thrackle78Facts.N681.HS212
import Thrackle78Facts.N681.HS213
import Thrackle78Facts.N681.HS214
import Thrackle78Facts.N681.HS215
import Thrackle78Facts.N681.HS216
import Thrackle78Facts.N681.HS217
import Thrackle78Facts.N681.HS218
import Thrackle78Facts.N681.HS219
import Thrackle78Facts.N681.HS220
import Thrackle78Facts.N681.HS221
import Thrackle78Facts.N681.HS222
import Thrackle78Facts.N681.HS223
import Thrackle78Facts.N681.HS224
import Thrackle78Facts.N681.HS225
import Thrackle78Facts.N681.HS226
import Thrackle78Facts.N681.HS227
import Thrackle78Facts.N681.HS228
import Thrackle78Facts.N681.HS229
import Thrackle78Facts.N681.HS230
import Thrackle78Facts.N681.HS231
import Thrackle78Facts.N681.HS232
import Thrackle78Facts.N681.HS233
import Thrackle78Facts.N681.HS234
import Thrackle78Facts.N681.HS235
import Thrackle78Facts.N681.HS236
import Thrackle78Facts.N681.HS237
import Thrackle78Facts.N681.HS238
import Thrackle78Facts.N681.HS239

open Thrackle78 Thrackle78Core

theorem T78Native.N681.hgroup_ok_7 : ∀ j < 30, checkFilterXShards 12 lDB681.toArray T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF (T78Native.N681.hbatch (30 * 7 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.hshard_ok_210,
      T78Native.N681.hshard_ok_211,
      T78Native.N681.hshard_ok_212,
      T78Native.N681.hshard_ok_213,
      T78Native.N681.hshard_ok_214,
      T78Native.N681.hshard_ok_215,
      T78Native.N681.hshard_ok_216,
      T78Native.N681.hshard_ok_217,
      T78Native.N681.hshard_ok_218,
      T78Native.N681.hshard_ok_219,
      T78Native.N681.hshard_ok_220,
      T78Native.N681.hshard_ok_221,
      T78Native.N681.hshard_ok_222,
      T78Native.N681.hshard_ok_223,
      T78Native.N681.hshard_ok_224,
      T78Native.N681.hshard_ok_225,
      T78Native.N681.hshard_ok_226,
      T78Native.N681.hshard_ok_227,
      T78Native.N681.hshard_ok_228,
      T78Native.N681.hshard_ok_229,
      T78Native.N681.hshard_ok_230,
      T78Native.N681.hshard_ok_231,
      T78Native.N681.hshard_ok_232,
      T78Native.N681.hshard_ok_233,
      T78Native.N681.hshard_ok_234,
      T78Native.N681.hshard_ok_235,
      T78Native.N681.hshard_ok_236,
      T78Native.N681.hshard_ok_237,
      T78Native.N681.hshard_ok_238,
      T78Native.N681.hshard_ok_239]
