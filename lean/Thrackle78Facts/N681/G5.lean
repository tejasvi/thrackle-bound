import Thrackle78Facts.N681.B200
import Thrackle78Facts.N681.B201
import Thrackle78Facts.N681.B202
import Thrackle78Facts.N681.B203
import Thrackle78Facts.N681.B204
import Thrackle78Facts.N681.B205
import Thrackle78Facts.N681.B206
import Thrackle78Facts.N681.B207
import Thrackle78Facts.N681.B208
import Thrackle78Facts.N681.B209
import Thrackle78Facts.N681.B210
import Thrackle78Facts.N681.B211
import Thrackle78Facts.N681.B212
import Thrackle78Facts.N681.B213
import Thrackle78Facts.N681.B214
import Thrackle78Facts.N681.B215
import Thrackle78Facts.N681.B216
import Thrackle78Facts.N681.B217
import Thrackle78Facts.N681.B218
import Thrackle78Facts.N681.B219
import Thrackle78Facts.N681.B220
import Thrackle78Facts.N681.B221
import Thrackle78Facts.N681.B222
import Thrackle78Facts.N681.B223
import Thrackle78Facts.N681.B224
import Thrackle78Facts.N681.B225
import Thrackle78Facts.N681.B226
import Thrackle78Facts.N681.B227
import Thrackle78Facts.N681.B228
import Thrackle78Facts.N681.B229
import Thrackle78Facts.N681.B230
import Thrackle78Facts.N681.B231
import Thrackle78Facts.N681.B232
import Thrackle78Facts.N681.B233
import Thrackle78Facts.N681.B234
import Thrackle78Facts.N681.B235
import Thrackle78Facts.N681.B236
import Thrackle78Facts.N681.B237
import Thrackle78Facts.N681.B238
import Thrackle78Facts.N681.B239

open Thrackle78 Thrackle78Core

theorem T78Native.N681.group_ok_5 : ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * 5 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.batch_ok_200,
      T78Native.N681.batch_ok_201,
      T78Native.N681.batch_ok_202,
      T78Native.N681.batch_ok_203,
      T78Native.N681.batch_ok_204,
      T78Native.N681.batch_ok_205,
      T78Native.N681.batch_ok_206,
      T78Native.N681.batch_ok_207,
      T78Native.N681.batch_ok_208,
      T78Native.N681.batch_ok_209,
      T78Native.N681.batch_ok_210,
      T78Native.N681.batch_ok_211,
      T78Native.N681.batch_ok_212,
      T78Native.N681.batch_ok_213,
      T78Native.N681.batch_ok_214,
      T78Native.N681.batch_ok_215,
      T78Native.N681.batch_ok_216,
      T78Native.N681.batch_ok_217,
      T78Native.N681.batch_ok_218,
      T78Native.N681.batch_ok_219,
      T78Native.N681.batch_ok_220,
      T78Native.N681.batch_ok_221,
      T78Native.N681.batch_ok_222,
      T78Native.N681.batch_ok_223,
      T78Native.N681.batch_ok_224,
      T78Native.N681.batch_ok_225,
      T78Native.N681.batch_ok_226,
      T78Native.N681.batch_ok_227,
      T78Native.N681.batch_ok_228,
      T78Native.N681.batch_ok_229,
      T78Native.N681.batch_ok_230,
      T78Native.N681.batch_ok_231,
      T78Native.N681.batch_ok_232,
      T78Native.N681.batch_ok_233,
      T78Native.N681.batch_ok_234,
      T78Native.N681.batch_ok_235,
      T78Native.N681.batch_ok_236,
      T78Native.N681.batch_ok_237,
      T78Native.N681.batch_ok_238,
      T78Native.N681.batch_ok_239]
