import Thrackle78Facts.N681.B240
import Thrackle78Facts.N681.B241
import Thrackle78Facts.N681.B242
import Thrackle78Facts.N681.B243
import Thrackle78Facts.N681.B244
import Thrackle78Facts.N681.B245
import Thrackle78Facts.N681.B246
import Thrackle78Facts.N681.B247
import Thrackle78Facts.N681.B248
import Thrackle78Facts.N681.B249
import Thrackle78Facts.N681.B250
import Thrackle78Facts.N681.B251
import Thrackle78Facts.N681.B252
import Thrackle78Facts.N681.B253
import Thrackle78Facts.N681.B254
import Thrackle78Facts.N681.B255
import Thrackle78Facts.N681.B256
import Thrackle78Facts.N681.B257
import Thrackle78Facts.N681.B258
import Thrackle78Facts.N681.B259
import Thrackle78Facts.N681.B260
import Thrackle78Facts.N681.B261
import Thrackle78Facts.N681.B262
import Thrackle78Facts.N681.B263
import Thrackle78Facts.N681.B264
import Thrackle78Facts.N681.B265
import Thrackle78Facts.N681.B266
import Thrackle78Facts.N681.B267
import Thrackle78Facts.N681.B268
import Thrackle78Facts.N681.B269
import Thrackle78Facts.N681.B270
import Thrackle78Facts.N681.B271
import Thrackle78Facts.N681.B272
import Thrackle78Facts.N681.B273
import Thrackle78Facts.N681.B274
import Thrackle78Facts.N681.B275
import Thrackle78Facts.N681.B276
import Thrackle78Facts.N681.B277
import Thrackle78Facts.N681.B278
import Thrackle78Facts.N681.B279

open Thrackle78 Thrackle78Core

theorem T78Native.N681.group_ok_6 : ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * 6 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.batch_ok_240,
      T78Native.N681.batch_ok_241,
      T78Native.N681.batch_ok_242,
      T78Native.N681.batch_ok_243,
      T78Native.N681.batch_ok_244,
      T78Native.N681.batch_ok_245,
      T78Native.N681.batch_ok_246,
      T78Native.N681.batch_ok_247,
      T78Native.N681.batch_ok_248,
      T78Native.N681.batch_ok_249,
      T78Native.N681.batch_ok_250,
      T78Native.N681.batch_ok_251,
      T78Native.N681.batch_ok_252,
      T78Native.N681.batch_ok_253,
      T78Native.N681.batch_ok_254,
      T78Native.N681.batch_ok_255,
      T78Native.N681.batch_ok_256,
      T78Native.N681.batch_ok_257,
      T78Native.N681.batch_ok_258,
      T78Native.N681.batch_ok_259,
      T78Native.N681.batch_ok_260,
      T78Native.N681.batch_ok_261,
      T78Native.N681.batch_ok_262,
      T78Native.N681.batch_ok_263,
      T78Native.N681.batch_ok_264,
      T78Native.N681.batch_ok_265,
      T78Native.N681.batch_ok_266,
      T78Native.N681.batch_ok_267,
      T78Native.N681.batch_ok_268,
      T78Native.N681.batch_ok_269,
      T78Native.N681.batch_ok_270,
      T78Native.N681.batch_ok_271,
      T78Native.N681.batch_ok_272,
      T78Native.N681.batch_ok_273,
      T78Native.N681.batch_ok_274,
      T78Native.N681.batch_ok_275,
      T78Native.N681.batch_ok_276,
      T78Native.N681.batch_ok_277,
      T78Native.N681.batch_ok_278,
      T78Native.N681.batch_ok_279]
