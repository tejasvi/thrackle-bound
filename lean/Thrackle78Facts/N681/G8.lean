import Thrackle78Facts.N681.B320
import Thrackle78Facts.N681.B321
import Thrackle78Facts.N681.B322
import Thrackle78Facts.N681.B323
import Thrackle78Facts.N681.B324
import Thrackle78Facts.N681.B325
import Thrackle78Facts.N681.B326
import Thrackle78Facts.N681.B327
import Thrackle78Facts.N681.B328
import Thrackle78Facts.N681.B329
import Thrackle78Facts.N681.B330
import Thrackle78Facts.N681.B331
import Thrackle78Facts.N681.B332
import Thrackle78Facts.N681.B333
import Thrackle78Facts.N681.B334
import Thrackle78Facts.N681.B335
import Thrackle78Facts.N681.B336
import Thrackle78Facts.N681.B337
import Thrackle78Facts.N681.B338
import Thrackle78Facts.N681.B339
import Thrackle78Facts.N681.B340
import Thrackle78Facts.N681.B341
import Thrackle78Facts.N681.B342
import Thrackle78Facts.N681.B343
import Thrackle78Facts.N681.B344
import Thrackle78Facts.N681.B345
import Thrackle78Facts.N681.B346
import Thrackle78Facts.N681.B347
import Thrackle78Facts.N681.B348
import Thrackle78Facts.N681.B349
import Thrackle78Facts.N681.B350
import Thrackle78Facts.N681.B351
import Thrackle78Facts.N681.B352
import Thrackle78Facts.N681.B353
import Thrackle78Facts.N681.B354
import Thrackle78Facts.N681.B355
import Thrackle78Facts.N681.B356
import Thrackle78Facts.N681.B357
import Thrackle78Facts.N681.B358
import Thrackle78Facts.N681.B359

open Thrackle78 Thrackle78Core

theorem T78Native.N681.group_ok_8 : ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * 8 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.batch_ok_320,
      T78Native.N681.batch_ok_321,
      T78Native.N681.batch_ok_322,
      T78Native.N681.batch_ok_323,
      T78Native.N681.batch_ok_324,
      T78Native.N681.batch_ok_325,
      T78Native.N681.batch_ok_326,
      T78Native.N681.batch_ok_327,
      T78Native.N681.batch_ok_328,
      T78Native.N681.batch_ok_329,
      T78Native.N681.batch_ok_330,
      T78Native.N681.batch_ok_331,
      T78Native.N681.batch_ok_332,
      T78Native.N681.batch_ok_333,
      T78Native.N681.batch_ok_334,
      T78Native.N681.batch_ok_335,
      T78Native.N681.batch_ok_336,
      T78Native.N681.batch_ok_337,
      T78Native.N681.batch_ok_338,
      T78Native.N681.batch_ok_339,
      T78Native.N681.batch_ok_340,
      T78Native.N681.batch_ok_341,
      T78Native.N681.batch_ok_342,
      T78Native.N681.batch_ok_343,
      T78Native.N681.batch_ok_344,
      T78Native.N681.batch_ok_345,
      T78Native.N681.batch_ok_346,
      T78Native.N681.batch_ok_347,
      T78Native.N681.batch_ok_348,
      T78Native.N681.batch_ok_349,
      T78Native.N681.batch_ok_350,
      T78Native.N681.batch_ok_351,
      T78Native.N681.batch_ok_352,
      T78Native.N681.batch_ok_353,
      T78Native.N681.batch_ok_354,
      T78Native.N681.batch_ok_355,
      T78Native.N681.batch_ok_356,
      T78Native.N681.batch_ok_357,
      T78Native.N681.batch_ok_358,
      T78Native.N681.batch_ok_359]
