import Thrackle78Facts.N681.B400
import Thrackle78Facts.N681.B401
import Thrackle78Facts.N681.B402
import Thrackle78Facts.N681.B403
import Thrackle78Facts.N681.B404
import Thrackle78Facts.N681.B405
import Thrackle78Facts.N681.B406
import Thrackle78Facts.N681.B407
import Thrackle78Facts.N681.B408
import Thrackle78Facts.N681.B409
import Thrackle78Facts.N681.B410
import Thrackle78Facts.N681.B411
import Thrackle78Facts.N681.B412
import Thrackle78Facts.N681.B413
import Thrackle78Facts.N681.B414
import Thrackle78Facts.N681.B415
import Thrackle78Facts.N681.B416
import Thrackle78Facts.N681.B417
import Thrackle78Facts.N681.B418
import Thrackle78Facts.N681.B419
import Thrackle78Facts.N681.B420
import Thrackle78Facts.N681.B421
import Thrackle78Facts.N681.B422
import Thrackle78Facts.N681.B423
import Thrackle78Facts.N681.B424
import Thrackle78Facts.N681.B425
import Thrackle78Facts.N681.B426
import Thrackle78Facts.N681.B427
import Thrackle78Facts.N681.B428
import Thrackle78Facts.N681.B429
import Thrackle78Facts.N681.B430
import Thrackle78Facts.N681.B431
import Thrackle78Facts.N681.B432
import Thrackle78Facts.N681.B433
import Thrackle78Facts.N681.B434
import Thrackle78Facts.N681.B435
import Thrackle78Facts.N681.B436
import Thrackle78Facts.N681.B437
import Thrackle78Facts.N681.B438
import Thrackle78Facts.N681.B439

open Thrackle78 Thrackle78Core

theorem T78Native.N681.group_ok_10 : ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * 10 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.batch_ok_400,
      T78Native.N681.batch_ok_401,
      T78Native.N681.batch_ok_402,
      T78Native.N681.batch_ok_403,
      T78Native.N681.batch_ok_404,
      T78Native.N681.batch_ok_405,
      T78Native.N681.batch_ok_406,
      T78Native.N681.batch_ok_407,
      T78Native.N681.batch_ok_408,
      T78Native.N681.batch_ok_409,
      T78Native.N681.batch_ok_410,
      T78Native.N681.batch_ok_411,
      T78Native.N681.batch_ok_412,
      T78Native.N681.batch_ok_413,
      T78Native.N681.batch_ok_414,
      T78Native.N681.batch_ok_415,
      T78Native.N681.batch_ok_416,
      T78Native.N681.batch_ok_417,
      T78Native.N681.batch_ok_418,
      T78Native.N681.batch_ok_419,
      T78Native.N681.batch_ok_420,
      T78Native.N681.batch_ok_421,
      T78Native.N681.batch_ok_422,
      T78Native.N681.batch_ok_423,
      T78Native.N681.batch_ok_424,
      T78Native.N681.batch_ok_425,
      T78Native.N681.batch_ok_426,
      T78Native.N681.batch_ok_427,
      T78Native.N681.batch_ok_428,
      T78Native.N681.batch_ok_429,
      T78Native.N681.batch_ok_430,
      T78Native.N681.batch_ok_431,
      T78Native.N681.batch_ok_432,
      T78Native.N681.batch_ok_433,
      T78Native.N681.batch_ok_434,
      T78Native.N681.batch_ok_435,
      T78Native.N681.batch_ok_436,
      T78Native.N681.batch_ok_437,
      T78Native.N681.batch_ok_438,
      T78Native.N681.batch_ok_439]
