import Thrackle78Facts.N681.HS270
import Thrackle78Facts.N681.HS271
import Thrackle78Facts.N681.HS272
import Thrackle78Facts.N681.HS273
import Thrackle78Facts.N681.HS274
import Thrackle78Facts.N681.HS275
import Thrackle78Facts.N681.HS276
import Thrackle78Facts.N681.HS277
import Thrackle78Facts.N681.HS278
import Thrackle78Facts.N681.HS279
import Thrackle78Facts.N681.HS280
import Thrackle78Facts.N681.HS281
import Thrackle78Facts.N681.HS282
import Thrackle78Facts.N681.HS283
import Thrackle78Facts.N681.HS284
import Thrackle78Facts.N681.HS285
import Thrackle78Facts.N681.HS286
import Thrackle78Facts.N681.HS287
import Thrackle78Facts.N681.HS288
import Thrackle78Facts.N681.HS289
import Thrackle78Facts.N681.HS290
import Thrackle78Facts.N681.HS291
import Thrackle78Facts.N681.HS292
import Thrackle78Facts.N681.HS293
import Thrackle78Facts.N681.HS294
import Thrackle78Facts.N681.HS295
import Thrackle78Facts.N681.HS296
import Thrackle78Facts.N681.HS297
import Thrackle78Facts.N681.HS298
import Thrackle78Facts.N681.HS299

open Thrackle78 Thrackle78Core

theorem T78Native.N681.hgroup_ok_9 : ∀ j < 30, checkFilterXShards 12 lDB681.toArray T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF (T78Native.N681.hbatch (30 * 9 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.hshard_ok_270,
      T78Native.N681.hshard_ok_271,
      T78Native.N681.hshard_ok_272,
      T78Native.N681.hshard_ok_273,
      T78Native.N681.hshard_ok_274,
      T78Native.N681.hshard_ok_275,
      T78Native.N681.hshard_ok_276,
      T78Native.N681.hshard_ok_277,
      T78Native.N681.hshard_ok_278,
      T78Native.N681.hshard_ok_279,
      T78Native.N681.hshard_ok_280,
      T78Native.N681.hshard_ok_281,
      T78Native.N681.hshard_ok_282,
      T78Native.N681.hshard_ok_283,
      T78Native.N681.hshard_ok_284,
      T78Native.N681.hshard_ok_285,
      T78Native.N681.hshard_ok_286,
      T78Native.N681.hshard_ok_287,
      T78Native.N681.hshard_ok_288,
      T78Native.N681.hshard_ok_289,
      T78Native.N681.hshard_ok_290,
      T78Native.N681.hshard_ok_291,
      T78Native.N681.hshard_ok_292,
      T78Native.N681.hshard_ok_293,
      T78Native.N681.hshard_ok_294,
      T78Native.N681.hshard_ok_295,
      T78Native.N681.hshard_ok_296,
      T78Native.N681.hshard_ok_297,
      T78Native.N681.hshard_ok_298,
      T78Native.N681.hshard_ok_299]
