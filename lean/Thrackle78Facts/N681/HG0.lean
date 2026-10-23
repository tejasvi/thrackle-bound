import Thrackle78Facts.N681.HS0
import Thrackle78Facts.N681.HS1
import Thrackle78Facts.N681.HS2
import Thrackle78Facts.N681.HS3
import Thrackle78Facts.N681.HS4
import Thrackle78Facts.N681.HS5
import Thrackle78Facts.N681.HS6
import Thrackle78Facts.N681.HS7
import Thrackle78Facts.N681.HS8
import Thrackle78Facts.N681.HS9
import Thrackle78Facts.N681.HS10
import Thrackle78Facts.N681.HS11
import Thrackle78Facts.N681.HS12
import Thrackle78Facts.N681.HS13
import Thrackle78Facts.N681.HS14
import Thrackle78Facts.N681.HS15
import Thrackle78Facts.N681.HS16
import Thrackle78Facts.N681.HS17
import Thrackle78Facts.N681.HS18
import Thrackle78Facts.N681.HS19
import Thrackle78Facts.N681.HS20
import Thrackle78Facts.N681.HS21
import Thrackle78Facts.N681.HS22
import Thrackle78Facts.N681.HS23
import Thrackle78Facts.N681.HS24
import Thrackle78Facts.N681.HS25
import Thrackle78Facts.N681.HS26
import Thrackle78Facts.N681.HS27
import Thrackle78Facts.N681.HS28
import Thrackle78Facts.N681.HS29

open Thrackle78 Thrackle78Core

theorem T78Native.N681.hgroup_ok_0 : ∀ j < 30, checkFilterXShards 12 lDB681.toArray T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF (T78Native.N681.hbatch (30 * 0 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.hshard_ok_0,
      T78Native.N681.hshard_ok_1,
      T78Native.N681.hshard_ok_2,
      T78Native.N681.hshard_ok_3,
      T78Native.N681.hshard_ok_4,
      T78Native.N681.hshard_ok_5,
      T78Native.N681.hshard_ok_6,
      T78Native.N681.hshard_ok_7,
      T78Native.N681.hshard_ok_8,
      T78Native.N681.hshard_ok_9,
      T78Native.N681.hshard_ok_10,
      T78Native.N681.hshard_ok_11,
      T78Native.N681.hshard_ok_12,
      T78Native.N681.hshard_ok_13,
      T78Native.N681.hshard_ok_14,
      T78Native.N681.hshard_ok_15,
      T78Native.N681.hshard_ok_16,
      T78Native.N681.hshard_ok_17,
      T78Native.N681.hshard_ok_18,
      T78Native.N681.hshard_ok_19,
      T78Native.N681.hshard_ok_20,
      T78Native.N681.hshard_ok_21,
      T78Native.N681.hshard_ok_22,
      T78Native.N681.hshard_ok_23,
      T78Native.N681.hshard_ok_24,
      T78Native.N681.hshard_ok_25,
      T78Native.N681.hshard_ok_26,
      T78Native.N681.hshard_ok_27,
      T78Native.N681.hshard_ok_28,
      T78Native.N681.hshard_ok_29]
