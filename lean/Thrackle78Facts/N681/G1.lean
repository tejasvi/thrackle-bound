import Thrackle78Facts.N681.B40
import Thrackle78Facts.N681.B41
import Thrackle78Facts.N681.B42
import Thrackle78Facts.N681.B43
import Thrackle78Facts.N681.B44
import Thrackle78Facts.N681.B45
import Thrackle78Facts.N681.B46
import Thrackle78Facts.N681.B47
import Thrackle78Facts.N681.B48
import Thrackle78Facts.N681.B49
import Thrackle78Facts.N681.B50
import Thrackle78Facts.N681.B51
import Thrackle78Facts.N681.B52
import Thrackle78Facts.N681.B53
import Thrackle78Facts.N681.B54
import Thrackle78Facts.N681.B55
import Thrackle78Facts.N681.B56
import Thrackle78Facts.N681.B57
import Thrackle78Facts.N681.B58
import Thrackle78Facts.N681.B59
import Thrackle78Facts.N681.B60
import Thrackle78Facts.N681.B61
import Thrackle78Facts.N681.B62
import Thrackle78Facts.N681.B63
import Thrackle78Facts.N681.B64
import Thrackle78Facts.N681.B65
import Thrackle78Facts.N681.B66
import Thrackle78Facts.N681.B67
import Thrackle78Facts.N681.B68
import Thrackle78Facts.N681.B69
import Thrackle78Facts.N681.B70
import Thrackle78Facts.N681.B71
import Thrackle78Facts.N681.B72
import Thrackle78Facts.N681.B73
import Thrackle78Facts.N681.B74
import Thrackle78Facts.N681.B75
import Thrackle78Facts.N681.B76
import Thrackle78Facts.N681.B77
import Thrackle78Facts.N681.B78
import Thrackle78Facts.N681.B79

open Thrackle78 Thrackle78Core

theorem T78Native.N681.group_ok_1 : ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * 1 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.batch_ok_40,
      T78Native.N681.batch_ok_41,
      T78Native.N681.batch_ok_42,
      T78Native.N681.batch_ok_43,
      T78Native.N681.batch_ok_44,
      T78Native.N681.batch_ok_45,
      T78Native.N681.batch_ok_46,
      T78Native.N681.batch_ok_47,
      T78Native.N681.batch_ok_48,
      T78Native.N681.batch_ok_49,
      T78Native.N681.batch_ok_50,
      T78Native.N681.batch_ok_51,
      T78Native.N681.batch_ok_52,
      T78Native.N681.batch_ok_53,
      T78Native.N681.batch_ok_54,
      T78Native.N681.batch_ok_55,
      T78Native.N681.batch_ok_56,
      T78Native.N681.batch_ok_57,
      T78Native.N681.batch_ok_58,
      T78Native.N681.batch_ok_59,
      T78Native.N681.batch_ok_60,
      T78Native.N681.batch_ok_61,
      T78Native.N681.batch_ok_62,
      T78Native.N681.batch_ok_63,
      T78Native.N681.batch_ok_64,
      T78Native.N681.batch_ok_65,
      T78Native.N681.batch_ok_66,
      T78Native.N681.batch_ok_67,
      T78Native.N681.batch_ok_68,
      T78Native.N681.batch_ok_69,
      T78Native.N681.batch_ok_70,
      T78Native.N681.batch_ok_71,
      T78Native.N681.batch_ok_72,
      T78Native.N681.batch_ok_73,
      T78Native.N681.batch_ok_74,
      T78Native.N681.batch_ok_75,
      T78Native.N681.batch_ok_76,
      T78Native.N681.batch_ok_77,
      T78Native.N681.batch_ok_78,
      T78Native.N681.batch_ok_79]
