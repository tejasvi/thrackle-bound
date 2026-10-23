/-!
# Joining certificate chunks (core Lean only)

`catBytes` concatenates the bytes of a list of strings into one preallocated byte array (linear time and memory).
Used only to present certificate data to the readers; the soundness of the checks does not depend on it.
-/

namespace Thrackle78Core

/-- The bytes of the strings of `l`, concatenated. -/
def catBytes (l : List String) : ByteArray :=
  l.foldl (fun acc s => acc.append s.toUTF8) (ByteArray.emptyWithCapacity (l.foldl (fun n s => n + s.utf8ByteSize) 0))

end Thrackle78Core
